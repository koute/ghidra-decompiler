use std::sync::Arc;
use std::sync::RwLock;
use std::sync::atomic::{AtomicI64, Ordering as AtomicOrdering};

use crate::architecture::{ATTRIB_ADJUSTVMA, Architecture, ArchitectureCapability, ErrorStream};
use crate::capability::CapabilityPoint;
use crate::error::{Error, Result};
use crate::istream::{Basefield, read_i64};
use crate::loadimage::SharedLoadImage;
use crate::loadimage_xml::LoadImageXml;
use crate::marshal::{ElementId, Encoder};
use crate::sleigh_arch::{LoaderSlot, SleighArchitecture, SleighArchitectureHooks, SleighCapability};
use crate::xml::{Document, DocumentStorage};

pub const ELEM_XML_SAVEFILE: ElementId = ElementId::new("xml_savefile", 236);

pub struct XmlArchitectureCapability;

pub static XML_ARCHITECTURE_CAPABILITY: XmlArchitectureCapability = XmlArchitectureCapability;

impl CapabilityPoint for XmlArchitectureCapability {
    fn initialize(&self) -> Result<()> {
        Ok(())
    }
}

impl ArchitectureCapability for XmlArchitectureCapability {
    fn get_name(&self) -> &str {
        "xml"
    }

    fn build_architecture(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<Box<Architecture>> {
        Ok(self.build_with_slot(filename, target, estream)?.0)
    }

    fn is_file_match(&self, filename: &str) -> bool {
        let Ok(bytes) = std::fs::read(filename) else {
            return false;
        };
        let mut pos = 0;
        while pos < bytes.len() && matches!(bytes[pos], b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r') {
            pos += 1;
        }
        bytes.len() >= pos + 3 && bytes[pos] == b'<' && bytes[pos + 1] == b'b' && bytes[pos + 2] == b'i'
    }

    fn is_xml_match(&self, doc: &Document) -> bool {
        doc.get_root().get_name() == "xml_savefile"
    }
}

impl SleighCapability for XmlArchitectureCapability {
    fn build_with_slot(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<(Box<Architecture>, LoaderSlot)> {
        let builder = XmlArchitecture::new(filename, target, estream);
        let slot = builder.sleigh.loader_slot();
        let mut glb = Box::new(Architecture::new());
        glb.builder = Some(Arc::new(builder));
        Ok((glb, slot))
    }
}

pub struct XmlArchitecture {
    pub sleigh: SleighArchitecture,
    adjustvma: AtomicI64,
    loader: RwLock<Option<Arc<LoadImageXml>>>,
}

impl XmlArchitecture {
    pub fn new(fname: &str, targ: &str, estream: Option<ErrorStream>) -> XmlArchitecture {
        XmlArchitecture {
            sleigh: SleighArchitecture::new(fname, targ, estream),
            adjustvma: AtomicI64::new(0),
            loader: RwLock::new(None),
        }
    }

    fn xml_loader(&self) -> Result<Arc<LoadImageXml>> {
        self.loader
            .read()
            .expect("poisoned lock")
            .clone()
            .ok_or_else(|| Error::Lowlevel("missing xml load image".to_string()))
    }
}

impl SleighArchitectureHooks for XmlArchitecture {
    fn sleigh(&self) -> &SleighArchitecture {
        &self.sleigh
    }

    fn build_loader(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh.collect_spec_files();
        let mut el = store.get_tag("binaryimage");
        if el.is_none() {
            let doc = store.open_document(&self.sleigh.get_filename())?;
            store.register_tag(doc.get_root());
            el = store.get_tag("binaryimage");
        }
        let Some(el) = el else {
            return Err(Error::Lowlevel("Could not find binaryimage tag".to_string()));
        };
        let loader = Arc::new(LoadImageXml::new(&self.sleigh.get_filename(), el)?);
        *self.loader.write().expect("poisoned lock") = Some(loader.clone());
        self.sleigh.set_adjustable_loader(loader.clone());
        let shared: SharedLoadImage = loader;
        glb.loader = Some(shared);
        Ok(())
    }

    fn post_spec_file(&self, glb: &mut Architecture) -> Result<()> {
        glb.post_spec_file_base()?;
        let loader = self.xml_loader()?;
        let translate = glb
            .translate
            .as_deref()
            .ok_or_else(|| Error::Lowlevel("missing translator".to_string()))?;
        loader.open(translate.manager())?;
        if self.adjustvma.load(AtomicOrdering::Relaxed) != 0 {
            loader.adjust_vma_shared(self.adjustvma.load(AtomicOrdering::Relaxed));
        }
        Ok(())
    }

    fn encode(&self, glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_XML_SAVEFILE);
        self.sleigh.encode_header(encoder);
        encoder.write_unsigned_integer(ATTRIB_ADJUSTVMA, self.adjustvma.load(AtomicOrdering::Relaxed) as u64);
        self.xml_loader()?.encode(encoder)?;
        glb.types
            .as_ref()
            .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?
            .encode_core_types(encoder, glb)?;
        glb.encode_base(encoder)?;
        encoder.close_element(ELEM_XML_SAVEFILE);
        Ok(())
    }

    fn restore_xml(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        let Some(el) = store.get_tag("xml_savefile") else {
            return Err(Error::Lowlevel("Could not find xml_savefile tag".to_string()));
        };
        self.sleigh.restore_xml_header(&el)?;
        let adjustvma = read_i64(
            el.get_attribute_value("adjustvma")?,
            Basefield::Auto,
            self.adjustvma.load(AtomicOrdering::Relaxed),
        );
        self.adjustvma.store(adjustvma, AtomicOrdering::Relaxed);
        let list = el.get_children();
        let mut iter = 0usize;
        if iter < list.len() && list[iter].get_name() == "binaryimage" {
            store.register_tag(&list[iter]);
            iter += 1;
        }
        if iter < list.len() && list[iter].get_name() == "specextensions" {
            store.register_tag(&list[iter]);
            iter += 1;
        }
        if iter < list.len() && list[iter].get_name() == "coretypes" {
            store.register_tag(&list[iter]);
            iter += 1;
        }
        glb.init(store)?;
        if iter < list.len() {
            store.register_tag(&list[iter]);
            glb.restore_xml_base(store)?;
        }
        Ok(())
    }
}
