use std::sync::atomic::{AtomicI64, Ordering as AtomicOrdering};
use std::sync::{Arc, RwLock};

use crate::address::{Address, RangeList};
use crate::architecture::{ATTRIB_ADJUSTVMA, Architecture, ArchitectureCapability, ErrorStream};
use crate::capability::CapabilityPoint;
use crate::error::{Error, Result};
use crate::istream::{Basefield, read_i64};
use crate::loadimage::{LoadImage, LoadImageFunc, LoadImageSection, RawLoadImage, SharedLoadImage};
use crate::marshal::{ElementId, Encoder};
use crate::sleigh_arch::{
    AdjustableLoadImage, LoaderSlot, SleighArchitecture, SleighArchitectureHooks, SleighCapability,
};
use crate::space::SpaceRef;
use crate::xml::{Document, DocumentStorage};

pub const ELEM_RAW_SAVEFILE: ElementId = ElementId::new("raw_savefile", 237);

#[derive(Debug)]
pub struct SharedRawLoadImage {
    filename: String,
    inner: RwLock<RawLoadImage>,
}

impl SharedRawLoadImage {
    pub fn new(image: RawLoadImage) -> SharedRawLoadImage {
        SharedRawLoadImage {
            filename: image.get_file_name().to_string(),
            inner: RwLock::new(image),
        }
    }

    pub fn attach_to_space(&self, id: SpaceRef) {
        self.inner
            .write()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .attach_to_space(id);
    }
}

impl LoadImage for SharedRawLoadImage {
    fn get_file_name(&self) -> &str {
        &self.filename
    }

    fn load_fill(&self, ptr: &mut [u8], addr: &Address) -> Result<()> {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .load_fill(ptr, addr)
    }

    fn open_symbols(&self) {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .open_symbols()
    }

    fn close_symbols(&self) {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .close_symbols()
    }

    fn get_next_symbol(&self, record: &mut LoadImageFunc) -> bool {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get_next_symbol(record)
    }

    fn open_section_info(&self) {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .open_section_info()
    }

    fn close_section_info(&self) {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .close_section_info()
    }

    fn get_next_section(&self, record: &mut LoadImageSection) -> bool {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get_next_section(record)
    }

    fn get_readonly(&self, list: &mut RangeList) {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get_readonly(list)
    }

    fn get_arch_type(&self) -> String {
        self.inner
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get_arch_type()
    }

    fn adjust_vma(&mut self, adjust: i64) {
        self.adjust_vma_shared(adjust);
    }
}

impl AdjustableLoadImage for SharedRawLoadImage {
    fn adjust_vma_shared(&self, adjust: i64) {
        self.inner
            .write()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .adjust_vma(adjust);
    }
}

pub struct RawBinaryArchitectureCapability;

pub static RAW_BINARY_ARCHITECTURE_CAPABILITY: RawBinaryArchitectureCapability = RawBinaryArchitectureCapability;

impl CapabilityPoint for RawBinaryArchitectureCapability {
    fn initialize(&self) -> Result<()> {
        Ok(())
    }
}

impl ArchitectureCapability for RawBinaryArchitectureCapability {
    fn get_name(&self) -> &str {
        "raw"
    }

    fn build_architecture(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<Box<Architecture>> {
        Ok(self.build_with_slot(filename, target, estream)?.0)
    }

    fn is_file_match(&self, _filename: &str) -> bool {
        true
    }

    fn is_xml_match(&self, doc: &Document) -> bool {
        doc.get_root().get_name() == "raw_savefile"
    }
}

impl SleighCapability for RawBinaryArchitectureCapability {
    fn build_with_slot(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<(Box<Architecture>, LoaderSlot)> {
        let builder = RawBinaryArchitecture::new(filename, target, estream);
        let slot = builder.sleigh.loader_slot();
        let mut glb = Box::new(Architecture::new());
        glb.builder = Some(Arc::new(builder));
        Ok((glb, slot))
    }
}

pub struct RawBinaryArchitecture {
    pub sleigh: SleighArchitecture,
    adjustvma: AtomicI64,
    loader: RwLock<Option<Arc<SharedRawLoadImage>>>,
    image_bytes: Option<Vec<u8>>,
}

impl RawBinaryArchitecture {
    pub fn new(fname: &str, targ: &str, estream: Option<ErrorStream>) -> RawBinaryArchitecture {
        RawBinaryArchitecture {
            sleigh: SleighArchitecture::new(fname, targ, estream),
            adjustvma: AtomicI64::new(0),
            loader: RwLock::new(None),
            image_bytes: None,
        }
    }

    pub fn with_bytes(fname: &str, targ: &str, bytes: Vec<u8>, base_address: u64) -> RawBinaryArchitecture {
        RawBinaryArchitecture {
            image_bytes: Some(bytes),
            adjustvma: AtomicI64::new(base_address as i64),
            ..RawBinaryArchitecture::new(fname, targ, None)
        }
    }
}

impl SleighArchitectureHooks for RawBinaryArchitecture {
    fn sleigh(&self) -> &SleighArchitecture {
        &self.sleigh
    }

    fn build_loader(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        self.sleigh.collect_spec_files();
        let mut ldr = match &self.image_bytes {
            Some(bytes) => RawLoadImage::from_bytes(&self.sleigh.get_filename(), bytes.clone()),
            None => {
                let mut ldr = RawLoadImage::new(&self.sleigh.get_filename());
                ldr.open()?;
                ldr
            }
        };
        if self.adjustvma.load(AtomicOrdering::Relaxed) != 0 {
            ldr.adjust_vma(self.adjustvma.load(AtomicOrdering::Relaxed));
        }
        let loader = Arc::new(SharedRawLoadImage::new(ldr));
        *self.loader.write().expect("poisoned lock") = Some(loader.clone());
        self.sleigh.set_adjustable_loader(loader.clone());
        let shared: SharedLoadImage = loader;
        glb.loader = Some(shared);
        Ok(())
    }

    fn resolve_architecture(&self, glb: &mut Architecture) -> Result<()> {
        glb.archid = self.sleigh.get_target();
        self.sleigh.resolve_architecture(glb)
    }

    fn post_spec_file(&self, glb: &mut Architecture) -> Result<()> {
        glb.post_spec_file_base()?;
        let loader = self
            .loader
            .read()
            .expect("poisoned lock")
            .clone()
            .ok_or_else(|| Error::Lowlevel("missing raw load image".to_string()))?;
        if let Some(space) = glb.manager.get_default_code_space() {
            loader.attach_to_space(space);
        }
        Ok(())
    }

    fn encode(&self, glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_RAW_SAVEFILE);
        self.sleigh.encode_header(encoder);
        encoder.write_unsigned_integer(ATTRIB_ADJUSTVMA, self.adjustvma.load(AtomicOrdering::Relaxed) as u64);
        glb.types
            .as_ref()
            .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?
            .encode_core_types(encoder, glb)?;
        glb.encode_base(encoder)?;
        encoder.close_element(ELEM_RAW_SAVEFILE);
        Ok(())
    }

    fn restore_xml(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        let Some(el) = store.get_tag("raw_savefile") else {
            return Err(Error::Lowlevel("Could not find raw_savefile tag".to_string()));
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
