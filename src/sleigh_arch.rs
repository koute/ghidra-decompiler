use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::sync::RwLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::atomic::{AtomicI32, Ordering as AtomicOrdering};
use std::sync::{Arc, Mutex, OnceLock};

use crate::address::{Address, MachExtreme, Range};
use crate::architecture::{
    ATTRIB_ADDRESS, Architecture, ArchitectureBuilder, ArchitectureCapability, ELEM_DEFAULT_SYMBOLS, ErrorStream,
};
use crate::comment::CommentDatabaseInternal;
use crate::cpool::ConstantPoolInternal;
use crate::database::{ATTRIB_VOLATILE, Database};
use crate::embedded_languages::EMBEDDED_FILES;
use crate::error::{Error, Result};
use crate::globalcontext::{ContextDatabase, ContextInternal};
use crate::inject_sleigh::PcodeInjectLibrarySleigh;
use crate::loadimage::SharedLoadImage;
use crate::marshal::{
    ATTRIB_CONTENT, ATTRIB_ID, ATTRIB_NAME, ATTRIB_SIZE, AttributeId, Decoder, ELEM_SYMBOL, ElementId, Encoder,
    XmlDecode,
};
use crate::opbehavior::OpBehaviorRef;
use crate::pcodeinject::PcodeInjectLibrary;
use crate::sleigh::{SharedContextDatabase, Sleigh};
use crate::stringmanage::StringManagerUnicode;
use crate::translate::{ELEM_TRUNCATE_SPACE, Translate, TruncationTag};
use crate::types::{TypeFactory, TypeMetatype};
use crate::varnode::Varnode;
use crate::xml::{self, DocumentStorage, Element};

pub const ATTRIB_DEPRECATED: AttributeId = AttributeId::new("deprecated", 136);
pub const ATTRIB_ENDIAN: AttributeId = AttributeId::new("endian", 137);
pub const ATTRIB_PROCESSOR: AttributeId = AttributeId::new("processor", 138);
pub const ATTRIB_PROCESSORSPEC: AttributeId = AttributeId::new("processorspec", 139);
pub const ATTRIB_SLAFILE: AttributeId = AttributeId::new("slafile", 140);
pub const ATTRIB_SPEC: AttributeId = AttributeId::new("spec", 141);
pub const ATTRIB_TARGET: AttributeId = AttributeId::new("target", 142);
pub const ATTRIB_VARIANT: AttributeId = AttributeId::new("variant", 143);
pub const ATTRIB_VERSION: AttributeId = AttributeId::new("version", 144);

pub const ELEM_COMPILER: ElementId = ElementId::new("compiler", 232);
pub const ELEM_DESCRIPTION: ElementId = ElementId::new("description", 233);
pub const ELEM_LANGUAGE: ElementId = ElementId::new("language", 234);
pub const ELEM_LANGUAGE_DEFINITIONS: ElementId = ElementId::new("language_definitions", 235);

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompilerTag {
    name: String,
    spec: String,
    id: String,
}

impl CompilerTag {
    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_COMPILER)?;
        self.name = decoder.read_string_attr(ATTRIB_NAME)?;
        self.spec = decoder.read_string_attr(ATTRIB_SPEC)?;
        self.id = decoder.read_string_attr(ATTRIB_ID)?;
        decoder.close_element(elem_id)
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_spec(&self) -> &str {
        &self.spec
    }

    pub fn get_id(&self) -> &str {
        &self.id
    }
}

#[derive(Clone, Debug, Default)]
pub struct LanguageDescription {
    processor: String,
    isbigendian: bool,
    size: i32,
    variant: String,
    version: String,
    slafile: String,
    processorspec: String,
    id: String,
    description: String,
    deprecated: bool,
    compilers: Vec<CompilerTag>,
    truncations: Vec<TruncationTag>,
}

impl LanguageDescription {
    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_LANGUAGE)?;
        self.processor = decoder.read_string_attr(ATTRIB_PROCESSOR)?;
        self.isbigendian = decoder.read_string_attr(ATTRIB_ENDIAN)? == "big";
        self.size = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as i32;
        self.variant = decoder.read_string_attr(ATTRIB_VARIANT)?;
        self.version = decoder.read_string_attr(ATTRIB_VERSION)?;
        self.slafile = decoder.read_string_attr(ATTRIB_SLAFILE)?;
        self.processorspec = decoder.read_string_attr(ATTRIB_PROCESSORSPEC)?;
        self.id = decoder.read_string_attr(ATTRIB_ID)?;
        self.deprecated = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_DEPRECATED {
                self.deprecated = decoder.read_bool()?;
            }
        }
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_DESCRIPTION {
                decoder.open_element()?;
                self.description = decoder.read_string_attr(ATTRIB_CONTENT)?;
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_COMPILER {
                let mut tag = CompilerTag::default();
                tag.decode(decoder)?;
                self.compilers.push(tag);
            } else if sub_id == ELEM_TRUNCATE_SPACE {
                let mut tag = TruncationTag::default();
                tag.decode(decoder)?;
                self.truncations.push(tag);
            } else {
                decoder.open_element()?;
                decoder.close_element_skipping(sub_id)?;
            }
        }
        decoder.close_element(elem_id)
    }

    pub fn get_processor(&self) -> &str {
        &self.processor
    }

    pub fn is_big_endian(&self) -> bool {
        self.isbigendian
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_variant(&self) -> &str {
        &self.variant
    }

    pub fn get_version(&self) -> &str {
        &self.version
    }

    pub fn get_sla_file(&self) -> &str {
        &self.slafile
    }

    pub fn get_processor_spec(&self) -> &str {
        &self.processorspec
    }

    pub fn get_id(&self) -> &str {
        &self.id
    }

    pub fn get_description(&self) -> &str {
        &self.description
    }

    pub fn is_deprecated(&self) -> bool {
        self.deprecated
    }

    pub fn get_compilers(&self) -> &[CompilerTag] {
        &self.compilers
    }

    pub fn get_compiler(&self, nm: &str) -> Result<&CompilerTag> {
        let mut defaultind = None;
        for (index, tag) in self.compilers.iter().enumerate() {
            if tag.get_id() == nm {
                return Ok(tag);
            }
            if tag.get_id() == "default" {
                defaultind = Some(index);
            }
        }
        if let Some(index) = defaultind {
            return Ok(&self.compilers[index]);
        }
        self.compilers
            .first()
            .ok_or_else(|| Error::Lowlevel(format!("language {} has no compiler specification", self.id)))
    }

    pub fn num_truncations(&self) -> i32 {
        self.truncations.len() as i32
    }

    pub fn get_truncation(&self, index: i32) -> &TruncationTag {
        &self.truncations[index as usize]
    }
}

pub fn normalize_processor(nm: &str) -> String {
    if nm.contains("386") {
        return "x86".to_string();
    }
    nm.to_string()
}

pub fn normalize_endian(nm: &str) -> String {
    if nm.contains("big") {
        return "BE".to_string();
    }
    if nm.contains("little") {
        return "LE".to_string();
    }
    nm.to_string()
}

pub fn normalize_size(nm: &str) -> String {
    let mut res = nm.to_string();
    if let Some(pos) = res.find("bit") {
        res.replace_range(pos..pos + 3, "");
    }
    if let Some(pos) = res.find('-') {
        res.replace_range(pos..pos + 1, "");
    }
    res
}

pub fn normalize_architecture(nm: &str) -> Result<String> {
    let mut pos = [0usize; 4];
    let mut count = 0;
    let mut curpos = 0usize;
    while count < 4 {
        let start = curpos + 1;
        let found = if start <= nm.len() {
            nm[start..].find(':').map(|index| index + start)
        } else {
            None
        };
        match found {
            None => break,
            Some(found) => {
                curpos = found;
                pos[count] = found;
                count += 1;
            }
        }
    }
    if count != 3 && count != 4 {
        return Err(Error::Lowlevel(format!(
            "Architecture string does not look like sleigh id: {nm}"
        )));
    }
    let processor = &nm[..pos[0]];
    let endian = &nm[pos[0] + 1..pos[1]];
    let size = &nm[pos[1] + 1..pos[2]];
    let (variant, compile) = if count == 4 {
        (&nm[pos[2] + 1..pos[3]], &nm[pos[3] + 1..])
    } else {
        (&nm[pos[2] + 1..], "default")
    };
    Ok(format!(
        "{}:{}:{}:{}:{}",
        normalize_processor(processor),
        normalize_endian(endian),
        normalize_size(size),
        variant,
        compile
    ))
}

#[derive(Clone, Debug)]
enum SpecFileData {
    Embedded(&'static [u8]),
    File(PathBuf),
}

#[derive(Clone, Debug)]
struct SpecDirectory {
    files: BTreeMap<String, SpecFileData>,
}

#[derive(Clone, Debug, Default)]
pub struct LanguageRegistry {
    descriptions: Vec<LanguageDescription>,
    directories: Vec<SpecDirectory>,
    warnings: Vec<String>,
}

pub struct SleighDecoder {
    pub sleigh: Sleigh,
    pub context: Arc<Mutex<ContextInternal>>,
    pub language: LanguageDescription,
    pub compiler: CompilerTag,
    pub warnings: Vec<String>,
}

impl SleighDecoder {
    pub fn set_context_override(&self, name: &str, value: u32) -> Result<()> {
        let codespace = self
            .sleigh
            .manager()
            .get_default_code_space()
            .ok_or_else(|| Error::Lowlevel("no default code space".to_string()))?;
        let mut context = self
            .context
            .lock()
            .map_err(|_| Error::Lowlevel("context database lock is poisoned".to_string()))?;
        context.set_variable_default(name, value)?;
        context.set_variable_region(name, &Address::new(codespace, 0), &Address::invalid(), value)
    }
}

impl LanguageRegistry {
    pub fn new() -> LanguageRegistry {
        LanguageRegistry::default()
    }

    pub fn embedded() -> LanguageRegistry {
        let mut registry = LanguageRegistry::new();
        let mut groups: Vec<((String, String), BTreeMap<String, SpecFileData>)> = Vec::new();
        for file in EMBEDDED_FILES.iter() {
            let (dir, name) = match file.path.rfind('/') {
                Some(pos) => (&file.path[..pos], &file.path[pos + 1..]),
                None => ("", file.path),
            };
            let key = (file.processor.to_string(), dir.to_string());
            match groups.iter_mut().find(|(group, _)| *group == key) {
                Some((_, files)) => {
                    files.insert(name.to_string(), SpecFileData::Embedded(file.data));
                }
                None => {
                    let mut files = BTreeMap::new();
                    files.insert(name.to_string(), SpecFileData::Embedded(file.data));
                    groups.push((key, files));
                }
            }
        }
        for (_, files) in groups {
            registry.add_spec_directory(files);
        }
        registry
    }

    pub fn from_directory(path: &Path) -> Result<LanguageRegistry> {
        let mut registry = LanguageRegistry::new();
        registry.add_directory(path)?;
        Ok(registry)
    }

    pub fn from_ghidra_root(path: &Path) -> Result<LanguageRegistry> {
        let mut registry = LanguageRegistry::new();
        registry.scan_for_sleigh_directories(path)?;
        Ok(registry)
    }

    fn list_directory(path: &Path) -> Vec<PathBuf> {
        let mut res: Vec<PathBuf> = match std::fs::read_dir(path) {
            Ok(entries) => entries
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .collect(),
            Err(_) => Vec::new(),
        };
        res.sort();
        res
    }

    fn scan_directories_with_name(path: &Path, name: &str, depth: i32, res: &mut Vec<PathBuf>) {
        if depth == 0 {
            return;
        }
        for entry in LanguageRegistry::list_directory(path) {
            if !entry.is_dir() {
                continue;
            }
            if entry.file_name().is_some_and(|file| file == name) {
                res.push(entry.clone());
            }
            LanguageRegistry::scan_directories_with_name(&entry, name, depth - 1, res);
        }
    }

    pub fn scan_for_sleigh_directories(&mut self, rootpath: &Path) -> Result<()> {
        let mut ghidradir = Vec::new();
        LanguageRegistry::scan_directories_with_name(rootpath, "Ghidra", 2, &mut ghidradir);
        let mut procdir = Vec::new();
        for dir in ghidradir.iter() {
            LanguageRegistry::scan_directories_with_name(dir, "Processors", 1, &mut procdir);
            LanguageRegistry::scan_directories_with_name(dir, "contrib", 1, &mut procdir);
        }
        let mut languagesubdirs = Vec::new();
        if !procdir.is_empty() {
            let mut procdir2 = Vec::new();
            for dir in procdir.iter() {
                procdir2.extend(
                    LanguageRegistry::list_directory(dir)
                        .into_iter()
                        .filter(|entry| entry.is_dir()),
                );
            }
            let mut datadirs = Vec::new();
            for dir in procdir2.iter() {
                LanguageRegistry::scan_directories_with_name(dir, "data", 1, &mut datadirs);
            }
            let mut languagedirs = Vec::new();
            for dir in datadirs.iter() {
                LanguageRegistry::scan_directories_with_name(dir, "languages", 1, &mut languagedirs);
            }
            languagesubdirs.extend(languagedirs.iter().cloned());
            for dir in languagedirs.iter() {
                languagesubdirs.extend(
                    LanguageRegistry::list_directory(dir)
                        .into_iter()
                        .filter(|entry| entry.is_dir()),
                );
            }
        }
        if languagesubdirs.is_empty() {
            languagesubdirs.push(rootpath.to_path_buf());
        }
        for dir in languagesubdirs {
            self.add_single_directory(&dir);
        }
        Ok(())
    }

    pub fn add_directory(&mut self, path: &Path) -> Result<()> {
        if !path.is_dir() {
            return Err(Error::Lowlevel(format!(
                "language directory does not exist: {}",
                path.display()
            )));
        }
        self.add_single_directory(path);
        for entry in LanguageRegistry::list_directory(path) {
            if entry.is_dir() {
                self.add_single_directory(&entry);
            }
        }
        Ok(())
    }

    fn add_single_directory(&mut self, path: &Path) {
        let mut files = BTreeMap::new();
        for entry in LanguageRegistry::list_directory(path) {
            if entry.is_file()
                && let Some(name) = entry.file_name().and_then(|name| name.to_str())
            {
                files.insert(name.to_string(), SpecFileData::File(entry.clone()));
            }
        }
        self.add_spec_directory(files);
    }

    fn add_spec_directory(&mut self, files: BTreeMap<String, SpecFileData>) {
        let ldefs: Vec<(String, SpecFileData)> = files
            .iter()
            .filter(|(name, _)| name.ends_with(".ldefs"))
            .map(|(name, data)| (name.clone(), data.clone()))
            .collect();
        self.directories.push(SpecDirectory { files });
        for (name, data) in ldefs {
            if let Err(err) = self.load_language_description(&name, &data) {
                self.warnings.push(err.explain().to_string());
            }
        }
    }

    fn read_data(data: &SpecFileData) -> Result<Vec<u8>> {
        match data {
            SpecFileData::Embedded(bytes) => Ok(bytes.to_vec()),
            SpecFileData::File(path) => {
                std::fs::read(path).map_err(|_| Error::Lowlevel(format!("Unable to open file: {}", path.display())))
            }
        }
    }

    fn load_language_description(&mut self, specfile: &str, data: &SpecFileData) -> Result<()> {
        let bytes = LanguageRegistry::read_data(data)?;
        let mut decoder = XmlDecode::new(None, 0);
        if decoder.ingest_stream(&bytes).is_err() {
            self.warnings
                .push(format!("WARNING: Unable to parse sleigh specfile: {specfile}"));
            return Ok(());
        }
        let elem_id = decoder.open_element_expect(ELEM_LANGUAGE_DEFINITIONS)?;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_LANGUAGE {
                let mut description = LanguageDescription::default();
                description.decode(&mut decoder)?;
                self.descriptions.push(description);
            } else {
                decoder.open_element()?;
                decoder.close_element_skipping(sub_id)?;
            }
        }
        decoder.close_element(elem_id)
    }

    pub fn get_descriptions(&self) -> &[LanguageDescription] {
        &self.descriptions
    }

    pub fn get_warnings(&self) -> &[String] {
        &self.warnings
    }

    pub fn find_file(&self, name: &str) -> Option<Vec<u8>> {
        let path = Path::new(name);
        if path.is_absolute() {
            return std::fs::read(path).ok();
        }
        for dir in self.directories.iter() {
            if let Some(data) = dir.files.get(name) {
                return LanguageRegistry::read_data(data).ok();
            }
        }
        None
    }

    pub fn resolve_architecture(&self, target: &str) -> Result<(usize, String, Vec<String>)> {
        let mut archid = target.to_string();
        if let Some(stripped) = archid.strip_prefix("binary-") {
            archid = stripped.to_string();
        } else if let Some(stripped) = archid.strip_prefix("default-") {
            archid = stripped.to_string();
        }
        archid = normalize_architecture(&archid)?;
        let baseid = &archid[..archid.rfind(':').unwrap_or(archid.len())];
        let mut warnings = Vec::new();
        for (index, description) in self.descriptions.iter().enumerate() {
            if description.get_id() == baseid {
                if description.is_deprecated() {
                    warnings.push(format!("WARNING: Language {baseid} is deprecated"));
                }
                return Ok((index, archid.clone(), warnings));
            }
        }
        Err(Error::Lowlevel(format!("No sleigh specification for {baseid}")))
    }

    fn parse_spec(&self, name: &str, kind: &str) -> Result<Arc<Element>> {
        let Some(bytes) = self.find_file(name) else {
            return Err(Error::Sleigh(format!(
                "Error reading {kind} specification: {name}\n Unable to open xml document {name}"
            )));
        };
        match xml::xml_tree(&bytes) {
            Ok(doc) => Ok(doc.get_root().clone()),
            Err(Error::Decoder(message)) => Err(Error::Sleigh(format!(
                "XML error parsing {kind} specification: {name}\n {message}"
            ))),
            Err(err) => Err(Error::Sleigh(format!(
                "Error reading {kind} specification: {name}\n {}",
                err.explain()
            ))),
        }
    }

    fn apply_context_data(sleigh: &Sleigh, context: &Arc<Mutex<ContextInternal>>, root: &Arc<Element>) -> Result<()> {
        for child in root.get_children() {
            if child.get_name() != "context_data" {
                continue;
            }
            let mut decoder = XmlDecode::with_root(Some(sleigh.manager()), child.clone(), 0);
            decoder.set_translate(Some(sleigh));
            let mut guard = context
                .lock()
                .map_err(|_| Error::Lowlevel("context database lock is poisoned".to_string()))?;
            guard.decode_from_spec(&mut decoder)?;
        }
        Ok(())
    }

    pub fn build_decoder(&self, target: &str, loader: SharedLoadImage) -> Result<SleighDecoder> {
        let (index, archid, warnings) = self.resolve_architecture(target)?;
        let language = self.descriptions[index].clone();
        let compiler_name = &archid[archid.rfind(':').map(|pos| pos + 1).unwrap_or(0)..];
        let compiler = language.get_compiler(compiler_name)?.clone();
        let Some(sla) = self.find_file(language.get_sla_file()) else {
            return Err(Error::Sleigh(format!("Could not find .sla file for {archid}")));
        };
        let processor_root = self.parse_spec(language.get_processor_spec(), "processor")?;
        let compiler_root = self.parse_spec(compiler.get_spec(), "compiler")?;
        if processor_root.get_name() != "processor_spec" {
            return Err(Error::Lowlevel("No processor configuration tag found".to_string()));
        }
        if compiler_root.get_name() != "compiler_spec" {
            return Err(Error::Lowlevel("No compiler configuration tag found".to_string()));
        }
        let context = Arc::new(Mutex::new(ContextInternal::new()));
        let shared: SharedContextDatabase = context.clone();
        let mut sleigh = Sleigh::new(loader, shared);
        sleigh.initialize_from_sla(&sla)?;
        for truncation in language.truncations.iter() {
            sleigh.manager().truncate_space(truncation)?;
        }
        LanguageRegistry::apply_context_data(&sleigh, &context, &processor_root)?;
        sleigh.set_default_float_formats();
        LanguageRegistry::apply_context_data(&sleigh, &context, &compiler_root)?;
        Ok(SleighDecoder {
            sleigh,
            context,
            language,
            compiler,
            warnings,
        })
    }
}

pub fn build_embedded_decoder(target: &str, loader: SharedLoadImage) -> Result<SleighDecoder> {
    LanguageRegistry::embedded().build_decoder(target, loader)
}

pub type BehaviorCell = Arc<OnceLock<Vec<Option<OpBehaviorRef>>>>;

pub trait AdjustableLoadImage: Send + Sync {
    fn adjust_vma_shared(&self, adjust: i64);
}

pub type LoaderSlot = Arc<RwLock<Option<Arc<dyn AdjustableLoadImage>>>>;

pub trait SleighCapability: ArchitectureCapability {
    fn build_with_slot(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<(Box<Architecture>, LoaderSlot)>;
}

pub fn sleigh_capabilities() -> Vec<&'static dyn SleighCapability> {
    let mut thelist: Vec<&'static dyn SleighCapability> = vec![
        &crate::xml_arch::XML_ARCHITECTURE_CAPABILITY,
        &crate::object_arch::OBJECT_ARCHITECTURE_CAPABILITY,
        &crate::raw_arch::RAW_BINARY_ARCHITECTURE_CAPABILITY,
    ];
    if let Some(index) = thelist.iter().position(|capa| capa.get_name() == "raw") {
        let capa = thelist.remove(index);
        thelist.push(capa);
    }
    thelist
}

pub fn find_sleigh_capability(filename: &str) -> Option<&'static dyn SleighCapability> {
    sleigh_capabilities()
        .into_iter()
        .find(|capa| capa.is_file_match(filename))
}

pub fn find_sleigh_capability_doc(doc: &xml::Document) -> Option<&'static dyn SleighCapability> {
    sleigh_capabilities().into_iter().find(|capa| capa.is_xml_match(doc))
}

pub fn get_sleigh_capability(name: &str) -> Option<&'static dyn SleighCapability> {
    sleigh_capabilities().into_iter().find(|capa| capa.get_name() == name)
}

static GLOBAL_REGISTRY: OnceLock<Mutex<Arc<LanguageRegistry>>> = OnceLock::new();

static SPEC_FILES_COLLECTED: AtomicBool = AtomicBool::new(false);

fn global_registry_slot() -> &'static Mutex<Arc<LanguageRegistry>> {
    GLOBAL_REGISTRY.get_or_init(|| Mutex::new(Arc::new(LanguageRegistry::embedded())))
}

pub fn global_language_registry() -> Arc<LanguageRegistry> {
    global_registry_slot()
        .lock()
        .map(|guard| guard.clone())
        .unwrap_or_else(|poisoned| poisoned.into_inner().clone())
}

pub fn set_global_language_registry(registry: LanguageRegistry) {
    let mut guard = global_registry_slot()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    *guard = Arc::new(registry);
}

pub fn add_global_language_directory(path: &Path) -> Result<()> {
    let mut guard = global_registry_slot()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let mut registry = (**guard).clone();
    registry.add_directory(path)?;
    *guard = Arc::new(registry);
    Ok(())
}

pub fn scan_global_sleigh_directories(rootpath: &Path) -> Result<()> {
    let mut guard = global_registry_slot()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let mut registry = (**guard).clone();
    registry.scan_for_sleigh_directories(rootpath)?;
    *guard = Arc::new(registry);
    Ok(())
}

pub struct SleighArchitecture {
    registry: Arc<LanguageRegistry>,
    languageindex: AtomicI32,
    filename: RwLock<String>,
    target: RwLock<String>,
    slabytes: RwLock<Option<Vec<u8>>>,
    behaviors: RwLock<Option<BehaviorCell>>,
    loader_slot: LoaderSlot,
    pub errorstream: Option<ErrorStream>,
}

impl SleighArchitecture {
    pub fn new(fname: &str, targ: &str, estream: Option<ErrorStream>) -> SleighArchitecture {
        SleighArchitecture::with_registry(global_language_registry(), fname, targ, estream)
    }

    pub fn with_registry(
        registry: Arc<LanguageRegistry>,
        fname: &str,
        targ: &str,
        estream: Option<ErrorStream>,
    ) -> SleighArchitecture {
        SleighArchitecture {
            registry,
            languageindex: AtomicI32::new(-1),
            filename: RwLock::new(fname.to_string()),
            target: RwLock::new(targ.to_string()),
            slabytes: RwLock::new(None),
            behaviors: RwLock::new(None),
            loader_slot: Arc::new(RwLock::new(None)),
            errorstream: estream,
        }
    }

    pub fn registry(&self) -> &Arc<LanguageRegistry> {
        &self.registry
    }

    pub fn loader_slot(&self) -> LoaderSlot {
        self.loader_slot.clone()
    }

    pub fn set_adjustable_loader(&self, loader: Arc<dyn AdjustableLoadImage>) {
        *self.loader_slot.write().expect("poisoned lock") = Some(loader);
    }

    pub fn collect_spec_files(&self) {
        if SPEC_FILES_COLLECTED.swap(true, Ordering::SeqCst) {
            return;
        }
        for warning in self.registry.get_warnings() {
            if let Some(stream) = &self.errorstream {
                stream.lock().expect("poisoned output stream lock").push_str(warning);
            }
        }
    }

    pub fn get_filename(&self) -> String {
        self.filename.read().expect("poisoned lock").clone()
    }

    pub fn get_target(&self) -> String {
        self.target.read().expect("poisoned lock").clone()
    }

    pub fn get_language_index(&self) -> i32 {
        self.languageindex.load(AtomicOrdering::Relaxed)
    }

    fn language(&self) -> Result<&LanguageDescription> {
        let index = self.languageindex.load(AtomicOrdering::Relaxed);
        if index < 0 {
            return Err(Error::Lowlevel("no language has been resolved".to_string()));
        }
        Ok(&self.registry.get_descriptions()[index as usize])
    }

    pub fn encode_header(&self, encoder: &mut dyn Encoder) {
        encoder.write_string(ATTRIB_NAME, &self.filename.read().expect("poisoned lock"));
        encoder.write_string(ATTRIB_TARGET, &self.target.read().expect("poisoned lock"));
    }

    pub fn restore_xml_header(&self, el: &Element) -> Result<()> {
        *self.filename.write().expect("poisoned lock") = el.get_attribute_value("name")?.to_string();
        *self.target.write().expect("poisoned lock") = el.get_attribute_value("target")?.to_string();
        Ok(())
    }

    pub fn print_warning(&self, message: &str) {
        if let Some(stream) = &self.errorstream {
            let mut out = stream.lock().expect("poisoned output stream lock");
            out.push_str("WARNING: ");
            out.push_str(message);
            out.push('\n');
        }
    }

    pub fn get_description(&self) -> String {
        match self.language() {
            Ok(language) => language.get_description().to_string(),
            Err(_) => String::new(),
        }
    }

    pub fn build_translator(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<Box<dyn Translate>> {
        let loader = glb
            .loader
            .clone()
            .ok_or_else(|| Error::Lowlevel("no load image for translator".to_string()))?;
        let context = glb
            .context
            .clone()
            .ok_or_else(|| Error::Lowlevel("no context database for translator".to_string()))?;
        let sla = self.slabytes.write().expect("poisoned lock").take();
        let Some(bytes) = sla else {
            let mut sleigh = Sleigh::new(loader, context);
            sleigh.initialize(store)?;
            return Ok(Box::new(sleigh));
        };
        let key = translator_key(&bytes);
        let cached = parsed_translators().lock().expect("poisoned lock").get(&key).cloned();
        let mut sleigh = match cached {
            Some(base) => Sleigh::from_base(loader, context, base.as_ref().clone()),
            None => Sleigh::new(loader, context),
        };
        let fresh = !sleigh.base().is_initialized();
        sleigh.initialize_from_sla(&bytes)?;
        if fresh {
            parsed_translators()
                .lock()
                .expect("poisoned lock")
                .insert(key, Arc::new(sleigh.base().clone()));
        }
        Ok(Box::new(sleigh))
    }

    pub fn build_pcode_inject_library(&self, glb: &mut Architecture) -> Result<Box<dyn PcodeInjectLibrary>> {
        let library = PcodeInjectLibrarySleigh::new(glb)?;
        *self.behaviors.write().expect("poisoned lock") = Some(library.behavior_cell());
        Ok(Box::new(library))
    }

    pub fn build_typegrp(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        glb.types = Some(Box::new(TypeFactory::new()));
        Ok(())
    }

    pub fn build_core_types(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        if let Some(el) = store.get_tag("coretypes") {
            let mut decoder = XmlDecode::with_root(None, el, 0);
            return TypeFactory::decode_core_types(glb, &mut decoder);
        }
        let types = glb
            .types
            .as_mut()
            .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?;
        let core: [(&str, i32, TypeMetatype, bool); 22] = [
            ("void", 1, TypeMetatype::Void, false),
            ("bool", 1, TypeMetatype::Bool, false),
            ("uint1", 1, TypeMetatype::Uint, false),
            ("uint2", 2, TypeMetatype::Uint, false),
            ("uint4", 4, TypeMetatype::Uint, false),
            ("uint8", 8, TypeMetatype::Uint, false),
            ("int1", 1, TypeMetatype::Int, false),
            ("int2", 2, TypeMetatype::Int, false),
            ("int4", 4, TypeMetatype::Int, false),
            ("int8", 8, TypeMetatype::Int, false),
            ("float4", 4, TypeMetatype::Float, false),
            ("float8", 8, TypeMetatype::Float, false),
            ("float10", 10, TypeMetatype::Float, false),
            ("float16", 16, TypeMetatype::Float, false),
            ("xunknown1", 1, TypeMetatype::Unknown, false),
            ("xunknown2", 2, TypeMetatype::Unknown, false),
            ("xunknown4", 4, TypeMetatype::Unknown, false),
            ("xunknown8", 8, TypeMetatype::Unknown, false),
            ("code", 1, TypeMetatype::Code, false),
            ("char", 1, TypeMetatype::Int, true),
            ("wchar2", 2, TypeMetatype::Int, true),
            ("wchar4", 4, TypeMetatype::Int, true),
        ];
        for (name, size, meta, chartp) in core {
            types.set_core_type(name, size, meta, chartp)?;
        }
        types.cache_core_types()
    }

    pub fn build_comment_db(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        glb.commentdb = Some(Box::new(CommentDatabaseInternal::new()));
        Ok(())
    }

    pub fn build_string_manager(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        glb.string_manager = Some(Box::new(StringManagerUnicode::new(2048)));
        Ok(())
    }

    pub fn build_constant_pool(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        glb.cpool = Some(Box::new(ConstantPoolInternal::new()));
        Ok(())
    }

    pub fn build_context(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        let context: SharedContextDatabase = Arc::new(Mutex::new(ContextInternal::new()));
        glb.context = Some(context);
        Ok(())
    }

    pub fn build_symbols(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        let Some(symtag) = store.get_tag(ELEM_DEFAULT_SYMBOLS.get_name()) else {
            return Ok(());
        };
        let mut decoder = XmlDecode::with_root(None, symtag, 0);
        let el = decoder.open_element_expect(ELEM_DEFAULT_SYMBOLS)?;
        let mut last_addr = Address::extreme(MachExtreme::Minimal);
        let mut last_size: i32 = -1;
        while decoder.peek_element()? != 0 {
            let subel = decoder.open_element_expect(ELEM_SYMBOL)?;
            let mut addr = Address::invalid();
            let mut name = String::new();
            let mut size: i32 = 0;
            let mut volatile_state: i32 = -1;
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_NAME {
                    name = decoder.read_string()?;
                } else if attrib_id == ATTRIB_ADDRESS {
                    let addr_str = decoder.read_string()?;
                    if addr_str == "next" && last_size != -1 {
                        addr = last_addr.add(last_size as i64);
                    } else {
                        addr = glb.manager.parse_address_simple(&addr_str)?;
                    }
                } else if attrib_id == ATTRIB_VOLATILE {
                    volatile_state = if decoder.read_bool()? { 1 } else { 0 };
                } else if attrib_id == ATTRIB_SIZE {
                    size = decoder.read_signed_integer()? as i32;
                }
            }
            decoder.close_element(subel)?;
            if name.is_empty() {
                return Err(Error::Lowlevel(
                    "Missing name attribute in <symbol> element".to_string(),
                ));
            }
            let Some(space) = addr.get_space().cloned() else {
                return Err(Error::Lowlevel(
                    "Missing address attribute in <symbol> element".to_string(),
                ));
            };
            if size == 0 {
                size = space.get_word_size() as i32;
            }
            if volatile_state >= 0 {
                let range = Range::new(
                    space.clone(),
                    addr.get_offset(),
                    addr.get_offset().wrapping_add((size - 1) as u64),
                );
                let symboltab = glb
                    .symboltab
                    .as_mut()
                    .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))?;
                if volatile_state == 0 {
                    symboltab.clear_property_range(Varnode::VOLATIL, &range, &glb.manager);
                } else {
                    symboltab.set_property_range(Varnode::VOLATIL, &range, &glb.manager);
                }
            }
            let ct = glb
                .types
                .as_mut()
                .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?
                .get_base(size, TypeMetatype::Unknown)?;
            let usepoint = Address::invalid();
            let global = glb
                .symboltab
                .as_ref()
                .and_then(|symboltab| symboltab.get_global_scope())
                .ok_or_else(|| Error::Lowlevel("missing global scope".to_string()))?;
            Database::scope_add_symbol_at(glb, global, &name, Some(ct), &addr, &usepoint)?;
            last_addr = addr;
            last_size = size;
        }
        decoder.close_element(el)
    }

    pub fn resolve_architecture(&self, glb: &mut Architecture) -> Result<()> {
        if glb.archid.is_empty() {
            let target = self.target.read().expect("poisoned lock").clone();
            if target.is_empty() || target == "default" {
                glb.archid = glb
                    .loader
                    .as_ref()
                    .map(|loader| loader.get_arch_type())
                    .unwrap_or_default();
            } else {
                glb.archid = target;
            }
        }
        if let Some(stripped) = glb.archid.strip_prefix("binary-") {
            glb.archid = stripped.to_string();
        } else if let Some(stripped) = glb.archid.strip_prefix("default-") {
            glb.archid = stripped.to_string();
        }
        glb.archid = normalize_architecture(&glb.archid)?;
        let baseid = glb.archid[..glb.archid.rfind(':').unwrap_or(glb.archid.len())].to_string();
        self.languageindex.store(-1, AtomicOrdering::Relaxed);
        for (index, description) in self.registry.get_descriptions().iter().enumerate() {
            if description.get_id() == baseid {
                self.languageindex.store(index as i32, AtomicOrdering::Relaxed);
                if description.is_deprecated() {
                    self.print_warning(&format!("Language {baseid} is deprecated"));
                }
                break;
            }
        }
        if self.languageindex.load(AtomicOrdering::Relaxed) == -1 {
            return Err(Error::Lowlevel(format!("No sleigh specification for {baseid}")));
        }
        Ok(())
    }

    fn register_spec(&self, store: &mut DocumentStorage, name: &str, kind: &str) -> Result<()> {
        let Some(bytes) = self.registry.find_file(name) else {
            return Err(Error::Sleigh(format!(
                "XML error parsing {kind} specification: \n Unable to open xml document "
            )));
        };
        match store.parse_document(&bytes) {
            Ok(doc) => {
                store.register_tag(doc.get_root());
                Ok(())
            }
            Err(Error::Decoder(message)) => Err(Error::Sleigh(format!(
                "XML error parsing {kind} specification: {name}\n {message}"
            ))),
            Err(err) => Err(Error::Sleigh(format!(
                "Error reading {kind} specification: {name}\n {}",
                err.explain()
            ))),
        }
    }

    pub fn build_spec_file(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        let language = self.language()?.clone();
        let compiler = glb.archid[glb.archid.rfind(':').map(|pos| pos + 1).unwrap_or(0)..].to_string();
        let compilertag = language.get_compiler(&compiler)?.clone();
        let Some(sla) = self.registry.find_file(language.get_sla_file()) else {
            return Err(Error::Sleigh(format!("Could not find .sla file for {}", glb.archid)));
        };
        self.register_spec(store, language.get_processor_spec(), "processor")?;
        self.register_spec(store, compilertag.get_spec(), "compiler")?;
        *self.slabytes.write().expect("poisoned lock") = Some(sla);
        Ok(())
    }

    pub fn modify_spaces(&self, _glb: &mut Architecture, trans: &mut dyn Translate) -> Result<()> {
        let language = self.language()?;
        for index in 0..language.num_truncations() {
            trans.manager().truncate_space(language.get_truncation(index))?;
        }
        Ok(())
    }

    pub fn collect_behaviors(&self, glb: &Architecture) {
        let Some(cell) = self.behaviors.read().expect("poisoned lock").clone() else {
            return;
        };
        let behaviors: Vec<Option<OpBehaviorRef>> = glb
            .inst
            .iter()
            .map(|slot| slot.as_ref().and_then(|op| op.base().behave.clone()))
            .collect();
        let _ = cell.set(behaviors);
    }
}

pub trait SleighArchitectureHooks: Send + Sync {
    fn sleigh(&self) -> &SleighArchitecture;

    fn build_loader(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn resolve_architecture(&self, glb: &mut Architecture) -> Result<()> {
        self.sleigh().resolve_architecture(glb)
    }

    fn post_spec_file(&self, glb: &mut Architecture) -> Result<()> {
        glb.post_spec_file_base()
    }

    fn encode(&self, glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        glb.encode_base(encoder)
    }

    fn restore_xml(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        glb.restore_xml_base(store)
    }
}

impl<T: SleighArchitectureHooks> ArchitectureBuilder for T {
    fn get_description(&self, _glb: &Architecture) -> String {
        self.sleigh().get_description()
    }

    fn print_warning(&self, _glb: &Architecture, message: &str) {
        self.sleigh().print_warning(message)
    }

    fn encode(&self, glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        SleighArchitectureHooks::encode(self, glb, encoder)
    }

    fn restore_xml(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        SleighArchitectureHooks::restore_xml(self, glb, store)
    }

    fn build_translator(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<Box<dyn Translate>> {
        self.sleigh().build_translator(glb, store)
    }

    fn build_loader(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        SleighArchitectureHooks::build_loader(self, glb, store)
    }

    fn build_pcode_inject_library(&self, glb: &mut Architecture) -> Result<Box<dyn PcodeInjectLibrary>> {
        self.sleigh().build_pcode_inject_library(glb)
    }

    fn build_typegrp(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_typegrp(glb, store)
    }

    fn build_core_types(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_core_types(glb, store)
    }

    fn build_comment_db(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_comment_db(glb, store)
    }

    fn build_string_manager(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_string_manager(glb, store)
    }

    fn build_constant_pool(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_constant_pool(glb, store)
    }

    fn build_instructions(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        glb.build_instructions_base(store)?;
        self.sleigh().collect_behaviors(glb);
        Ok(())
    }

    fn build_context(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_context(glb, store)
    }

    fn build_symbols(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_symbols(glb, store)
    }

    fn build_spec_file(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        self.sleigh().build_spec_file(glb, store)
    }

    fn modify_spaces(&self, glb: &mut Architecture, trans: &mut dyn Translate) -> Result<()> {
        self.sleigh().modify_spaces(glb, trans)
    }

    fn post_spec_file(&self, glb: &mut Architecture) -> Result<()> {
        SleighArchitectureHooks::post_spec_file(self, glb)
    }

    fn resolve_architecture(&self, glb: &mut Architecture) -> Result<()> {
        SleighArchitectureHooks::resolve_architecture(self, glb)
    }
}

fn parsed_translators() -> &'static Mutex<HashMap<u64, Arc<crate::sleighbase::SleighBase>>> {
    static TRANSLATORS: OnceLock<Mutex<HashMap<u64, Arc<crate::sleighbase::SleighBase>>>> = OnceLock::new();
    TRANSLATORS.get_or_init(|| Mutex::new(HashMap::new()))
}

fn translator_key(sla: &[u8]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    sla.hash(&mut hasher);
    hasher.finish()
}
