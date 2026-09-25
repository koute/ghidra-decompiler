use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use crate::action::{ActionDatabase, Rule};
use crate::address::{Address, Range, RangeList, RangeProperties, calc_mask};
use crate::arena::Arena;
use crate::capability::CapabilityPoint;
use crate::comment::{Comment, CommentDatabase, ELEM_COMMENTDB};
use crate::cpool::{ConstantPool, ELEM_CONSTANTPOOL};
use crate::database::{Database, ELEM_DB, Scope, ScopeId, SymbolId};
use crate::error::{Error, Result};
use crate::float::format_float_general;
use crate::fspec::{ELEM_PROTOTYPE, ELEM_RESOLVEPROTOTYPE, ModelId, ProtoModel, PrototypePieces};
use crate::funcdata::Funcdata;
use crate::globalcontext::{ELEM_CONTEXT_DATA, ELEM_CONTEXT_POINTS};
use crate::loadimage::{LoadImageFunc, SharedLoadImage};
use crate::marshal::{
    ATTRIB_ALIGN, ATTRIB_NAME, ATTRIB_SPACE, ATTRIB_TYPE, AttributeId, Decoder, ELEM_RETURNADDRESS, ElementId, Encoder,
    XmlDecode,
};
use crate::opbehavior::OpBehaviorRef;
use crate::options::{ELEM_OPTIONSLIST, OptionDatabase, OptionSplitDatatypes};
use crate::overrides::{ELEM_CALLDEST, ELEM_DEADCODEDELAY, ELEM_FLOW};
use crate::pcodeinject::{CALLFIXUP_TYPE, ELEM_CALLFIXUP, ELEM_CALLOTHERFIXUP, ELEM_INJECTDEBUG, PcodeInjectLibrary};
use crate::pcoderaw::VarnodeData;
use crate::prefersplit::{ELEM_PREFERSPLIT, PreferSplitManager, PreferSplitRecord};
use crate::printlanguage::{PrintLanguage, find_capability as find_print_capability, get_default_capability};
use crate::sleigh::SharedContextDatabase;
use crate::space::{AddrSpace, OTHER_SPACE_NAME, SpaceRef, SpaceType};
use crate::stringmanage::{ELEM_STRINGMANAGE, StringManager};
use crate::transform::{ATTRIB_VECTOR_LANE_SIZES, LanedRegister};
use crate::translate::{AddrSpaceManager, AddressResolver, Translate};
use crate::typeop::TypeOp;
use crate::types::{ELEM_DATA_ORGANIZATION, ELEM_ENUM, ELEM_TYPEGRP, TypeFactory};
use crate::userop::{ELEM_JUMPASSIST, ELEM_SEGMENTOP, UserOpManage, UserPcodeOp};
use crate::varnode::Varnode;
use crate::xml::{Document, DocumentStorage};

pub const ATTRIB_ADDRESS: AttributeId = AttributeId::new("address", 148);
pub const ATTRIB_ADJUSTVMA: AttributeId = AttributeId::new("adjustvma", 103);
pub const ATTRIB_ENABLE: AttributeId = AttributeId::new("enable", 104);
pub const ATTRIB_GROUP: AttributeId = AttributeId::new("group", 105);
pub const ATTRIB_GROWTH: AttributeId = AttributeId::new("growth", 106);
pub const ATTRIB_KEY: AttributeId = AttributeId::new("key", 107);
pub const ATTRIB_LOADERSYMBOLS: AttributeId = AttributeId::new("loadersymbols", 108);
pub const ATTRIB_PARENT: AttributeId = AttributeId::new("parent", 109);
pub const ATTRIB_REGISTER: AttributeId = AttributeId::new("register", 110);
pub const ATTRIB_REVERSEJUSTIFY: AttributeId = AttributeId::new("reversejustify", 111);
pub const ATTRIB_SIGNEXT: AttributeId = AttributeId::new("signext", 112);
pub const ATTRIB_STYLE: AttributeId = AttributeId::new("style", 113);
pub const ELEM_ADDRESS_SHIFT_AMOUNT: ElementId = ElementId::new("address_shift_amount", 130);
pub const ELEM_AGGRESSIVETRIM: ElementId = ElementId::new("aggressivetrim", 131);
pub const ELEM_COMPILER_SPEC: ElementId = ElementId::new("compiler_spec", 132);
pub const ELEM_DATA_SPACE: ElementId = ElementId::new("data_space", 133);
pub const ELEM_DEFAULT_MEMORY_BLOCKS: ElementId = ElementId::new("default_memory_blocks", 134);
pub const ELEM_DEFAULT_PROTO: ElementId = ElementId::new("default_proto", 135);
pub const ELEM_DEFAULT_SYMBOLS: ElementId = ElementId::new("default_symbols", 136);
pub const ELEM_EVAL_CALLED_PROTOTYPE: ElementId = ElementId::new("eval_called_prototype", 137);
pub const ELEM_EVAL_CURRENT_PROTOTYPE: ElementId = ElementId::new("eval_current_prototype", 138);
pub const ELEM_EXPERIMENTAL_RULES: ElementId = ElementId::new("experimental_rules", 139);
pub const ELEM_FLOWOVERRIDELIST: ElementId = ElementId::new("flowoverridelist", 140);
pub const ELEM_FUNCPTR: ElementId = ElementId::new("funcptr", 141);
pub const ELEM_GLOBAL: ElementId = ElementId::new("global", 142);
pub const ELEM_INCIDENTALCOPY: ElementId = ElementId::new("incidentalcopy", 143);
pub const ELEM_INFERPTRBOUNDS: ElementId = ElementId::new("inferptrbounds", 144);
pub const ELEM_MODELALIAS: ElementId = ElementId::new("modelalias", 145);
pub const ELEM_NOHIGHPTR: ElementId = ElementId::new("nohighptr", 146);
pub const ELEM_PROCESSOR_SPEC: ElementId = ElementId::new("processor_spec", 147);
pub const ELEM_PROGRAMCOUNTER: ElementId = ElementId::new("programcounter", 148);
pub const ELEM_PROPERTIES: ElementId = ElementId::new("properties", 149);
pub const ELEM_PROPERTY: ElementId = ElementId::new("property", 150);
pub const ELEM_READONLY: ElementId = ElementId::new("readonly", 151);
pub const ELEM_REGISTER_DATA: ElementId = ElementId::new("register_data", 152);
pub const ELEM_RULE: ElementId = ElementId::new("rule", 153);
pub const ELEM_SAVE_STATE: ElementId = ElementId::new("save_state", 154);
pub const ELEM_SEGMENTED_ADDRESS: ElementId = ElementId::new("segmented_address", 155);
pub const ELEM_SPACEBASE: ElementId = ElementId::new("spacebase", 156);
pub const ELEM_SPECEXTENSIONS: ElementId = ElementId::new("specextensions", 157);
pub const ELEM_STACKPOINTER: ElementId = ElementId::new("stackpointer", 158);
pub const ELEM_VOLATILE: ElementId = ElementId::new("volatile", 159);

pub type ErrorStream = Arc<Mutex<String>>;

#[derive(Clone, Debug, Default)]
pub struct Statistics {
    pub numfunc: u64,
    pub numvar: u64,
    pub coversum: u64,
    pub coversumsq: u64,
    pub lastcastcount: u64,
    pub castcount: u64,
    pub castcountsq: u64,
}

impl Statistics {
    pub fn new() -> Statistics {
        Statistics {
            numfunc: 0,
            numvar: 0,
            coversum: 0,
            coversumsq: 0,
            lastcastcount: 0,
            castcount: 0,
            castcountsq: 0,
        }
    }

    pub fn process_cast(&mut self, _data: &Funcdata) {
        let perfunc = self.castcount.wrapping_sub(self.lastcastcount);
        self.lastcastcount = self.castcount;
        self.castcountsq = self.castcountsq.wrapping_add(perfunc.wrapping_mul(perfunc));
    }

    pub fn count_cast(&mut self) {
        self.castcount += 1;
    }

    pub fn process(&mut self, fd: &Funcdata) {
        self.numfunc += 1;
        self.process_cast(fd);
    }

    pub fn print_results(&self, out: &mut String) {
        out.push_str(&format!("Number of functions: {}\n", self.numfunc));
        let average = self.castcount as f64 / self.numfunc as f64;
        let mut variance = self.castcountsq as f64 / self.numfunc as f64;
        variance -= average * average;
        let stddev = variance.sqrt();
        out.push_str(&format!("Total functions = {}\n", self.numfunc));
        out.push_str(&format!("Total casts = {}\n", self.castcount));
        out.push_str(&format!(
            "Average casts per function = {}\n",
            format_float_general(average, 6)
        ));
        out.push_str(&format!(
            "        Standard deviation = {}\n",
            format_float_general(stddev, 6)
        ));
    }
}

pub const MAJOR_VERSION: u32 = 6;
pub const MINOR_VERSION: u32 = 2;

pub trait ArchitectureCapability: CapabilityPoint {
    fn get_name(&self) -> &str;

    fn build_architecture(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<Box<Architecture>>;

    fn is_file_match(&self, filename: &str) -> bool;

    fn is_xml_match(&self, doc: &Document) -> bool;
}

static ARCHITECTURE_CAPABILITIES: &[&dyn ArchitectureCapability] = &[];

pub fn architecture_capability_list() -> Vec<&'static dyn ArchitectureCapability> {
    let mut thelist: Vec<&'static dyn ArchitectureCapability> = ARCHITECTURE_CAPABILITIES.to_vec();
    sort_capabilities(&mut thelist);
    thelist
}

pub fn find_capability(filename: &str) -> Option<&'static dyn ArchitectureCapability> {
    architecture_capability_list()
        .into_iter()
        .find(|capa| capa.is_file_match(filename))
}

pub fn find_capability_doc(doc: &Document) -> Option<&'static dyn ArchitectureCapability> {
    architecture_capability_list()
        .into_iter()
        .find(|capa| capa.is_xml_match(doc))
}

pub fn get_capability(name: &str) -> Option<&'static dyn ArchitectureCapability> {
    architecture_capability_list()
        .into_iter()
        .find(|capa| capa.get_name() == name)
}

pub fn sort_capabilities(thelist: &mut Vec<&'static dyn ArchitectureCapability>) {
    let position = match thelist.iter().position(|capa| capa.get_name() == "raw") {
        None => return,
        Some(position) => position,
    };
    let capa = thelist.remove(position);
    thelist.push(capa);
}

pub fn get_major_version() -> u32 {
    MAJOR_VERSION
}

pub fn get_minor_version() -> u32 {
    MINOR_VERSION
}

pub trait ArchitectureBuilder: Send + Sync {
    fn get_description(&self, glb: &Architecture) -> String {
        glb.archid.clone()
    }

    fn print_warning(&self, glb: &Architecture, message: &str);

    fn encode(&self, glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        glb.encode_base(encoder)
    }

    fn restore_xml(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        glb.restore_xml_base(store)
    }

    fn name_function(&self, glb: &Architecture, addr: &Address, name: &mut String) {
        glb.name_function_base(addr, name)
    }

    fn build_database(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<ScopeId> {
        glb.build_database_base(store)
    }

    fn build_translator(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<Box<dyn Translate>>;

    fn build_loader(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_pcode_inject_library(&self, glb: &mut Architecture) -> Result<Box<dyn PcodeInjectLibrary>>;

    fn build_typegrp(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_core_types(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_comment_db(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_string_manager(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_constant_pool(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_instructions(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        glb.build_instructions_base(store)
    }

    fn build_action(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        glb.build_action_base(store)
    }

    fn build_context(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_symbols(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn build_spec_file(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()>;

    fn modify_spaces(&self, glb: &mut Architecture, trans: &mut dyn Translate) -> Result<()>;

    fn post_spec_file(&self, glb: &mut Architecture) -> Result<()> {
        glb.post_spec_file_base()
    }

    fn resolve_architecture(&self, glb: &mut Architecture) -> Result<()>;
}

pub struct Architecture {
    pub manager: Arc<AddrSpaceManager>,
    pub archid: String,
    pub trim_recurse_max: i32,
    pub max_implied_ref: i32,
    pub max_term_duplication: i32,
    pub max_basetype_size: i32,
    pub min_funcsymbol_size: i32,
    pub max_jumptable_size: u32,
    pub aggressive_ext_trim: bool,
    pub readonlypropagate: bool,
    pub infer_pointers: bool,
    pub analyze_for_loops: bool,
    pub nan_ignore_all: bool,
    pub nan_ignore_compare: bool,
    pub infer_ptr_spaces: Vec<SpaceRef>,
    pub funcptr_align: i32,
    pub flowoptions: u32,
    pub max_instructions: u32,
    pub max_baddata: u32,
    pub alias_block_level: i32,
    pub split_datatype_config: u32,
    pub extra_pool_rules: Vec<Box<dyn Rule>>,
    pub symboltab: Option<Box<Database>>,
    pub context: Option<SharedContextDatabase>,
    pub proto_models: Arena<ModelId, ProtoModel>,
    pub proto_model_map: BTreeMap<String, ModelId>,
    pub defaultfp: Option<ModelId>,
    pub default_return_addr: VarnodeData,
    pub evalfp_current: Option<ModelId>,
    pub evalfp_called: Option<ModelId>,
    pub types: Option<Box<TypeFactory>>,
    pub translate: Option<Arc<dyn Translate>>,
    pub loader: Option<SharedLoadImage>,
    pub pcodeinjectlib: Option<Box<dyn PcodeInjectLibrary>>,
    pub commentdb: Option<Box<dyn CommentDatabase>>,
    pub string_manager: Option<Box<dyn StringManager>>,
    pub cpool: Option<Box<dyn ConstantPool>>,
    pub print: usize,
    pub printlist: Vec<Option<Box<dyn PrintLanguage>>>,
    pub options: Option<Box<OptionDatabase>>,
    pub inst: Vec<Option<Box<dyn TypeOp>>>,
    pub userops: UserOpManage,
    pub splitrecords: Vec<PreferSplitRecord>,
    pub lanerecords: Vec<LanedRegister>,
    pub allacts: ActionDatabase,
    pub loadersymbols_parsed: bool,
    pub stats: Option<Box<Statistics>>,
    pub debugstream: Option<ErrorStream>,
    pub builder: Option<Arc<dyn ArchitectureBuilder>>,
    pub segmented_resolvers: BTreeMap<i32, Arc<SegmentedResolver>>,
}

fn missing(what: &str) -> Error {
    Error::Lowlevel(format!("missing {}", what))
}

impl Default for Architecture {
    fn default() -> Architecture {
        Architecture::new()
    }
}

impl Architecture {
    pub fn new() -> Architecture {
        let mut glb = Architecture {
            manager: Arc::new(AddrSpaceManager::new()),
            archid: String::new(),
            trim_recurse_max: 0,
            max_implied_ref: 0,
            max_term_duplication: 0,
            max_basetype_size: 0,
            min_funcsymbol_size: 1,
            max_jumptable_size: 0,
            aggressive_ext_trim: false,
            readonlypropagate: false,
            infer_pointers: false,
            analyze_for_loops: false,
            nan_ignore_all: false,
            nan_ignore_compare: false,
            infer_ptr_spaces: Vec::new(),
            funcptr_align: 0,
            flowoptions: 0,
            max_instructions: 0,
            max_baddata: 0,
            alias_block_level: 0,
            split_datatype_config: 0,
            extra_pool_rules: Vec::new(),
            symboltab: None,
            context: None,
            proto_models: Arena::new(),
            proto_model_map: BTreeMap::new(),
            defaultfp: None,
            default_return_addr: VarnodeData::default(),
            evalfp_current: None,
            evalfp_called: None,
            types: None,
            translate: None,
            loader: None,
            pcodeinjectlib: None,
            commentdb: None,
            string_manager: None,
            cpool: None,
            print: 0,
            printlist: Vec::new(),
            options: Some(Box::new(OptionDatabase::new())),
            inst: Vec::new(),
            userops: UserOpManage::new(),
            splitrecords: Vec::new(),
            lanerecords: Vec::new(),
            allacts: ActionDatabase::new(),
            loadersymbols_parsed: false,
            stats: None,
            debugstream: None,
            builder: None,
            segmented_resolvers: BTreeMap::new(),
        };
        glb.reset_defaults_internal();
        glb.min_funcsymbol_size = 1;
        glb.aggressive_ext_trim = false;
        glb.funcptr_align = 0;
        let capability = get_default_capability().expect("no registered print languages");
        let print = capability.build_language(&mut glb);
        glb.printlist.push(Some(print));
        glb.print = 0;
        glb
    }

    fn require_builder(&self) -> Result<Arc<dyn ArchitectureBuilder>> {
        self.builder
            .clone()
            .ok_or_else(|| Error::Lowlevel("architecture has no builder".to_string()))
    }

    pub fn translator(&self) -> Result<Arc<dyn Translate>> {
        self.translate.clone().ok_or_else(|| missing("translator"))
    }

    pub fn symboltab_ref(&self) -> Result<&Database> {
        self.symboltab.as_deref().ok_or_else(|| missing("symbol table"))
    }

    pub fn symboltab_mut(&mut self) -> Result<&mut Database> {
        self.symboltab.as_deref_mut().ok_or_else(|| missing("symbol table"))
    }

    pub fn types_mut(&mut self) -> Result<&mut TypeFactory> {
        self.types.as_deref_mut().ok_or_else(|| missing("type factory"))
    }

    fn global_scope(&self) -> Result<ScopeId> {
        self.symboltab_ref()?
            .get_global_scope()
            .ok_or_else(|| missing("global scope"))
    }

    pub fn refresh_type_properties(&mut self) {
        let data_space = self.manager.get_default_data_space();
        let max_basetype_size = self.max_basetype_size;
        if let Some(types) = self.types.as_deref_mut() {
            types.set_arch_properties(data_space, max_basetype_size);
        }
    }

    pub fn with_print_language<T>(
        &mut self,
        index: usize,
        body: impl FnOnce(&mut dyn PrintLanguage, &mut Architecture) -> T,
    ) -> T {
        let mut language = self.printlist[index].take().expect("print language is taken out");
        let res = body(language.as_mut(), self);
        self.printlist[index] = Some(language);
        res
    }

    fn new_decoder<'a>(
        manager: &'a AddrSpaceManager,
        trans: Option<&'a dyn Translate>,
        el: Arc<crate::xml::Element>,
    ) -> XmlDecode<'a> {
        let mut decoder = XmlDecode::with_root(Some(manager), el, 0);
        decoder.set_translate(trans);
        decoder
    }

    pub fn init(&mut self, store: &mut DocumentStorage) -> Result<()> {
        let builder = self.require_builder()?;
        builder.build_loader(self, store)?;
        builder.resolve_architecture(self)?;
        builder.build_spec_file(self, store)?;

        builder.build_context(self, store)?;
        builder.build_typegrp(self, store)?;
        self.refresh_type_properties();
        builder.build_comment_db(self, store)?;
        builder.build_string_manager(self, store)?;
        builder.build_constant_pool(self, store)?;
        builder.build_database(self, store)?;

        self.restore_from_spec(store)?;
        builder.build_core_types(self, store)?;
        let print = self.print;
        self.with_print_language(print, |language, glb| language.initialize_from_architecture(glb))?;
        let num_spaces = self.manager.num_spaces();
        self.symboltab_mut()?.adjust_caches(num_spaces);
        builder.build_symbols(self, store)?;
        builder.post_spec_file(self)?;

        builder.build_instructions(self, store)?;
        self.fillin_read_only_from_loader()
    }

    pub fn reset_defaults_internal(&mut self) {
        self.trim_recurse_max = 5;
        self.max_implied_ref = 2;
        self.max_term_duplication = 2;
        self.max_basetype_size = 10;
        self.flowoptions = crate::flow::ERROR_TOOMANYINSTRUCTIONS;
        self.max_instructions = 100000;
        self.max_baddata = 4;
        self.infer_pointers = true;
        self.analyze_for_loops = true;
        self.readonlypropagate = false;
        self.nan_ignore_all = false;
        self.nan_ignore_compare = true;
        self.alias_block_level = 2;
        self.split_datatype_config = OptionSplitDatatypes::OPTION_STRUCT
            | OptionSplitDatatypes::OPTION_ARRAY
            | OptionSplitDatatypes::OPTION_POINTER;
        self.max_jumptable_size = 1024;
        self.refresh_type_properties();
    }

    pub fn reset_defaults(&mut self) -> Result<()> {
        self.reset_defaults_internal();
        self.allacts.reset_defaults()?;
        for language in self.printlist.iter_mut().flatten() {
            language.reset_defaults();
        }
        Ok(())
    }

    pub fn get_model(&self, nm: &str) -> Option<ModelId> {
        self.proto_model_map.get(nm).copied()
    }

    pub fn has_model(&self, nm: &str) -> bool {
        self.proto_model_map.contains_key(nm)
    }

    pub fn create_unknown_model(&mut self, model_name: &str) -> Result<ModelId> {
        let defaultfp = self.defaultfp.ok_or_else(|| missing("default prototype model"))?;
        let id = self.proto_models.next_id();
        let mut model = ProtoModel::new_unknown(id, model_name, &self.proto_models[defaultfp])?;
        if model_name == "unknown" {
            model.set_print_in_decl(false);
        }
        let allocated = self.proto_models.alloc(model);
        self.proto_model_map.insert(model_name.to_string(), allocated);
        Ok(allocated)
    }

    pub fn get_space_by_spacebase(&self, loc: &Address, size: i32) -> Result<SpaceRef> {
        let sz = self.manager.num_spaces();
        for index in 0..sz {
            let id = match self.manager.get_space(index) {
                None => continue,
                Some(id) => id,
            };
            let numspace = id.num_spacebase();
            for slot in 0..numspace {
                let point = id.get_spacebase(slot)?;
                if point.size as i32 != size {
                    continue;
                }
                let point_index = point.space.as_ref().map(|spc| spc.get_index());
                let loc_index = loc.get_space().map(|spc| spc.get_index());
                if point_index != loc_index {
                    continue;
                }
                if point.offset != loc.get_offset() {
                    continue;
                }
                return Ok(id);
            }
        }
        Err(Error::Lowlevel(
            "Unable to find entry for spacebase register".to_string(),
        ))
    }

    pub fn get_laned_register(&self, _loc: &Address, size: i32) -> Option<usize> {
        let mut min: i32 = 0;
        let mut max: i32 = self.lanerecords.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let sz = self.lanerecords[mid as usize].get_whole_size();
            if sz < size {
                min = mid + 1;
            } else if size < sz {
                max = mid - 1;
            } else {
                return Some(mid as usize);
            }
        }
        None
    }

    pub fn get_minimum_laned_register_size(&self) -> i32 {
        match self.lanerecords.first() {
            None => -1,
            Some(record) => record.get_whole_size(),
        }
    }

    pub fn set_default_model(&mut self, model: ModelId) {
        if let Some(defaultfp) = self.defaultfp {
            self.proto_models[defaultfp].set_print_in_decl(true);
        }
        self.proto_models[model].set_print_in_decl(false);
        self.defaultfp = Some(model);
    }

    pub fn clear_analysis(&mut self, fd: &mut Funcdata) {
        fd.clear(self).expect("function analysis state could not be cleared");
        let addr = fd.get_address().clone();
        if let Some(commentdb) = self.commentdb.as_deref_mut() {
            commentdb.clear_type(&addr, Comment::WARNING | Comment::WARNINGHEADER);
        }
    }

    pub fn read_loader_symbols(&mut self) -> Result<()> {
        if self.loadersymbols_parsed {
            return Ok(());
        }
        let loader = self.loader.clone().ok_or_else(|| missing("load image"))?;
        loader.open_symbols();
        self.loadersymbols_parsed = true;
        let mut record = LoadImageFunc::default();
        while loader.get_next_symbol(&mut record) {
            let mut basename = String::new();
            let delim = self.get_scope_delimiter();
            let num_spaces = self.manager.num_spaces();
            let scope = self.symboltab_mut()?.find_create_scope_from_symbol_name(
                &record.name,
                &delim,
                &mut basename,
                None,
                num_spaces,
            )?;
            Database::scope_add_function(self, scope, &record.address, &basename)?;
        }
        loader.close_symbols();
        Ok(())
    }

    pub fn collect_behaviors(&self) -> Vec<Option<OpBehaviorRef>> {
        self.inst
            .iter()
            .map(|slot| slot.as_ref().and_then(|op| op.base().behave.clone()))
            .collect()
    }

    pub fn get_segment_op(&self, spc: &AddrSpace) -> Option<Arc<UserPcodeOp>> {
        if spc.get_index() >= self.userops.num_segment_ops() {
            return None;
        }
        let segdef = self.userops.get_segment_op(spc.get_index())?;
        let segment = segdef.as_segment()?;
        if segment.get_resolve().space.is_some() {
            return Some(segdef.clone());
        }
        None
    }

    pub fn set_prototype(&mut self, pieces: &PrototypePieces) -> Result<()> {
        let mut basename = String::new();
        let delim = self.get_scope_delimiter();
        let scope = self
            .symboltab_ref()?
            .resolve_scope_from_symbol_name(&pieces.name, &delim, &mut basename, None)
            .ok_or_else(|| Error::Parse(format!("Unknown namespace: {}", pieces.name)))?;
        let sym = self
            .symboltab_ref()?
            .scope_query_function_by_name(scope, &basename)
            .ok_or_else(|| Error::Parse(format!("Unknown function name: {}", pieces.name)))?;
        let mut proto = match Database::symbol_get_function(self, sym)? {
            None => return Err(Error::Parse(format!("Unknown function name: {}", pieces.name))),
            Some(fd) => std::mem::take(fd.get_func_proto_mut()),
        };
        let res = proto.set_pieces(pieces, self);
        if let Some(fd) = Database::symbol_get_function(self, sym)? {
            *fd.get_func_proto_mut() = proto;
        }
        res
    }

    pub fn set_print_language(&mut self, nm: &str) -> Result<()> {
        let current = self.print;
        for index in 0..self.printlist.len() {
            let matches = match self.printlist[index].as_deref() {
                None => false,
                Some(language) => language.get_name() == nm,
            };
            if matches {
                if index != current {
                    let stream = self.with_print_language(current, |language, _glb| language.take_output_stream());
                    self.with_print_language(index, |language, _glb| language.set_output_stream(stream));
                }
                self.print = index;
                self.with_print_language(index, |language, glb| language.adjust_type_operators(glb));
                return Ok(());
            }
        }
        let capa =
            find_print_capability(nm).ok_or_else(|| Error::Lowlevel(format!("Unknown print language: {}", nm)))?;
        let (print_markup, stream) = self.with_print_language(current, |language, _glb| {
            (language.emits_markup(), language.take_output_stream())
        });
        let mut language = capa.build_language(self);
        language.set_output_stream(stream);
        language.initialize_from_architecture(self)?;
        if print_markup {
            language.set_markup(true);
        }
        self.printlist.push(Some(language));
        self.print = self.printlist.len() - 1;
        let index = self.print;
        self.with_print_language(index, |language, glb| language.adjust_type_operators(glb));
        Ok(())
    }

    pub fn globalify(&mut self) -> Result<()> {
        let scope = self.global_scope()?;
        let nm = self.manager.num_spaces();
        for index in 0..nm {
            let spc = match self.manager.get_space(index) {
                None => continue,
                Some(spc) => spc,
            };
            if spc.get_type() != SpaceType::Processor && spc.get_type() != SpaceType::Spacebase {
                continue;
            }
            let highest = spc.get_highest();
            self.symboltab_mut()?.add_range(scope, &spc, 0, highest);
        }
        Ok(())
    }

    fn global_function(&mut self, funcaddr: &Address) -> Result<Option<&mut Funcdata>> {
        let scope = self.global_scope()?;
        let sym = self.symboltab_ref()?.scope_query_function(scope, funcaddr);
        match sym {
            None => Ok(None),
            Some(sym) => Database::symbol_get_function(self, sym),
        }
    }

    pub fn decode_flow_override(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_FLOWOVERRIDELIST)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == ELEM_FLOW {
                let flow_type = decoder.read_string_attr(ATTRIB_TYPE)?;
                let funcaddr = Address::decode(decoder)?;
                let overaddr = Address::decode(decoder)?;
                if let Some(fd) = self.global_function(&funcaddr)? {
                    fd.get_override().insert_flow_override(&overaddr, &flow_type)?;
                }
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_CALLDEST {
                let flow_type = decoder.read_string_attr(ATTRIB_TYPE)?;
                let funcaddr = Address::decode(decoder)?;
                let overaddr = Address::decode(decoder)?;
                let destaddr = Address::decode(decoder)?;
                if let Some(fd) = self.global_function(&funcaddr)? {
                    fd.get_override()
                        .insert_destination_override(&overaddr, &destaddr, &flow_type)?;
                }
                decoder.close_element(sub_id)?;
            } else {
                break;
            }
        }
        decoder.close_element(elem_id)
    }

    pub fn get_description(&self) -> String {
        match &self.builder {
            Some(builder) => builder.get_description(self),
            None => self.archid.clone(),
        }
    }

    pub fn print_warning(&self, message: &str) {
        if let Some(builder) = &self.builder {
            builder.print_warning(self, message);
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        match self.builder.clone() {
            Some(builder) => builder.encode(self, encoder),
            None => self.encode_base(encoder),
        }
    }

    pub fn encode_base(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_SAVE_STATE);
        encoder.write_bool(ATTRIB_LOADERSYMBOLS, self.loadersymbols_parsed);
        let types = self.types.as_deref().ok_or_else(|| missing("type factory"))?;
        types.encode(encoder, self)?;
        Database::encode(self, encoder)?;
        self.context
            .as_ref()
            .ok_or_else(|| missing("context database"))?
            .lock()
            .expect("context database lock is poisoned")
            .encode(encoder)?;
        self.commentdb
            .as_deref()
            .ok_or_else(|| missing("comment database"))?
            .encode(encoder)?;
        self.string_manager
            .as_deref()
            .ok_or_else(|| missing("string manager"))?
            .encode(encoder)?;
        let cpool = self.cpool.as_deref().ok_or_else(|| missing("constant pool"))?;
        if !cpool.empty() {
            cpool.encode(encoder, self)?;
        }
        encoder.close_element(ELEM_SAVE_STATE);
        Ok(())
    }

    pub fn restore_xml(&mut self, store: &mut DocumentStorage) -> Result<()> {
        match self.builder.clone() {
            Some(builder) => builder.restore_xml(self, store),
            None => self.restore_xml_base(store),
        }
    }

    pub fn restore_xml_base(&mut self, store: &mut DocumentStorage) -> Result<()> {
        let el = store
            .get_tag(ELEM_SAVE_STATE.get_name())
            .ok_or_else(|| Error::Lowlevel("Could not find save_state tag".to_string()))?;
        let manager = self.manager.clone();
        let trans = self.translate.clone();
        let mut decoder = Architecture::new_decoder(&manager, trans.as_deref(), el);
        let elem_id = decoder.open_element_expect(ELEM_SAVE_STATE)?;
        self.loadersymbols_parsed = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_LOADERSYMBOLS {
                self.loadersymbols_parsed = decoder.read_bool()?;
            }
        }

        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_TYPEGRP {
                TypeFactory::decode(self, &mut decoder)?;
            } else if sub_id == ELEM_DB {
                Database::decode(self, &mut decoder)?;
            } else if sub_id == ELEM_CONTEXT_POINTS {
                self.context
                    .as_ref()
                    .ok_or_else(|| missing("context database"))?
                    .lock()
                    .expect("context database lock is poisoned")
                    .decode(&mut decoder)?;
            } else if sub_id == ELEM_COMMENTDB {
                self.commentdb
                    .as_deref_mut()
                    .ok_or_else(|| missing("comment database"))?
                    .decode(&mut decoder)?;
            } else if sub_id == ELEM_STRINGMANAGE {
                self.string_manager
                    .as_deref_mut()
                    .ok_or_else(|| missing("string manager"))?
                    .decode(&mut decoder)?;
            } else if sub_id == ELEM_CONSTANTPOOL {
                let mut cpool = self.cpool.take().ok_or_else(|| missing("constant pool"))?;
                let outcome = cpool.decode(&mut decoder, self);
                self.cpool = Some(cpool);
                outcome?;
            } else if sub_id == ELEM_OPTIONSLIST {
                OptionDatabase::decode(self, &mut decoder)?;
            } else if sub_id == ELEM_FLOWOVERRIDELIST {
                self.decode_flow_override(&mut decoder)?;
            } else if sub_id == ELEM_INJECTDEBUG {
                self.pcodeinjectlib
                    .as_deref_mut()
                    .ok_or_else(|| missing("p-code inject library"))?
                    .decode_debug(&mut decoder)?;
            } else {
                return Err(Error::Lowlevel("XML error restoring architecture".to_string()));
            }
        }
        decoder.close_element(elem_id)
    }

    pub fn name_function(&self, addr: &Address, name: &mut String) {
        match &self.builder {
            Some(builder) => builder.name_function(self, addr, name),
            None => self.name_function_base(addr, name),
        }
    }

    pub fn name_function_base(&self, addr: &Address, name: &mut String) {
        let mut defname = "func_".to_string();
        addr.print_raw(&mut defname);
        *name = defname;
    }

    pub fn get_scope_delimiter(&self) -> String {
        self.printlist[self.print]
            .as_deref()
            .expect("current print language is taken out")
            .get_scope_delimiter()
    }

    pub fn set_debug_stream(&mut self, stream: Option<ErrorStream>) {
        self.debugstream = stream;
    }

    pub fn print_debug(&self, message: &str) {
        let stream = self.debugstream.as_ref().expect("missing debug stream");
        let mut out = stream.lock().expect("poisoned output stream lock");
        out.push_str(message);
        out.push('\n');
    }

    pub fn resolve_constant(
        &mut self,
        spc: &SpaceRef,
        val: u64,
        sz: i32,
        point: &Address,
        full_encoding: &mut u64,
    ) -> Result<Address> {
        if let Some(resolver) = self.segmented_resolvers.get(&spc.get_index()).cloned() {
            return resolver.resolve_with(self, val, sz, point, full_encoding);
        }
        Ok(self.manager.resolve_constant(spc, val, sz, point, full_encoding))
    }

    #[allow(clippy::too_many_arguments)]
    pub fn add_spacebase(
        &mut self,
        basespace: &SpaceRef,
        nm: &str,
        ptrdata: &VarnodeData,
        trunc_size: i32,
        isreversejustified: bool,
        stack_growth: bool,
        is_formal: bool,
    ) -> Result<()> {
        let ind = self.manager.num_spaces();
        let big_endian = self.translator()?.is_big_endian();
        let delay = ptrdata.space.as_ref().map_or(0, |spc| spc.get_delay());
        let spc = AddrSpace::new_spacebase(nm, big_endian, ind, trunc_size as u32, basespace, delay + 1, is_formal);
        if isreversejustified {
            self.manager.set_reverse_justified(&spc);
        }
        let spc = Arc::new(spc);
        self.manager.insert_space(spc.clone())?;
        self.manager
            .add_spacebase_pointer(&spc, ptrdata, trunc_size, stack_growth)
    }

    pub fn build_database_base(&mut self, _store: &mut DocumentStorage) -> Result<ScopeId> {
        let mut symboltab = Database::new(true);
        let num_spaces = self.manager.num_spaces();
        let globscope = symboltab.scopes.alloc(Scope::new_internal(0, "", num_spaces));
        symboltab.attach_scope(globscope, None)?;
        self.symboltab = Some(Box::new(symboltab));
        Ok(globscope)
    }

    pub fn build_instructions_base(&mut self, _store: &mut DocumentStorage) -> Result<()> {
        let trans = self.translator()?;
        let types = self.types.as_deref().ok_or_else(|| missing("type factory"))?;
        crate::typeop::register_instructions(&mut self.inst, types, trans.as_ref());
        Ok(())
    }

    pub fn build_action_base(&mut self, store: &mut DocumentStorage) -> Result<()> {
        self.parse_extra_rules(store)?;
        let mut allacts = std::mem::take(&mut self.allacts);
        allacts.universal_action(self);
        let res = allacts.reset_defaults();
        self.allacts = allacts;
        res
    }

    pub fn post_spec_file_base(&mut self) -> Result<()> {
        self.cache_addr_space_properties();
        Ok(())
    }

    pub fn restore_from_spec(&mut self, store: &mut DocumentStorage) -> Result<()> {
        let builder = self.require_builder()?;
        let mut utrans = builder.build_translator(self, store)?;
        utrans.initialize(store)?;
        builder.modify_spaces(self, utrans.as_mut())?;
        self.manager.copy_spaces(utrans.manager())?;
        utrans.set_default_float_formats();
        let trans: Arc<dyn Translate> = Arc::from(utrans);
        self.translate = Some(trans.clone());
        self.refresh_type_properties();
        let fspec_index = self.manager.num_spaces();
        self.manager.insert_space(Arc::new(AddrSpace::new_fspec(fspec_index)))?;
        let iop_index = self.manager.num_spaces();
        self.manager.insert_space(Arc::new(AddrSpace::new_iop(iop_index)))?;
        let join_index = self.manager.num_spaces();
        let join = AddrSpace::new_join(&self.manager, trans.is_big_endian(), join_index);
        self.manager.insert_space(Arc::new(join))?;
        UserOpManage::initialize(self)?;
        if trans.get_alignment() <= 8 {
            self.min_funcsymbol_size = trans.get_alignment();
        }
        self.pcodeinjectlib = Some(builder.build_pcode_inject_library(self)?);
        self.parse_processor_config(store)?;
        self.parse_compiler_config(store)?;
        builder.build_action(self, store)
    }

    pub fn fillin_read_only_from_loader(&mut self) -> Result<()> {
        let loader = self.loader.clone().ok_or_else(|| missing("load image"))?;
        let mut rangelist = RangeList::new();
        loader.get_readonly(&mut rangelist);
        let manager = self.manager.clone();
        let symboltab = self.symboltab_mut()?;
        for range in rangelist.iter() {
            symboltab.set_property_range(Varnode::READONLY, range, &manager);
        }
        Ok(())
    }

    pub fn initialize_segments(&mut self) -> Result<()> {
        let sz = self.userops.num_segment_ops();
        for index in 0..sz {
            let sop = match self.userops.get_segment_op(index) {
                None => continue,
                Some(sop) => sop.clone(),
            };
            let spc = sop
                .as_segment()
                .and_then(|segment| segment.get_space().cloned())
                .ok_or_else(|| missing("segment op space"))?;
            let rsolv = Arc::new(SegmentedResolver::new(spc.clone(), sop));
            self.manager.insert_resolver(&spc, rsolv.clone());
            self.segmented_resolvers.insert(spc.get_index(), rsolv);
        }
        Ok(())
    }

    pub fn cache_addr_space_properties(&mut self) {
        let mut copy_list: Vec<SpaceRef> = self.infer_ptr_spaces.clone();
        if let Some(spc) = self.manager.get_default_code_space() {
            copy_list.push(spc);
        }
        if let Some(spc) = self.manager.get_default_data_space() {
            copy_list.push(spc);
        }
        self.infer_ptr_spaces.clear();
        copy_list.sort_by_key(|spc| spc.get_index());
        let mut last_index: Option<i32> = None;
        for spc in copy_list {
            if last_index == Some(spc.get_index()) {
                continue;
            }
            last_index = Some(spc.get_index());
            if spc.no_high_ptr_possible() {
                continue;
            }
            if spc.get_type() == SpaceType::Spacebase {
                continue;
            }
            if spc.is_other_space() {
                continue;
            }
            if spc.is_overlay() {
                continue;
            }
            self.infer_ptr_spaces.push(spc);
        }

        let data_index = self.manager.get_default_data_space().map(|spc| spc.get_index());
        let mut def_pos: i32 = -1;
        for index in 0..self.infer_ptr_spaces.len() {
            let spc = self.infer_ptr_spaces[index].clone();
            if Some(spc.get_index()) == data_index {
                def_pos = index as i32;
            }
            if let Some(seg_op) = self.get_segment_op(&spc) {
                let val = seg_op.as_segment().map_or(0, |segment| segment.get_inner_size());
                self.manager.mark_near_pointers(&spc, val);
            }
        }
        if def_pos > 0 {
            self.infer_ptr_spaces.swap(0, def_pos as usize);
        }
    }

    pub fn create_model_alias(&mut self, alias_name: &str, parent_name: &str) -> Result<()> {
        let parent = self
            .proto_model_map
            .get(parent_name)
            .copied()
            .ok_or_else(|| Error::Lowlevel(format!("Requesting non-existent prototype model: {}", parent_name)))?;
        let model = &self.proto_models[parent];
        if model.is_merged() {
            return Err(Error::Lowlevel(format!(
                "Cannot make alias of merged model: {}",
                parent_name
            )));
        }
        if model.get_alias_parent().is_some() {
            return Err(Error::Lowlevel(format!(
                "Cannot make alias of an alias: {}",
                parent_name
            )));
        }
        if self.proto_model_map.contains_key(alias_name) {
            return Err(Error::Lowlevel(format!("Duplicate ProtoModel name: {}", alias_name)));
        }
        let id = self.proto_models.next_id();
        let alias = ProtoModel::new_copy(id, alias_name, &self.proto_models[parent])?;
        let allocated = self.proto_models.alloc(alias);
        self.proto_model_map.insert(alias_name.to_string(), allocated);
        Ok(())
    }

    pub fn parse_processor_config(&mut self, store: &mut DocumentStorage) -> Result<()> {
        let el = store
            .get_tag("processor_spec")
            .ok_or_else(|| Error::Lowlevel("No processor configuration tag found".to_string()))?;
        let manager = self.manager.clone();
        let trans = self.translate.clone();
        let mut decoder = Architecture::new_decoder(&manager, trans.as_deref(), el);

        let elem_id = decoder.open_element_expect(ELEM_PROCESSOR_SPEC)?;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_PROGRAMCOUNTER {
                decoder.open_element()?;
                decoder.close_element_skipping(sub_id)?;
            } else if sub_id == ELEM_VOLATILE {
                self.decode_volatile(&mut decoder)?;
            } else if sub_id == ELEM_INCIDENTALCOPY {
                self.decode_incidental_copy(&mut decoder)?;
            } else if sub_id == ELEM_CONTEXT_DATA {
                self.context
                    .as_ref()
                    .ok_or_else(|| missing("context database"))?
                    .lock()
                    .expect("context database lock is poisoned")
                    .decode_from_spec(&mut decoder)?;
            } else if sub_id == ELEM_JUMPASSIST {
                UserOpManage::decode_jump_assist(&mut decoder, self)?;
            } else if sub_id == ELEM_SEGMENTOP {
                UserOpManage::decode_segment_op(&mut decoder, self)?;
            } else if sub_id == ELEM_REGISTER_DATA {
                self.decode_register_data(&mut decoder)?;
            } else if sub_id == ELEM_DATA_SPACE {
                let data_elem = decoder.open_element()?;
                let spc = decoder.read_space_attr(ATTRIB_SPACE)?;
                decoder.close_element(data_elem)?;
                self.manager.set_default_data_space(spc.get_index())?;
                self.refresh_type_properties();
            } else if sub_id == ELEM_INFERPTRBOUNDS {
                self.decode_infer_ptr_bounds(&mut decoder)?;
            } else if sub_id == ELEM_SEGMENTED_ADDRESS {
                decoder.open_element()?;
                decoder.close_element_skipping(sub_id)?;
            } else if sub_id == ELEM_DEFAULT_SYMBOLS {
                decoder.open_element()?;
                if let Some(current) = decoder.get_current_xml_element().cloned() {
                    store.register_tag(&current);
                }
                decoder.close_element_skipping(sub_id)?;
            } else if sub_id == ELEM_DEFAULT_MEMORY_BLOCKS
                || sub_id == ELEM_ADDRESS_SHIFT_AMOUNT
                || sub_id == ELEM_PROPERTIES
            {
                decoder.open_element()?;
                decoder.close_element_skipping(sub_id)?;
            } else {
                return Err(Error::Lowlevel("Unknown element in <processor_spec>".to_string()));
            }
        }
        decoder.close_element(elem_id)
    }

    pub fn parse_compiler_config(&mut self, store: &mut DocumentStorage) -> Result<()> {
        let mut global_ranges: Vec<RangeProperties> = Vec::new();
        let el = store
            .get_tag("compiler_spec")
            .ok_or_else(|| Error::Lowlevel("No compiler configuration tag found".to_string()))?;
        let manager = self.manager.clone();
        let trans = self.translate.clone();
        let mut decoder = Architecture::new_decoder(&manager, trans.as_deref(), el);

        let elem_id = decoder.open_element_expect(ELEM_COMPILER_SPEC)?;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_DEFAULT_PROTO {
                self.decode_default_proto(&mut decoder)?;
            } else if sub_id == ELEM_PROTOTYPE {
                self.decode_proto(&mut decoder)?;
            } else if sub_id == ELEM_STACKPOINTER {
                self.decode_stack_pointer(&mut decoder)?;
            } else if sub_id == ELEM_RETURNADDRESS {
                self.decode_return_address(&mut decoder)?;
            } else if sub_id == ELEM_SPACEBASE {
                self.decode_spacebase(&mut decoder)?;
            } else if sub_id == ELEM_NOHIGHPTR {
                self.decode_no_high_ptr(&mut decoder)?;
            } else if sub_id == ELEM_PREFERSPLIT {
                self.decode_prefer_split(&mut decoder)?;
            } else if sub_id == ELEM_AGGRESSIVETRIM {
                self.decode_aggressive_trim(&mut decoder)?;
            } else if sub_id == ELEM_DATA_ORGANIZATION {
                self.types_mut()?.decode_data_organization(&mut decoder)?;
            } else if sub_id == ELEM_ENUM {
                self.types_mut()?.parse_enum_config(&mut decoder)?;
            } else if sub_id == ELEM_GLOBAL {
                self.decode_global(&mut decoder, &mut global_ranges)?;
            } else if sub_id == ELEM_SEGMENTOP {
                UserOpManage::decode_segment_op(&mut decoder, self)?;
            } else if sub_id == ELEM_READONLY {
                self.decode_read_only(&mut decoder)?;
            } else if sub_id == ELEM_CONTEXT_DATA {
                self.context
                    .as_ref()
                    .ok_or_else(|| missing("context database"))?
                    .lock()
                    .expect("context database lock is poisoned")
                    .decode_from_spec(&mut decoder)?;
            } else if sub_id == ELEM_RESOLVEPROTOTYPE {
                self.decode_proto(&mut decoder)?;
            } else if sub_id == ELEM_EVAL_CALLED_PROTOTYPE || sub_id == ELEM_EVAL_CURRENT_PROTOTYPE {
                self.decode_proto_eval(&mut decoder)?;
            } else if sub_id == ELEM_CALLFIXUP {
                let source = format!("{} : compiler spec", self.archid);
                crate::pcodeinject::decode_inject_in(self, &source, "", CALLFIXUP_TYPE, &mut decoder)?;
            } else if sub_id == ELEM_CALLOTHERFIXUP {
                UserOpManage::decode_call_other_fixup(&mut decoder, self)?;
            } else if sub_id == ELEM_FUNCPTR {
                self.decode_func_ptr_align(&mut decoder)?;
            } else if sub_id == ELEM_DEADCODEDELAY {
                self.decode_deadcode_delay(&mut decoder)?;
            } else if sub_id == ELEM_INFERPTRBOUNDS {
                self.decode_infer_ptr_bounds(&mut decoder)?;
            } else if sub_id == ELEM_MODELALIAS {
                let alias_elem = decoder.open_element()?;
                let alias_name = decoder.read_string_attr(ATTRIB_NAME)?;
                let parent_name = decoder.read_string_attr(ATTRIB_PARENT)?;
                decoder.close_element(alias_elem)?;
                self.create_model_alias(&alias_name, &parent_name)?;
            } else {
                decoder.open_element()?;
                decoder.close_element_skipping(sub_id)?;
            }
        }
        decoder.close_element(elem_id)?;

        if let Some(ext) = store.get_tag("specextensions") {
            let mut decoder_ext = Architecture::new_decoder(&manager, trans.as_deref(), ext);
            let ext_id = decoder_ext.open_element_expect(ELEM_SPECEXTENSIONS)?;
            loop {
                let sub_id = decoder_ext.peek_element()?;
                if sub_id == 0 {
                    break;
                }
                if sub_id == ELEM_PROTOTYPE {
                    self.decode_proto(&mut decoder_ext)?;
                } else if sub_id == ELEM_CALLFIXUP {
                    let source = format!("{} : compiler spec", self.archid);
                    crate::pcodeinject::decode_inject_in(self, &source, "", CALLFIXUP_TYPE, &mut decoder)?;
                } else if sub_id == ELEM_CALLOTHERFIXUP {
                    UserOpManage::decode_call_other_fixup(&mut decoder, self)?;
                } else if sub_id == ELEM_GLOBAL {
                    self.decode_global(&mut decoder, &mut global_ranges)?;
                } else {
                    decoder_ext.open_element()?;
                    decoder_ext.close_element_skipping(sub_id)?;
                }
            }
            decoder_ext.close_element(ext_id)?;
        }

        for props in global_ranges.iter() {
            self.add_to_global_scope(props)?;
        }

        self.add_other_space()?;

        if self.defaultfp.is_none() {
            match self.proto_model_map.values().next().copied() {
                Some(model) => self.set_default_model(model),
                None => return Err(Error::Lowlevel("No default prototype specified".to_string())),
            }
        }
        if !self.proto_model_map.contains_key("__thiscall") {
            let defaultfp = self.defaultfp.expect("default prototype model is set");
            let default_name = self.proto_models[defaultfp].get_name().to_string();
            self.create_model_alias("__thiscall", &default_name)?;
        }
        self.initialize_segments()?;
        PreferSplitManager::initialize(&mut self.splitrecords);
        TypeFactory::setup_sizes(self)?;
        Ok(())
    }

    pub fn parse_extra_rules(&mut self, store: &mut DocumentStorage) -> Result<()> {
        if let Some(expertag) = store.get_tag("experimental_rules") {
            let manager = self.manager.clone();
            let trans = self.translate.clone();
            let mut decoder = Architecture::new_decoder(&manager, trans.as_deref(), expertag);
            let elem_id = decoder.open_element_expect(ELEM_EXPERIMENTAL_RULES)?;
            while decoder.peek_element()? != 0 {
                self.decode_dynamic_rule(&mut decoder)?;
            }
            decoder.close_element(elem_id)?;
        }
        Ok(())
    }

    pub fn decode_dynamic_rule(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let _elem_id = decoder.open_element_expect(ELEM_RULE)?;
        let mut rulename = String::new();
        let mut groupname = String::new();
        let mut enabled = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_NAME {
                rulename = decoder.read_string()?;
            } else if attrib_id == ATTRIB_GROUP {
                groupname = decoder.read_string()?;
            } else if attrib_id == ATTRIB_ENABLE {
                enabled = decoder.read_bool()?;
            } else {
                return Err(Error::Lowlevel(
                    "Dynamic rule tag contains illegal attribute".to_string(),
                ));
            }
        }
        if rulename.is_empty() {
            return Err(Error::Lowlevel("Dynamic rule has no name".to_string()));
        }
        if groupname.is_empty() {
            return Err(Error::Lowlevel("Dynamic rule has no group".to_string()));
        }
        if !enabled {
            return Ok(());
        }
        Err(Error::Lowlevel(
            "Dynamic rules have not been enabled for this decompiler".to_string(),
        ))
    }

    pub fn decode_proto(&mut self, decoder: &mut dyn Decoder) -> Result<ModelId> {
        let elem_id = decoder.peek_element()?;
        let id = self.proto_models.next_id();
        let mut model = if elem_id == ELEM_PROTOTYPE {
            ProtoModel::new(id, &self.manager)
        } else if elem_id == ELEM_RESOLVEPROTOTYPE {
            ProtoModel::new_merged(id, &self.manager)
        } else {
            return Err(Error::Lowlevel(
                "Expecting <prototype> or <resolveprototype> tag".to_string(),
            ));
        };

        model.decode(decoder, self)?;

        let name = model.get_name().to_string();
        if self.get_model(&name).is_some() {
            return Err(Error::Lowlevel(format!("Duplicate ProtoModel name: {}", name)));
        }
        let res = self.proto_models.alloc(model);
        self.proto_model_map.insert(name, res);
        Ok(res)
    }

    pub fn decode_proto_eval(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element()?;
        let model_name = decoder.read_string_attr(ATTRIB_NAME)?;
        let res = self
            .get_model(&model_name)
            .ok_or_else(|| Error::Lowlevel(format!("Unknown prototype model name: {}", model_name)))?;

        if elem_id == ELEM_EVAL_CALLED_PROTOTYPE {
            if self.evalfp_called.is_some() {
                return Err(Error::Lowlevel("Duplicate <eval_called_prototype> tag".to_string()));
            }
            self.evalfp_called = Some(res);
        } else {
            if self.evalfp_current.is_some() {
                return Err(Error::Lowlevel("Duplicate <eval_current_prototype> tag".to_string()));
            }
            self.evalfp_current = Some(res);
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_default_proto(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_DEFAULT_PROTO)?;
        while decoder.peek_element()? != 0 {
            if self.defaultfp.is_some() {
                return Err(Error::Lowlevel("More than one default prototype model".to_string()));
            }
            let model = self.decode_proto(decoder)?;
            self.set_default_model(model);
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_global(&mut self, decoder: &mut dyn Decoder, range_props: &mut Vec<RangeProperties>) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_GLOBAL)?;
        while decoder.peek_element()? != 0 {
            range_props.push(RangeProperties::new());
            range_props
                .last_mut()
                .expect("range properties were pushed")
                .decode(decoder)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn add_to_global_scope(&mut self, props: &RangeProperties) -> Result<()> {
        let scope = self.global_scope()?;
        let trans = self.translate.clone();
        let range = Range::from_properties(props, &self.manager, trans.as_deref())?;
        let spc = range.get_space().clone();
        self.infer_ptr_spaces.push(spc.clone());
        self.symboltab_mut()?
            .add_range(scope, &spc, range.get_first(), range.get_last());
        if spc.is_overlay_base() {
            let num = self.manager.num_spaces();
            for index in 0..num {
                let ospc = match self.manager.get_space(index) {
                    None => continue,
                    Some(ospc) => ospc,
                };
                if !ospc.is_overlay() {
                    continue;
                }
                if ospc.get_contain().map(|contain| contain.get_index()) != Some(spc.get_index()) {
                    continue;
                }
                self.symboltab_mut()?
                    .add_range(scope, &ospc, range.get_first(), range.get_last());
            }
        }
        Ok(())
    }

    pub fn add_other_space(&mut self) -> Result<()> {
        let scope = self.global_scope()?;
        let other_space = self
            .manager
            .get_space_by_name(OTHER_SPACE_NAME)
            .ok_or_else(|| missing("OTHER space"))?;
        let highest = other_space.get_highest();
        self.symboltab_mut()?.add_range(scope, &other_space, 0, highest);
        if other_space.is_overlay_base() {
            let num = self.manager.num_spaces();
            for index in 0..num {
                let ospc = match self.manager.get_space(index) {
                    None => continue,
                    Some(ospc) => ospc,
                };
                if !ospc.is_overlay() {
                    continue;
                }
                if ospc.get_contain().map(|contain| contain.get_index()) != Some(other_space.get_index()) {
                    continue;
                }
                self.symboltab_mut()?.add_range(scope, &ospc, 0, highest);
            }
        }
        Ok(())
    }

    fn set_property_range(&mut self, flags: u32, range: &Range) -> Result<()> {
        let manager = self.manager.clone();
        self.symboltab_mut()?.set_property_range(flags, range, &manager);
        Ok(())
    }

    pub fn decode_read_only(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_READONLY)?;
        while decoder.peek_element()? != 0 {
            let range = Range::decode(decoder)?;
            self.set_property_range(Varnode::READONLY, &range)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_volatile(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_VOLATILE)?;
        UserOpManage::decode_volatile(decoder, self)?;
        while decoder.peek_element()? != 0 {
            let range = Range::decode(decoder)?;
            self.set_property_range(Varnode::VOLATIL, &range)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_return_address(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_RETURNADDRESS)?;
        let sub_id = decoder.peek_element()?;
        if sub_id != 0 {
            if self.default_return_addr.space.is_some() {
                return Err(Error::Lowlevel("Multiple <returnaddress> tags in .cspec".to_string()));
            }
            self.default_return_addr = VarnodeData::decode(decoder)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_incidental_copy(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_INCIDENTALCOPY)?;
        while decoder.peek_element()? != 0 {
            let vdata = VarnodeData::decode(decoder)?;
            let spc = vdata.space.clone().ok_or_else(|| missing("varnode space"))?;
            let range = Range::new(
                spc,
                vdata.offset,
                vdata.offset.wrapping_add(vdata.size as u64).wrapping_sub(1),
            );
            self.set_property_range(Varnode::INCIDENTAL_COPY, &range)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_register_data(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let mut mask_list: Vec<u32> = Vec::new();

        let elem_id = decoder.open_element_expect(ELEM_REGISTER_DATA)?;
        while decoder.peek_element()? != 0 {
            let sub_id = decoder.open_element_expect(crate::address::ELEM_REGISTER)?;
            let mut is_volatile = false;
            let mut lane_sizes = String::new();
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_VECTOR_LANE_SIZES {
                    lane_sizes = decoder.read_string()?;
                } else if attrib_id == crate::database::ATTRIB_VOLATILE {
                    is_volatile = decoder.read_bool()?;
                }
            }
            if !lane_sizes.is_empty() || is_volatile {
                decoder.rewind_attributes();
                let storage = VarnodeData::decode_from_attributes(decoder)?;
                if !lane_sizes.is_empty() {
                    let mut laned_register = LanedRegister::new();
                    laned_register.parse_sizes(storage.size as i32, &lane_sizes)?;
                    let size_index = laned_register.get_whole_size() as usize;
                    while mask_list.len() <= size_index {
                        mask_list.push(0);
                    }
                    mask_list[size_index] |= laned_register.get_size_bit_mask();
                }
                if is_volatile {
                    let spc = storage.space.clone().ok_or_else(|| missing("register space"))?;
                    let range = Range::new(
                        spc,
                        storage.offset,
                        storage.offset.wrapping_add(storage.size as u64).wrapping_sub(1),
                    );
                    self.set_property_range(Varnode::VOLATIL, &range)?;
                }
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)?;
        self.lanerecords.clear();
        for (index, mask) in mask_list.iter().enumerate() {
            if *mask == 0 {
                continue;
            }
            self.lanerecords.push(LanedRegister::with_mask(index as i32, *mask));
        }
        Ok(())
    }

    pub fn decode_stack_pointer(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_STACKPOINTER)?;

        let mut register_name = String::new();
        let mut stack_growth = true;
        let mut isreversejustify = false;
        let mut basespace: Option<SpaceRef> = None;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_REVERSEJUSTIFY {
                isreversejustify = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_GROWTH {
                stack_growth = decoder.read_string()? == "negative";
            } else if attrib_id == ATTRIB_SPACE {
                basespace = Some(decoder.read_space()?);
            } else if attrib_id == ATTRIB_REGISTER {
                register_name = decoder.read_string()?;
            }
        }

        let basespace = basespace.ok_or_else(|| {
            Error::Lowlevel(format!(
                "{} element missing \"space\" attribute",
                ELEM_STACKPOINTER.get_name()
            ))
        })?;

        let point = self.translator()?.get_register(&register_name)?;
        decoder.close_element(elem_id)?;

        let mut trunc_size = point.size as i32;
        if basespace.is_truncated() && point.size > basespace.get_addr_size() {
            trunc_size = basespace.get_addr_size() as i32;
        }

        self.add_spacebase(
            &basespace,
            "stack",
            &point,
            trunc_size,
            isreversejustify,
            stack_growth,
            true,
        )
    }

    pub fn decode_deadcode_delay(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_DEADCODEDELAY)?;
        let spc = decoder.read_space_attr(ATTRIB_SPACE)?;
        let delay = decoder.read_signed_integer_attr(crate::space::ATTRIB_DELAY)? as i32;
        if delay >= 0 {
            self.manager.set_deadcode_delay(&spc, delay);
        } else {
            return Err(Error::Lowlevel("Bad <deadcodedelay> tag".to_string()));
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_infer_ptr_bounds(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_INFERPTRBOUNDS)?;
        while decoder.peek_element()? != 0 {
            let range = Range::decode(decoder)?;
            self.manager.set_infer_ptr_bounds(&range);
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_func_ptr_align(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_FUNCPTR)?;
        let mut align = decoder.read_signed_integer_attr(ATTRIB_ALIGN)? as i32;
        decoder.close_element(elem_id)?;

        if align == 0 {
            self.funcptr_align = 0;
            return Ok(());
        }
        let mut bits = 0;
        while (align & 1) == 0 {
            bits += 1;
            align >>= 1;
        }
        self.funcptr_align = bits;
        Ok(())
    }

    pub fn decode_spacebase(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_SPACEBASE)?;
        let name_string = decoder.read_string_attr(ATTRIB_NAME)?;
        let register_name = decoder.read_string_attr(ATTRIB_REGISTER)?;
        let basespace = decoder.read_space_attr(ATTRIB_SPACE)?;
        decoder.close_element(elem_id)?;
        let point = self.translator()?.get_register(&register_name)?;
        let size = point.size as i32;
        self.add_spacebase(&basespace, &name_string, &point, size, false, false, false)
    }

    pub fn decode_no_high_ptr(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_NOHIGHPTR)?;
        while decoder.peek_element()? != 0 {
            let range = Range::decode(decoder)?;
            self.manager.add_no_high_ptr(&range);
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_prefer_split(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_PREFERSPLIT)?;
        let style = decoder.read_string_attr(ATTRIB_STYLE)?;
        if style != "inhalf" {
            return Err(Error::Lowlevel(format!("Unknown prefersplit style: {}", style)));
        }

        while decoder.peek_element()? != 0 {
            let storage = VarnodeData::decode(decoder)?;
            let splitoffset = (storage.size / 2) as i32;
            self.splitrecords.push(PreferSplitRecord { storage, splitoffset });
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_aggressive_trim(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_AGGRESSIVETRIM)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_SIGNEXT {
                self.aggressive_ext_trim = decoder.read_bool()?;
            }
        }
        decoder.close_element(elem_id)
    }
}

pub struct SegmentedResolver {
    pub spc: SpaceRef,
    pub segop: Arc<UserPcodeOp>,
}

impl SegmentedResolver {
    pub fn new(sp: SpaceRef, sop: Arc<UserPcodeOp>) -> SegmentedResolver {
        SegmentedResolver { spc: sp, segop: sop }
    }

    pub fn resolve_with(
        &self,
        glb: &mut Architecture,
        val: u64,
        sz: i32,
        point: &Address,
        full_encoding: &mut u64,
    ) -> Result<Address> {
        let segment = self
            .segop
            .as_segment()
            .ok_or_else(|| Error::Lowlevel("segmented resolver without a segment op".to_string()))?;
        let innersz = segment.get_inner_size();
        let mut val = val;
        if sz >= 0 && sz <= innersz {
            if segment.get_resolve().space.is_some() {
                let base = glb
                    .context
                    .as_ref()
                    .ok_or_else(|| missing("context database"))?
                    .lock()
                    .expect("context database lock is poisoned")
                    .get_tracked_value(segment.get_resolve(), point);
                *full_encoding = base
                    .wrapping_shl((8 * innersz) as u32)
                    .wrapping_add(val & calc_mask(innersz));
                let seginput = vec![base, val];
                val = self.segop.execute(&seginput, glb)?;
                return Ok(Address::new(
                    self.spc.clone(),
                    AddrSpace::address_to_byte(val, self.spc.get_word_size()),
                ));
            }
        } else {
            *full_encoding = val;
            let outersz = segment.get_base_size();
            let base = val.wrapping_shr((8 * innersz) as u32) & calc_mask(outersz);
            val &= calc_mask(innersz);
            let seginput = vec![base, val];
            val = self.segop.execute(&seginput, glb)?;
            return Ok(Address::new(
                self.spc.clone(),
                AddrSpace::address_to_byte(val, self.spc.get_word_size()),
            ));
        }
        Ok(Address::default())
    }
}

impl AddressResolver for SegmentedResolver {
    fn resolve(&self, _val: u64, _sz: i32, _point: &Address, _full_encoding: &mut u64) -> Address {
        Address::default()
    }
}

impl Architecture {
    pub fn take_function(&mut self, sym: SymbolId) -> Result<Box<Funcdata>> {
        if Database::symbol_get_function(self, sym)?.is_none() {
            return Err(Error::Lowlevel("Symbol is not a function".to_string()));
        }
        self.symboltab
            .as_deref_mut()
            .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))?
            .symbol_take_function(sym)
            .ok_or_else(|| Error::Lowlevel("Function is already in use".to_string()))
    }

    pub fn restore_function(&mut self, sym: SymbolId, function: Box<Funcdata>) {
        if let Some(symboltab) = self.symboltab.as_deref_mut() {
            symboltab.symbol_restore_function(sym, function);
        }
    }

    pub fn with_function<R>(
        &mut self,
        sym: SymbolId,
        body: impl FnOnce(&mut Funcdata, &mut Architecture) -> Result<R>,
    ) -> Result<R> {
        let mut function = self.take_function(sym)?;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| body(&mut function, self)));
        self.restore_function(sym, function);
        result.unwrap_or_else(|payload| std::panic::resume_unwind(payload))
    }

    pub fn with_current_action<R>(
        &mut self,
        body: impl FnOnce(&mut dyn crate::action::Action, &mut Architecture) -> Result<R>,
    ) -> Result<R> {
        let Some(name) = self.allacts.currentact.clone() else {
            return Err(Error::Lowlevel("No action set".to_string()));
        };
        let Some(mut action) = self.allacts.actionmap.remove(&name) else {
            return Err(Error::Lowlevel("No action set".to_string()));
        };
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| body(action.as_mut(), self)));
        self.allacts.actionmap.insert(name, action);
        result.unwrap_or_else(|payload| std::panic::resume_unwind(payload))
    }

    pub fn with_printer<R>(
        &mut self,
        data: Option<&mut Funcdata>,
        body: impl FnOnce(&mut dyn PrintLanguage, &mut crate::printlanguage::PrintContext<'_>) -> Result<R>,
    ) -> Result<(R, String)> {
        let index = self.print;
        let mut printer = self.printlist[index]
            .take()
            .ok_or_else(|| Error::Lowlevel("print language is not available".to_string()))?;
        let saved = printer.take_output_stream();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut ctx = crate::printlanguage::PrintContext::new(self, data);
            body(printer.as_mut(), &mut ctx)
        }));
        let output = printer.take_output_stream();
        printer.set_output_stream(saved);
        self.printlist[index] = Some(printer);
        let result = result.unwrap_or_else(|payload| std::panic::resume_unwind(payload));
        let text = String::from_utf8_lossy(&output).into_owned();
        result.map(|value| (value, text))
    }

    pub fn function_symbols_address_order(&self) -> Result<Vec<SymbolId>> {
        let symboltab = self
            .symboltab
            .as_deref()
            .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))?;
        let root = symboltab
            .get_global_scope()
            .ok_or_else(|| Error::Lowlevel("missing global scope".to_string()))?;
        let mut functions = Vec::new();
        let mut pending = vec![root];
        while let Some(scope) = pending.pop() {
            if !symboltab.scope(scope).is_global() {
                continue;
            }
            let scope_ref = symboltab.scope(scope);
            let mut position = symboltab.scope_begin(scope);
            let end = symboltab.scope_end(scope);
            while !position.equals(&end, scope_ref) {
                let entry = position.get(scope_ref);
                let sym = symboltab.entry(entry).get_symbol();
                position.advance(scope_ref);
                if matches!(symboltab.symbol(sym).kind, crate::database::SymbolKind::Function { .. }) {
                    functions.push(sym);
                }
            }
            let children: Vec<ScopeId> = scope_ref.children().values().copied().collect();
            pending.extend(children.into_iter().rev());
        }
        Ok(functions)
    }
}
