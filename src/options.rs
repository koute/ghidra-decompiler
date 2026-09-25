use std::collections::BTreeMap;

use crate::architecture::Architecture;
use crate::comment::Comment;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::flow::{
    ERROR_REINTERPRETED, ERROR_TOOMANYINSTRUCTIONS, ERROR_UNIMPLEMENTED, IGNORE_UNIMPLEMENTED, RECORD_JUMPLOADS,
};
use crate::fspec::ProtoModel;
use crate::funcdata::Funcdata;
use crate::istream::{Basefield, read_i32, read_u32};
use crate::marshal::{ATTRIB_CONTENT, Decoder, ElementId};
use crate::prettyprint::BraceStyle;
use crate::printc::PrintC;
use crate::printlanguage::{NamespaceStrategy, PrintLanguage};

pub const ELEM_ALIASBLOCK: ElementId = ElementId::new("aliasblock", 174);
pub const ELEM_ALLOWCONTEXTSET: ElementId = ElementId::new("allowcontextset", 175);
pub const ELEM_ANALYZEFORLOOPS: ElementId = ElementId::new("analyzeforloops", 176);
pub const ELEM_COMMENTHEADER: ElementId = ElementId::new("commentheader", 177);
pub const ELEM_COMMENTINDENT: ElementId = ElementId::new("commentindent", 178);
pub const ELEM_COMMENTINSTRUCTION: ElementId = ElementId::new("commentinstruction", 179);
pub const ELEM_COMMENTSTYLE: ElementId = ElementId::new("commentstyle", 180);
pub const ELEM_CONVENTIONPRINTING: ElementId = ElementId::new("conventionprinting", 181);
pub const ELEM_CURRENTACTION: ElementId = ElementId::new("currentaction", 182);
pub const ELEM_DEFAULTPROTOTYPE: ElementId = ElementId::new("defaultprototype", 183);
pub const ELEM_ERRORREINTERPRETED: ElementId = ElementId::new("errorreinterpreted", 184);
pub const ELEM_ERRORTOOMANYINSTRUCTIONS: ElementId = ElementId::new("errortoomanyinstructions", 185);
pub const ELEM_ERRORUNIMPLEMENTED: ElementId = ElementId::new("errorunimplemented", 186);
pub const ELEM_BADDATACOUNT: ElementId = ElementId::new("baddatacount", 290);
pub const ELEM_EXTRAPOP: ElementId = ElementId::new("extrapop", 187);
pub const ELEM_IGNOREUNIMPLEMENTED: ElementId = ElementId::new("ignoreunimplemented", 188);
pub const ELEM_INDENTINCREMENT: ElementId = ElementId::new("indentincrement", 189);
pub const ELEM_INFERCONSTPTR: ElementId = ElementId::new("inferconstptr", 190);
pub const ELEM_INLINE: ElementId = ElementId::new("inline", 191);
pub const ELEM_INPLACEOPS: ElementId = ElementId::new("inplaceops", 192);
pub const ELEM_INTEGERFORMAT: ElementId = ElementId::new("integerformat", 193);
pub const ELEM_JUMPLOAD: ElementId = ElementId::new("jumpload", 194);
pub const ELEM_MAXINSTRUCTION: ElementId = ElementId::new("maxinstruction", 195);
pub const ELEM_MAXLINEWIDTH: ElementId = ElementId::new("maxlinewidth", 196);
pub const ELEM_NAMESPACESTRATEGY: ElementId = ElementId::new("namespacestrategy", 197);
pub const ELEM_NOCASTPRINTING: ElementId = ElementId::new("nocastprinting", 198);
pub const ELEM_NORETURN: ElementId = ElementId::new("noreturn", 199);
pub const ELEM_NULLPRINTING: ElementId = ElementId::new("nullprinting", 200);
pub const ELEM_OPTIONSLIST: ElementId = ElementId::new("optionslist", 201);
pub const ELEM_PARAM1: ElementId = ElementId::new("param1", 202);
pub const ELEM_PARAM2: ElementId = ElementId::new("param2", 203);
pub const ELEM_PARAM3: ElementId = ElementId::new("param3", 204);
pub const ELEM_PROTOEVAL: ElementId = ElementId::new("protoeval", 205);
pub const ELEM_SETACTION: ElementId = ElementId::new("setaction", 206);
pub const ELEM_SETLANGUAGE: ElementId = ElementId::new("setlanguage", 207);
pub const ELEM_SPLITDATATYPE: ElementId = ElementId::new("splitdatatype", 270);
pub const ELEM_STRUCTALIGN: ElementId = ElementId::new("structalign", 208);
pub const ELEM_TOGGLERULE: ElementId = ElementId::new("togglerule", 209);
pub const ELEM_WARNING: ElementId = ElementId::new("warning", 210);
pub const ELEM_JUMPTABLEMAX: ElementId = ElementId::new("jumptablemax", 271);
pub const ELEM_NANIGNORE: ElementId = ElementId::new("nanignore", 272);
pub const ELEM_BRACEFORMAT: ElementId = ElementId::new("braceformat", 284);

pub trait ArchOption: Send {
    fn get_name(&self) -> String;

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, p3: &str) -> Result<String>;
}

pub fn on_or_off(value: &str) -> Result<bool> {
    if value.is_empty() {
        return Ok(true);
    }
    if value == "on" {
        return Ok(true);
    }
    if value == "off" {
        return Ok(false);
    }
    Err(Error::Parse("Must specify toggle value, on/off".to_string()))
}

fn current_print(glb: &mut Architecture) -> &mut dyn PrintLanguage {
    let index = glb.print;
    glb.printlist[index]
        .as_deref_mut()
        .expect("current print language is taken out")
}

fn current_print_c(glb: &mut Architecture) -> Option<&mut PrintC> {
    current_print(glb).as_any_mut().downcast_mut::<PrintC>()
}

fn query_function_by_name<'a>(glb: &'a mut Architecture, name: &str) -> Result<Option<&'a mut Funcdata>> {
    let sym = {
        let symboltab = glb.symboltab_ref()?;
        let global = symboltab
            .get_global_scope()
            .ok_or_else(|| Error::Lowlevel("missing global scope".to_string()))?;
        match symboltab.scope_query_function_by_name(global, name) {
            None => return Ok(None),
            Some(sym) => sym,
        }
    };
    Database::symbol_get_function(glb, sym)
}

pub struct OptionDatabase {
    pub optionmap: BTreeMap<u32, Box<dyn ArchOption>>,
}

impl Default for OptionDatabase {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionDatabase {
    pub fn new() -> OptionDatabase {
        let mut res = OptionDatabase {
            optionmap: BTreeMap::new(),
        };
        res.register_option(Box::new(OptionExtraPop::new()));
        res.register_option(Box::new(OptionReadOnly::new()));
        res.register_option(Box::new(OptionIgnoreUnimplemented::new()));
        res.register_option(Box::new(OptionErrorUnimplemented::new()));
        res.register_option(Box::new(OptionErrorReinterpreted::new()));
        res.register_option(Box::new(OptionErrorTooManyInstructions::new()));
        res.register_option(Box::new(OptionBadDataCount::new()));
        res.register_option(Box::new(OptionDefaultPrototype::new()));
        res.register_option(Box::new(OptionInferConstPtr::new()));
        res.register_option(Box::new(OptionForLoops::new()));
        res.register_option(Box::new(OptionInline::new()));
        res.register_option(Box::new(OptionNoReturn::new()));
        res.register_option(Box::new(OptionProtoEval::new()));
        res.register_option(Box::new(OptionWarning::new()));
        res.register_option(Box::new(OptionNullPrinting::new()));
        res.register_option(Box::new(OptionInPlaceOps::new()));
        res.register_option(Box::new(OptionConventionPrinting::new()));
        res.register_option(Box::new(OptionNoCastPrinting::new()));
        res.register_option(Box::new(OptionMaxLineWidth::new()));
        res.register_option(Box::new(OptionIndentIncrement::new()));
        res.register_option(Box::new(OptionCommentIndent::new()));
        res.register_option(Box::new(OptionCommentStyle::new()));
        res.register_option(Box::new(OptionCommentHeader::new()));
        res.register_option(Box::new(OptionCommentInstruction::new()));
        res.register_option(Box::new(OptionIntegerFormat::new()));
        res.register_option(Box::new(OptionBraceFormat::new()));
        res.register_option(Box::new(OptionCurrentAction::new()));
        res.register_option(Box::new(OptionAllowContextSet::new()));
        res.register_option(Box::new(OptionSetAction::new()));
        res.register_option(Box::new(OptionSetLanguage::new()));
        res.register_option(Box::new(OptionJumpTableMax::new()));
        res.register_option(Box::new(OptionJumpLoad::new()));
        res.register_option(Box::new(OptionToggleRule::new()));
        res.register_option(Box::new(OptionAliasBlock::new()));
        res.register_option(Box::new(OptionMaxInstruction::new()));
        res.register_option(Box::new(OptionNamespaceStrategy::new()));
        res.register_option(Box::new(OptionSplitDatatypes::new()));
        res.register_option(Box::new(OptionNanIgnore::new()));
        res
    }

    pub fn register_option(&mut self, option: Box<dyn ArchOption>) {
        let id = ElementId::find(&option.get_name(), 0);
        self.optionmap.insert(id, option);
    }

    pub fn set(glb: &mut Architecture, name_id: u32, p1: &str, p2: &str, p3: &str) -> Result<String> {
        let options = glb
            .options
            .take()
            .ok_or_else(|| Error::Lowlevel("option database is taken out".to_string()))?;
        let res = match options.optionmap.get(&name_id) {
            None => Err(Error::Parse("Unknown option".to_string())),
            Some(opt) => opt.apply(glb, p1, p2, p3),
        };
        glb.options = Some(options);
        res
    }

    pub fn decode_one(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<()> {
        let mut p1 = String::new();
        let mut p2 = String::new();
        let mut p3 = String::new();

        let elem_id = decoder.open_element()?;
        let mut sub_id = decoder.open_element()?;
        if sub_id == ELEM_PARAM1 {
            p1 = decoder.read_string_attr(ATTRIB_CONTENT)?;
            decoder.close_element(sub_id)?;
            sub_id = decoder.open_element()?;
            if sub_id == ELEM_PARAM2 {
                p2 = decoder.read_string_attr(ATTRIB_CONTENT)?;
                decoder.close_element(sub_id)?;
                sub_id = decoder.open_element()?;
                if sub_id == ELEM_PARAM3 {
                    p3 = decoder.read_string_attr(ATTRIB_CONTENT)?;
                    decoder.close_element(sub_id)?;
                }
            }
        } else if sub_id == 0 {
            p1 = decoder.read_string_attr(ATTRIB_CONTENT)?;
        }
        decoder.close_element(elem_id)?;
        OptionDatabase::set(glb, elem_id, &p1, &p2, &p3)?;
        Ok(())
    }

    pub fn decode(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_OPTIONSLIST)?;
        while decoder.peek_element()? != 0 {
            OptionDatabase::decode_one(glb, decoder)?;
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub struct OptionExtraPop {
    pub name: String,
}

impl Default for OptionExtraPop {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionExtraPop {
    pub fn new() -> OptionExtraPop {
        OptionExtraPop {
            name: "extrapop".to_string(),
        }
    }
}

impl ArchOption for OptionExtraPop {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        let mut expop: i32 = -300;
        let res;
        if p1 == "unknown" {
            expop = ProtoModel::EXTRAPOP_UNKNOWN;
        } else {
            expop = read_i32(p1, Basefield::Auto, expop);
        }
        if expop == -300 {
            return Err(Error::Parse("Bad extrapop adjustment parameter".to_string()));
        }
        if !p2.is_empty() {
            let fd = query_function_by_name(glb, p2)?
                .ok_or_else(|| Error::Recov(format!("Unknown function name: {}", p2)))?;
            fd.get_func_proto_mut().set_extra_pop(expop);
            res = format!("ExtraPop set for function {}", p2);
        } else {
            let defaultfp = glb.defaultfp.expect("missing default prototype model");
            glb.proto_models[defaultfp].set_extra_pop(expop);
            if let Some(model) = glb.evalfp_current {
                glb.proto_models[model].set_extra_pop(expop);
            }
            if let Some(model) = glb.evalfp_called {
                glb.proto_models[model].set_extra_pop(expop);
            }
            res = "Global extrapop set".to_string();
        }
        Ok(res)
    }
}

pub struct OptionReadOnly {
    pub name: String,
}

impl Default for OptionReadOnly {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionReadOnly {
    pub fn new() -> OptionReadOnly {
        OptionReadOnly {
            name: "readonly".to_string(),
        }
    }
}

impl ArchOption for OptionReadOnly {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse(
                "Read-only option must be set \"on\" or \"off\"".to_string(),
            ));
        }
        glb.readonlypropagate = on_or_off(p1)?;
        if glb.readonlypropagate {
            return Ok("Read-only memory locations now propagate as constants".to_string());
        }
        Ok("Read-only memory locations now do not propagate".to_string())
    }
}

pub struct OptionDefaultPrototype {
    pub name: String,
}

impl Default for OptionDefaultPrototype {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionDefaultPrototype {
    pub fn new() -> OptionDefaultPrototype {
        OptionDefaultPrototype {
            name: "defaultprototype".to_string(),
        }
    }
}

impl ArchOption for OptionDefaultPrototype {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let model = glb
            .get_model(p1)
            .ok_or_else(|| Error::Lowlevel(format!("Unknown prototype model :{}", p1)))?;
        glb.set_default_model(model);
        Ok(format!("Set default prototype to {}", p1))
    }
}

pub struct OptionInferConstPtr {
    pub name: String,
}

impl Default for OptionInferConstPtr {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionInferConstPtr {
    pub fn new() -> OptionInferConstPtr {
        OptionInferConstPtr {
            name: "inferconstptr".to_string(),
        }
    }
}

impl ArchOption for OptionInferConstPtr {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let res;
        if val {
            res = "Constant pointers are now inferred".to_string();
            glb.infer_pointers = true;
        } else {
            res = "Constant pointers must now be set explicitly".to_string();
            glb.infer_pointers = false;
        }
        Ok(res)
    }
}

pub struct OptionForLoops {
    pub name: String,
}

impl Default for OptionForLoops {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionForLoops {
    pub fn new() -> OptionForLoops {
        OptionForLoops {
            name: "analyzeforloops".to_string(),
        }
    }
}

impl ArchOption for OptionForLoops {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        glb.analyze_for_loops = on_or_off(p1)?;
        Ok(format!("Recovery of for-loops is {}", p1))
    }
}

pub struct OptionInline {
    pub name: String,
}

impl Default for OptionInline {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionInline {
    pub fn new() -> OptionInline {
        OptionInline {
            name: "inline".to_string(),
        }
    }
}

impl ArchOption for OptionInline {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        let infd =
            query_function_by_name(glb, p1)?.ok_or_else(|| Error::Recov(format!("Unknown function name: {}", p1)))?;
        let val = if p2.is_empty() { true } else { p2 == "true" };
        infd.get_func_proto_mut().set_inline(val);
        let prop = if val { "true" } else { "false" };
        Ok(format!("Inline property for function {} = {}", p1, prop))
    }
}

pub struct OptionNoReturn {
    pub name: String,
}

impl Default for OptionNoReturn {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionNoReturn {
    pub fn new() -> OptionNoReturn {
        OptionNoReturn {
            name: "noreturn".to_string(),
        }
    }
}

impl ArchOption for OptionNoReturn {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        let infd =
            query_function_by_name(glb, p1)?.ok_or_else(|| Error::Recov(format!("Unknown function name: {}", p1)))?;
        let val = if p2.is_empty() { true } else { p2 == "true" };
        infd.get_func_proto_mut().set_no_return(val);
        let prop = if val { "true" } else { "false" };
        Ok(format!("No return property for function {} = {}", p1, prop))
    }
}

pub struct OptionWarning {
    pub name: String,
}

impl Default for OptionWarning {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionWarning {
    pub fn new() -> OptionWarning {
        OptionWarning {
            name: "warning".to_string(),
        }
    }
}

impl ArchOption for OptionWarning {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse("No action/rule specified".to_string()));
        }
        let val = if p2.is_empty() { true } else { on_or_off(p2)? };
        let res = match glb.allacts.get_current() {
            None => false,
            Some(current) => current.set_warning(val, p1),
        };
        if !res {
            return Err(Error::Recov(format!("Bad action/rule specifier: {}", p1)));
        }
        let prop = if val { "on" } else { "off" };
        Ok(format!("Warnings for {} turned {}", p1, prop))
    }
}

pub struct OptionNullPrinting {
    pub name: String,
}

impl Default for OptionNullPrinting {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionNullPrinting {
    pub fn new() -> OptionNullPrinting {
        OptionNullPrinting {
            name: "nullprinting".to_string(),
        }
    }
}

impl ArchOption for OptionNullPrinting {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        if current_print(glb).get_name() != "c-language" {
            return Ok("Only c-language accepts the null printing option".to_string());
        }
        let lng = current_print_c(glb).expect("c-language printer is not a PrintC");
        lng.set_null_printing(val);
        let prop = if val { "on" } else { "off" };
        Ok(format!("Null printing turned {}", prop))
    }
}

pub struct OptionInPlaceOps {
    pub name: String,
}

impl Default for OptionInPlaceOps {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionInPlaceOps {
    pub fn new() -> OptionInPlaceOps {
        OptionInPlaceOps {
            name: "inplaceops".to_string(),
        }
    }
}

impl ArchOption for OptionInPlaceOps {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        if current_print(glb).get_name() != "c-language" {
            return Ok("Can only set inplace operators for C language".to_string());
        }
        let lng = current_print_c(glb).expect("c-language printer is not a PrintC");
        lng.set_inplace_ops(val);
        let prop = if val { "on" } else { "off" };
        Ok(format!("Inplace operators turned {}", prop))
    }
}

pub struct OptionConventionPrinting {
    pub name: String,
}

impl Default for OptionConventionPrinting {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionConventionPrinting {
    pub fn new() -> OptionConventionPrinting {
        OptionConventionPrinting {
            name: "conventionprinting".to_string(),
        }
    }
}

impl ArchOption for OptionConventionPrinting {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        if current_print(glb).get_name() != "c-language" {
            return Ok("Can only set convention printing for C language".to_string());
        }
        let lng = current_print_c(glb).expect("c-language printer is not a PrintC");
        lng.set_convention(val);
        let prop = if val { "on" } else { "off" };
        Ok(format!("Convention printing turned {}", prop))
    }
}

pub struct OptionNoCastPrinting {
    pub name: String,
}

impl Default for OptionNoCastPrinting {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionNoCastPrinting {
    pub fn new() -> OptionNoCastPrinting {
        OptionNoCastPrinting {
            name: "nocastprinting".to_string(),
        }
    }
}

impl ArchOption for OptionNoCastPrinting {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let lng = match current_print_c(glb) {
            None => return Ok("Can only set no cast printing for C language".to_string()),
            Some(lng) => lng,
        };
        lng.set_no_cast_printing(val);
        let prop = if val { "on" } else { "off" };
        Ok(format!("No cast printing turned {}", prop))
    }
}

pub struct OptionHideExtensions {
    pub name: String,
}

impl Default for OptionHideExtensions {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionHideExtensions {
    pub fn new() -> OptionHideExtensions {
        OptionHideExtensions {
            name: "hideextensions".to_string(),
        }
    }
}

impl ArchOption for OptionHideExtensions {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let lng = match current_print_c(glb) {
            None => return Ok("Can only toggle extension hiding for C language".to_string()),
            Some(lng) => lng,
        };
        lng.set_hide_implied_exts(val);
        let prop = if val { "on" } else { "off" };
        Ok(format!("Implied extension hiding turned {}", prop))
    }
}

pub struct OptionMaxLineWidth {
    pub name: String,
}

impl Default for OptionMaxLineWidth {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionMaxLineWidth {
    pub fn new() -> OptionMaxLineWidth {
        OptionMaxLineWidth {
            name: "maxlinewidth".to_string(),
        }
    }
}

impl ArchOption for OptionMaxLineWidth {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = read_i32(p1, Basefield::Auto, -1);
        if val == -1 {
            return Err(Error::Parse("Must specify integer linewidth".to_string()));
        }
        current_print(glb).set_max_line_size(val)?;
        Ok(format!("Maximum line width set to {}", p1))
    }
}

pub struct OptionIndentIncrement {
    pub name: String,
}

impl Default for OptionIndentIncrement {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionIndentIncrement {
    pub fn new() -> OptionIndentIncrement {
        OptionIndentIncrement {
            name: "indentincrement".to_string(),
        }
    }
}

impl ArchOption for OptionIndentIncrement {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = read_i32(p1, Basefield::Auto, -1);
        if val == -1 {
            return Err(Error::Parse("Must specify integer increment".to_string()));
        }
        current_print(glb).set_indent_increment(val);
        Ok(format!("Characters per indent level set to {}", p1))
    }
}

pub struct OptionCommentIndent {
    pub name: String,
}

impl Default for OptionCommentIndent {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionCommentIndent {
    pub fn new() -> OptionCommentIndent {
        OptionCommentIndent {
            name: "commentindent".to_string(),
        }
    }
}

impl ArchOption for OptionCommentIndent {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = read_i32(p1, Basefield::Auto, -1);
        if val == -1 {
            return Err(Error::Parse("Must specify integer comment indent".to_string()));
        }
        current_print(glb).set_line_comment_indent(val)?;
        Ok(format!("Comment indent set to {}", p1))
    }
}

pub struct OptionCommentStyle {
    pub name: String,
}

impl Default for OptionCommentStyle {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionCommentStyle {
    pub fn new() -> OptionCommentStyle {
        OptionCommentStyle {
            name: "commentstyle".to_string(),
        }
    }
}

impl ArchOption for OptionCommentStyle {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        current_print(glb).set_comment_style(p1)?;
        Ok(format!("Comment style set to {}", p1))
    }
}

pub struct OptionCommentHeader {
    pub name: String,
}

impl Default for OptionCommentHeader {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionCommentHeader {
    pub fn new() -> OptionCommentHeader {
        OptionCommentHeader {
            name: "commentheader".to_string(),
        }
    }
}

impl ArchOption for OptionCommentHeader {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        let toggle = on_or_off(p2)?;
        let mut flags = current_print(glb).get_header_comment();
        let val = Comment::encode_comment_type(p1)?;
        if toggle {
            flags |= val;
        } else {
            flags &= !val;
        }
        current_print(glb).set_header_comment(flags);
        let prop = if toggle { "on" } else { "off" };
        Ok(format!("Header comment type {} turned {}", p1, prop))
    }
}

pub struct OptionCommentInstruction {
    pub name: String,
}

impl Default for OptionCommentInstruction {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionCommentInstruction {
    pub fn new() -> OptionCommentInstruction {
        OptionCommentInstruction {
            name: "commentinstruction".to_string(),
        }
    }
}

impl ArchOption for OptionCommentInstruction {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        let toggle = on_or_off(p2)?;
        let mut flags = current_print(glb).get_instruction_comment();
        let val = Comment::encode_comment_type(p1)?;
        if toggle {
            flags |= val;
        } else {
            flags &= !val;
        }
        current_print(glb).set_instruction_comment(flags);
        let prop = if toggle { "on" } else { "off" };
        Ok(format!("Instruction comment type {} turned {}", p1, prop))
    }
}

pub struct OptionIntegerFormat {
    pub name: String,
}

impl Default for OptionIntegerFormat {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionIntegerFormat {
    pub fn new() -> OptionIntegerFormat {
        OptionIntegerFormat {
            name: "integerformat".to_string(),
        }
    }
}

impl ArchOption for OptionIntegerFormat {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        current_print(glb).set_integer_format(p1)?;
        Ok(format!("Integer format set to {}", p1))
    }
}

pub struct OptionBraceFormat {
    pub name: String,
}

impl Default for OptionBraceFormat {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionBraceFormat {
    pub fn new() -> OptionBraceFormat {
        OptionBraceFormat {
            name: "braceformat".to_string(),
        }
    }
}

impl ArchOption for OptionBraceFormat {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        let lng = match current_print_c(glb) {
            None => return Ok("Can only set brace formatting for C language".to_string()),
            Some(lng) => lng,
        };
        let style = if p2 == "same" {
            BraceStyle::SameLine
        } else if p2 == "next" {
            BraceStyle::NextLine
        } else if p2 == "skip" {
            BraceStyle::SkipLine
        } else {
            return Err(Error::Parse(format!("Unknown brace style: {}", p2)));
        };
        if p1 == "function" {
            lng.set_brace_format_function(style);
        } else if p1 == "ifelse" {
            lng.set_brace_format_if_else(style);
        } else if p1 == "loop" {
            lng.set_brace_format_loop(style);
        } else if p1 == "switch" {
            lng.set_brace_format_switch(style);
        } else {
            return Err(Error::Parse(format!("Unknown brace format category: {}", p1)));
        }
        Ok(format!("Brace formatting for {} set to {}", p1, p2))
    }
}

pub struct OptionSetAction {
    pub name: String,
}

impl Default for OptionSetAction {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionSetAction {
    pub fn new() -> OptionSetAction {
        OptionSetAction {
            name: "setaction".to_string(),
        }
    }
}

impl ArchOption for OptionSetAction {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse("Must specify preexisting action".to_string()));
        }
        if !p2.is_empty() {
            glb.allacts.clone_group(p1, p2)?;
            glb.allacts.set_current(p2)?;
            return Ok(format!("Created {} by cloning {} and made it current", p2, p1));
        }
        glb.allacts.set_current(p1)?;
        Ok(format!("Set current action to {}", p1))
    }
}

pub struct OptionCurrentAction {
    pub name: String,
}

impl Default for OptionCurrentAction {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionCurrentAction {
    pub fn new() -> OptionCurrentAction {
        OptionCurrentAction {
            name: "currentaction".to_string(),
        }
    }
}

impl ArchOption for OptionCurrentAction {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, p3: &str) -> Result<String> {
        if p1.is_empty() || p2.is_empty() {
            return Err(Error::Parse("Must specify subaction, on/off".to_string()));
        }
        let mut res = "Toggled ".to_string();
        if !p3.is_empty() {
            glb.allacts.set_current(p1)?;
            let val = on_or_off(p3)?;
            glb.allacts.toggle_action(p1, p2, val)?;
            res += &format!("{} in action {}", p2, p1);
        } else {
            let val = on_or_off(p2)?;
            let current = glb.allacts.get_current_name().to_string();
            glb.allacts.toggle_action(&current, p1, val)?;
            res += &format!("{} in action {}", p1, glb.allacts.get_current_name());
        }
        Ok(res)
    }
}

pub struct OptionAllowContextSet {
    pub name: String,
}

impl Default for OptionAllowContextSet {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionAllowContextSet {
    pub fn new() -> OptionAllowContextSet {
        OptionAllowContextSet {
            name: "allowcontextset".to_string(),
        }
    }
}

impl ArchOption for OptionAllowContextSet {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let prop = if val { "on" } else { "off" };
        let res = format!("Toggled allowcontextset to {}", prop);
        glb.translate
            .as_deref()
            .expect("missing translator")
            .allow_context_set(val);
        Ok(res)
    }
}

pub struct OptionIgnoreUnimplemented {
    pub name: String,
}

impl Default for OptionIgnoreUnimplemented {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionIgnoreUnimplemented {
    pub fn new() -> OptionIgnoreUnimplemented {
        OptionIgnoreUnimplemented {
            name: "ignoreunimplemented".to_string(),
        }
    }
}

impl ArchOption for OptionIgnoreUnimplemented {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let res;
        if val {
            res = "Unimplemented instructions are now ignored (treated as nop)".to_string();
            glb.flowoptions |= IGNORE_UNIMPLEMENTED;
        } else {
            res = "Unimplemented instructions now generate warnings".to_string();
            glb.flowoptions &= !IGNORE_UNIMPLEMENTED;
        }
        Ok(res)
    }
}

pub struct OptionErrorUnimplemented {
    pub name: String,
}

impl Default for OptionErrorUnimplemented {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionErrorUnimplemented {
    pub fn new() -> OptionErrorUnimplemented {
        OptionErrorUnimplemented {
            name: "errorunimplemented".to_string(),
        }
    }
}

impl ArchOption for OptionErrorUnimplemented {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let res;
        if val {
            res = "Unimplemented instructions are now a fatal error".to_string();
            glb.flowoptions |= ERROR_UNIMPLEMENTED;
        } else {
            res = "Unimplemented instructions now NOT a fatal error".to_string();
            glb.flowoptions &= !ERROR_UNIMPLEMENTED;
        }
        Ok(res)
    }
}

pub struct OptionErrorReinterpreted {
    pub name: String,
}

impl Default for OptionErrorReinterpreted {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionErrorReinterpreted {
    pub fn new() -> OptionErrorReinterpreted {
        OptionErrorReinterpreted {
            name: "errorreinterpreted".to_string(),
        }
    }
}

impl ArchOption for OptionErrorReinterpreted {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let res;
        if val {
            res = "Instruction reinterpretation is now a fatal error".to_string();
            glb.flowoptions |= ERROR_REINTERPRETED;
        } else {
            res = "Instruction reinterpretation is now NOT a fatal error".to_string();
            glb.flowoptions &= !ERROR_REINTERPRETED;
        }
        Ok(res)
    }
}

pub struct OptionErrorTooManyInstructions {
    pub name: String,
}

impl Default for OptionErrorTooManyInstructions {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionErrorTooManyInstructions {
    pub fn new() -> OptionErrorTooManyInstructions {
        OptionErrorTooManyInstructions {
            name: "errortoomanyinstructions".to_string(),
        }
    }
}

impl ArchOption for OptionErrorTooManyInstructions {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let res;
        if val {
            res = "Too many instructions are now a fatal error".to_string();
            glb.flowoptions |= ERROR_TOOMANYINSTRUCTIONS;
        } else {
            res = "Too many instructions are now NOT a fatal error".to_string();
            glb.flowoptions &= !ERROR_TOOMANYINSTRUCTIONS;
        }
        Ok(res)
    }
}

pub struct OptionBadDataCount {
    pub name: String,
}

impl Default for OptionBadDataCount {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionBadDataCount {
    pub fn new() -> OptionBadDataCount {
        OptionBadDataCount {
            name: "baddatacount".to_string(),
        }
    }
}

impl ArchOption for OptionBadDataCount {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let new_max: u32;
        let res;
        if p1.is_empty() {
            new_max = 0xffffffff;
            res = "No limit on instructions that cannot be disassembled".to_string();
        } else {
            new_max = read_u32(p1, Basefield::Auto, 0xdeadbeef);
            if new_max == 0xdeadbeef {
                return Err(Error::Parse("Bad baddatacount parameter".to_string()));
            }
            res = format!("Maximum instructions that cannot be disassembled set to {}", p1);
        }
        glb.max_baddata = new_max;
        Ok(res)
    }
}

pub struct OptionProtoEval {
    pub name: String,
}

impl Default for OptionProtoEval {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionProtoEval {
    pub fn new() -> OptionProtoEval {
        OptionProtoEval {
            name: "protoeval".to_string(),
        }
    }
}

impl ArchOption for OptionProtoEval {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse("Must specify prototype model".to_string()));
        }
        let model = if p1 == "default" {
            glb.defaultfp
        } else {
            match glb.get_model(p1) {
                None => return Err(Error::Parse(format!("Unknown prototype model: {}", p1))),
                Some(model) => Some(model),
            }
        };
        let res = format!("Set current evaluation to {}", p1);
        glb.evalfp_current = model;
        Ok(res)
    }
}

pub struct OptionSetLanguage {
    pub name: String,
}

impl Default for OptionSetLanguage {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionSetLanguage {
    pub fn new() -> OptionSetLanguage {
        OptionSetLanguage {
            name: "setlanguage".to_string(),
        }
    }
}

impl ArchOption for OptionSetLanguage {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        glb.set_print_language(p1)?;
        Ok(format!("Decompiler produces {}", p1))
    }
}

pub struct OptionJumpTableMax {
    pub name: String,
}

impl Default for OptionJumpTableMax {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionJumpTableMax {
    pub fn new() -> OptionJumpTableMax {
        OptionJumpTableMax {
            name: "jumptablemax".to_string(),
        }
    }
}

impl ArchOption for OptionJumpTableMax {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = read_u32(p1, Basefield::Auto, 0);
        if val == 0 {
            return Err(Error::Parse("Must specify integer maximum".to_string()));
        }
        glb.max_jumptable_size = val;
        Ok(format!("Maximum jumptable size set to {}", p1))
    }
}

pub struct OptionJumpLoad {
    pub name: String,
}

impl Default for OptionJumpLoad {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionJumpLoad {
    pub fn new() -> OptionJumpLoad {
        OptionJumpLoad {
            name: "jumpload".to_string(),
        }
    }
}

impl ArchOption for OptionJumpLoad {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let val = on_or_off(p1)?;
        let res;
        if val {
            res = "Jumptable analysis will record loads required to calculate jump address".to_string();
            glb.flowoptions |= RECORD_JUMPLOADS;
        } else {
            res = "Jumptable analysis will NOT record loads".to_string();
            glb.flowoptions &= !RECORD_JUMPLOADS;
        }
        Ok(res)
    }
}

pub struct OptionToggleRule {
    pub name: String,
}

impl Default for OptionToggleRule {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionToggleRule {
    pub fn new() -> OptionToggleRule {
        OptionToggleRule {
            name: "togglerule".to_string(),
        }
    }
}

impl ArchOption for OptionToggleRule {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse("Must specify rule path".to_string()));
        }
        if p2.is_empty() {
            return Err(Error::Parse("Must specify on/off".to_string()));
        }
        let val = on_or_off(p2)?;
        let root = glb
            .allacts
            .get_current()
            .ok_or_else(|| Error::Lowlevel("Missing current action".to_string()))?;
        let mut res;
        if !val {
            if root.disable_rule(p1) {
                res = "Successfully disabled".to_string();
            } else {
                res = "Failed to disable".to_string();
            }
            res += " rule";
        } else {
            if root.enable_rule(p1) {
                res = "Successfully enabled".to_string();
            } else {
                res = "Failed to enable".to_string();
            }
            res += " rule";
        }
        Ok(res)
    }
}

pub struct OptionAliasBlock {
    pub name: String,
}

impl Default for OptionAliasBlock {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionAliasBlock {
    pub fn new() -> OptionAliasBlock {
        OptionAliasBlock {
            name: "aliasblock".to_string(),
        }
    }
}

impl ArchOption for OptionAliasBlock {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse("Must specify alias block level".to_string()));
        }
        let old_val = glb.alias_block_level;
        if p1 == "none" {
            glb.alias_block_level = 0;
        } else if p1 == "struct" {
            glb.alias_block_level = 1;
        } else if p1 == "array" {
            glb.alias_block_level = 2;
        } else if p1 == "all" {
            glb.alias_block_level = 3;
        } else {
            return Err(Error::Parse(format!("Unknown alias block level: {}", p1)));
        }
        if old_val == glb.alias_block_level {
            return Ok("Alias block level unchanged".to_string());
        }
        Ok(format!("Alias block level set to {}", p1))
    }
}

pub struct OptionMaxInstruction {
    pub name: String,
}

impl Default for OptionMaxInstruction {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionMaxInstruction {
    pub fn new() -> OptionMaxInstruction {
        OptionMaxInstruction {
            name: "maxinstruction".to_string(),
        }
    }
}

impl ArchOption for OptionMaxInstruction {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        if p1.is_empty() {
            return Err(Error::Parse("Must specify number of instructions".to_string()));
        }
        let new_max = read_i32(p1, Basefield::Auto, -1);
        if new_max < 0 {
            return Err(Error::Parse("Bad maxinstruction parameter".to_string()));
        }
        glb.max_instructions = new_max as u32;
        Ok("Maximum instructions per function set".to_string())
    }
}

pub struct OptionNamespaceStrategy {
    pub name: String,
}

impl Default for OptionNamespaceStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionNamespaceStrategy {
    pub fn new() -> OptionNamespaceStrategy {
        OptionNamespaceStrategy {
            name: "namespacestrategy".to_string(),
        }
    }
}

impl ArchOption for OptionNamespaceStrategy {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let strategy = if p1 == "minimal" {
            NamespaceStrategy::MinimalNamespaces
        } else if p1 == "all" {
            NamespaceStrategy::AllNamespaces
        } else if p1 == "none" {
            NamespaceStrategy::NoNamespaces
        } else {
            return Err(Error::Parse("Must specify a valid strategy".to_string()));
        };
        current_print(glb).set_namespace_strategy(strategy);
        Ok("Namespace strategy set".to_string())
    }
}

pub struct OptionSplitDatatypes {
    pub name: String,
}

impl Default for OptionSplitDatatypes {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionSplitDatatypes {
    pub fn new() -> OptionSplitDatatypes {
        OptionSplitDatatypes {
            name: "splitdatatype".to_string(),
        }
    }

    pub const OPTION_STRUCT: u32 = 1;
    pub const OPTION_ARRAY: u32 = 2;
    pub const OPTION_POINTER: u32 = 4;

    pub fn get_option_bit(val: &str) -> Result<u32> {
        if val.is_empty() {
            return Ok(0);
        }
        if val == "struct" {
            return Ok(OptionSplitDatatypes::OPTION_STRUCT);
        }
        if val == "array" {
            return Ok(OptionSplitDatatypes::OPTION_ARRAY);
        }
        if val == "pointer" {
            return Ok(OptionSplitDatatypes::OPTION_POINTER);
        }
        Err(Error::Lowlevel(format!("Unknown data-type split option: {}", val)))
    }
}

impl ArchOption for OptionSplitDatatypes {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, p2: &str, p3: &str) -> Result<String> {
        let old_config = glb.split_datatype_config;
        glb.split_datatype_config = OptionSplitDatatypes::get_option_bit(p1)?;
        glb.split_datatype_config |= OptionSplitDatatypes::get_option_bit(p2)?;
        glb.split_datatype_config |= OptionSplitDatatypes::get_option_bit(p3)?;

        let current = glb.allacts.get_current_name().to_string();
        if (glb.split_datatype_config & (OptionSplitDatatypes::OPTION_STRUCT | OptionSplitDatatypes::OPTION_ARRAY)) == 0
        {
            glb.allacts.toggle_action(&current, "splitcopy", false)?;
            glb.allacts.toggle_action(&current, "splitpointer", false)?;
        } else {
            let pointers = (glb.split_datatype_config & OptionSplitDatatypes::OPTION_POINTER) != 0;
            glb.allacts.toggle_action(&current, "splitcopy", true)?;
            glb.allacts.toggle_action(&current, "splitpointer", pointers)?;
        }

        if old_config == glb.split_datatype_config {
            return Ok("Split data-type configuration unchanged".to_string());
        }
        Ok("Split data-type configuration set".to_string())
    }
}

pub struct OptionNanIgnore {
    pub name: String,
}

impl Default for OptionNanIgnore {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionNanIgnore {
    pub fn new() -> OptionNanIgnore {
        OptionNanIgnore {
            name: "nanignore".to_string(),
        }
    }
}

impl ArchOption for OptionNanIgnore {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn apply(&self, glb: &mut Architecture, p1: &str, _p2: &str, _p3: &str) -> Result<String> {
        let old_ignore_all = glb.nan_ignore_all;
        let old_ignore_compare = glb.nan_ignore_compare;

        if p1 == "none" {
            glb.nan_ignore_all = false;
            glb.nan_ignore_compare = false;
        } else if p1 == "compare" {
            glb.nan_ignore_all = false;
            glb.nan_ignore_compare = true;
        } else if p1 == "all" {
            glb.nan_ignore_all = true;
            glb.nan_ignore_compare = true;
        } else {
            return Err(Error::Lowlevel(format!("Unknown nanignore option: {}", p1)));
        }
        let ignore_nothing = !glb.nan_ignore_all && !glb.nan_ignore_compare;
        let root = glb
            .allacts
            .get_current()
            .ok_or_else(|| Error::Lowlevel("Missing current action".to_string()))?;
        if ignore_nothing {
            root.disable_rule("ignorenan");
        } else {
            root.enable_rule("ignorenan");
        }
        if old_ignore_all == glb.nan_ignore_all && old_ignore_compare == glb.nan_ignore_compare {
            return Ok("NaN ignore configuration unchanged".to_string());
        }
        Ok(format!("Nan ignore configuration set to: {}", p1))
    }
}
