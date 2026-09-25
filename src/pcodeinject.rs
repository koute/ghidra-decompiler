use std::collections::BTreeMap;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::emulate::{Emulate, PcodeEmitCache};
use crate::emulateutil::EmulateSnippet;
use crate::error::{Error, Result};
use crate::marshal::{ATTRIB_NAME, ATTRIB_SIZE, AttributeId, Decoder, ELEM_INPUT, ELEM_OUTPUT, ElementId, Encoder};
use crate::opbehavior::OpBehaviorRef;
use crate::pcoderaw::VarnodeData;
use crate::translate::PcodeEmit;

pub const ATTRIB_DYNAMIC: AttributeId = AttributeId::new("dynamic", 70);
pub const ATTRIB_INCIDENTALCOPY: AttributeId = AttributeId::new("incidentalcopy", 71);
pub const ATTRIB_INJECT: AttributeId = AttributeId::new("inject", 72);
pub const ATTRIB_PARAMSHIFT: AttributeId = AttributeId::new("paramshift", 73);
pub const ATTRIB_TARGETOP: AttributeId = AttributeId::new("targetop", 74);
pub const ELEM_ADDR_PCODE: ElementId = ElementId::new("addr_pcode", 89);
pub const ELEM_BODY: ElementId = ElementId::new("body", 90);
pub const ELEM_CALLFIXUP: ElementId = ElementId::new("callfixup", 91);
pub const ELEM_CALLOTHERFIXUP: ElementId = ElementId::new("callotherfixup", 92);
pub const ELEM_CASE_PCODE: ElementId = ElementId::new("case_pcode", 93);
pub const ELEM_CONTEXT: ElementId = ElementId::new("context", 94);
pub const ELEM_DEFAULT_PCODE: ElementId = ElementId::new("default_pcode", 95);
pub const ELEM_INJECT: ElementId = ElementId::new("inject", 96);
pub const ELEM_INJECTDEBUG: ElementId = ElementId::new("injectdebug", 97);
pub const ELEM_INST: ElementId = ElementId::new("inst", 98);
pub const ELEM_PAYLOAD: ElementId = ElementId::new("payload", 99);
pub const ELEM_PCODE: ElementId = ElementId::new("pcode", 100);
pub const ELEM_SIZE_PCODE: ElementId = ElementId::new("size_pcode", 101);

pub const CALLFIXUP_TYPE: i32 = 1;
pub const CALLOTHERFIXUP_TYPE: i32 = 2;
pub const CALLMECHANISM_TYPE: i32 = 3;
pub const EXECUTABLEPCODE_TYPE: i32 = 4;

#[derive(Clone, Debug)]
pub struct InjectParameter {
    pub name: String,
    pub index: i32,
    pub size: u32,
}

impl InjectParameter {
    pub fn new(nm: &str, sz: u32) -> InjectParameter {
        InjectParameter {
            name: nm.to_string(),
            index: 0,
            size: sz,
        }
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_index(&self) -> i32 {
        self.index
    }

    pub fn get_size(&self) -> u32 {
        self.size
    }
}

#[derive(Clone, Debug, Default)]
pub struct InjectContextBase {
    pub baseaddr: Address,
    pub nextaddr: Address,
    pub calladdr: Address,
    pub inputlist: Vec<VarnodeData>,
    pub output: Vec<VarnodeData>,
}

pub trait InjectContext {
    fn base(&self) -> &InjectContextBase;

    fn base_mut(&mut self) -> &mut InjectContextBase;

    fn clear(&mut self) {
        let base = self.base_mut();
        base.inputlist.clear();
        base.output.clear();
    }

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()>;
}

#[derive(Clone, Debug)]
pub struct InjectPayloadBase {
    pub name: String,
    pub tp: i32,
    pub dynamic: bool,
    pub incidental_copy: bool,
    pub paramshift: i32,
    pub inputlist: Vec<InjectParameter>,
    pub output: Vec<InjectParameter>,
}

impl InjectPayloadBase {
    pub fn new(nm: &str, tp: i32) -> InjectPayloadBase {
        InjectPayloadBase {
            name: nm.to_string(),
            tp,
            dynamic: false,
            incidental_copy: false,
            paramshift: 0,
            inputlist: Vec::new(),
            output: Vec::new(),
        }
    }

    pub fn decode_parameter(decoder: &mut dyn Decoder) -> Result<(String, u32)> {
        let mut name = String::new();
        let mut size: u32 = 0;
        let elem_id = decoder.open_element()?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_NAME {
                name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_SIZE {
                size = decoder.read_unsigned_integer()? as u32;
            }
        }
        decoder.close_element(elem_id)?;
        if name.is_empty() {
            return Err(Error::Lowlevel("Missing inject parameter name".to_string()));
        }
        Ok((name, size))
    }

    pub fn order_parameters(&mut self) {
        let mut id = 0;
        for param in self.inputlist.iter_mut() {
            param.index = id;
            id += 1;
        }
        for param in self.output.iter_mut() {
            param.index = id;
            id += 1;
        }
    }

    pub fn decode_payload_attributes(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.paramshift = 0;
        self.dynamic = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_PARAMSHIFT {
                self.paramshift = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_DYNAMIC {
                self.dynamic = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_INCIDENTALCOPY {
                self.incidental_copy = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_INJECT {
                let upon_type = decoder.read_string()?;
                if upon_type == "uponentry" {
                    self.name = format!("{}@@inject_uponentry", self.name);
                } else {
                    self.name = format!("{}@@inject_uponreturn", self.name);
                }
            }
        }
        Ok(())
    }

    pub fn decode_payload_params(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == ELEM_INPUT {
                let (param_name, size) = InjectPayloadBase::decode_parameter(decoder)?;
                self.inputlist.push(InjectParameter::new(&param_name, size));
            } else if sub_id == ELEM_OUTPUT {
                let (param_name, size) = InjectPayloadBase::decode_parameter(decoder)?;
                self.output.push(InjectParameter::new(&param_name, size));
            } else {
                break;
            }
        }
        self.order_parameters();
        Ok(())
    }
}

pub trait InjectPayload: Send {
    fn base(&self) -> &InjectPayloadBase;

    fn base_mut(&mut self) -> &mut InjectPayloadBase;

    fn get_param_shift(&self) -> i32 {
        self.base().paramshift
    }

    fn is_dynamic(&self) -> bool {
        self.base().dynamic
    }

    fn is_incidental_copy(&self) -> bool {
        self.base().incidental_copy
    }

    fn size_input(&self) -> i32 {
        self.base().inputlist.len() as i32
    }

    fn size_output(&self) -> i32 {
        self.base().output.len() as i32
    }

    fn get_input(&mut self, index: i32) -> &mut InjectParameter {
        &mut self.base_mut().inputlist[index as usize]
    }

    fn get_output(&mut self, index: i32) -> &mut InjectParameter {
        &mut self.base_mut().output[index as usize]
    }

    fn inject(&self, context: &mut dyn InjectContext, emit: &mut dyn PcodeEmit) -> Result<()>;

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()>;

    fn print_template(&self, out: &mut String);

    fn get_name(&self) -> String {
        self.base().name.clone()
    }

    fn get_type(&self) -> i32 {
        self.base().tp
    }

    fn get_source(&self) -> String;

    fn as_executable(&self) -> Option<&ExecutablePcode> {
        None
    }

    fn as_executable_mut(&mut self) -> Option<&mut ExecutablePcode> {
        None
    }
}

#[derive(Clone, Debug)]
pub struct ExecutablePcode {
    pub base: InjectPayloadBase,
    pub source: String,
    pub built: bool,
    pub emulator: EmulateSnippet,
    pub input_list: Vec<u64>,
    pub output_list: Vec<u64>,
}

impl ExecutablePcode {
    pub fn new(src: &str, nm: &str) -> ExecutablePcode {
        ExecutablePcode {
            base: InjectPayloadBase::new(nm, EXECUTABLEPCODE_TYPE),
            source: src.to_string(),
            built: false,
            emulator: EmulateSnippet::new(),
            input_list: Vec::new(),
            output_list: Vec::new(),
        }
    }

    pub fn get_source(&self) -> String {
        self.source.clone()
    }

    fn executable_part(payload: &mut dyn InjectPayload) -> Result<&mut ExecutablePcode> {
        payload
            .as_executable_mut()
            .ok_or_else(|| Error::Lowlevel("inject payload is not executable p-code".to_string()))
    }

    pub fn build(payload: &mut dyn InjectPayload, glb: &mut Architecture) -> Result<()> {
        if ExecutablePcode::executable_part(payload)?.built {
            return Ok(());
        }
        let code_space = glb.manager.get_default_code_space();
        let uniq_space = glb.manager.get_unique_space();
        let input_sizes: Vec<u32> = payload.base().inputlist.iter().map(|param| param.get_size()).collect();
        let output_sizes: Vec<u32> = payload.base().output.iter().map(|param| param.get_size()).collect();
        let library = glb
            .pcodeinjectlib
            .as_deref_mut()
            .ok_or_else(|| Error::Lowlevel("missing p-code inject library".to_string()))?;
        let icontext = library.get_cached_context();
        icontext.clear();
        let mut uniq_reserve: u64 = 0x10;
        {
            let exe = ExecutablePcode::executable_part(payload)?;
            let context_base = icontext.base_mut();
            context_base.baseaddr = Address::from_parts(code_space, 0x1000);
            context_base.nextaddr = context_base.baseaddr.clone();
            for size in input_sizes.iter() {
                context_base.inputlist.push(VarnodeData {
                    space: uniq_space.clone(),
                    offset: uniq_reserve,
                    size: *size,
                });
                exe.input_list.push(uniq_reserve);
                uniq_reserve += 0x20;
            }
            for size in output_sizes.iter() {
                context_base.output.push(VarnodeData {
                    space: uniq_space.clone(),
                    offset: uniq_reserve,
                    size: *size,
                });
                exe.output_list.push(uniq_reserve);
                uniq_reserve += 0x20;
            }
        }
        let mut ops = std::mem::take(&mut ExecutablePcode::executable_part(payload)?.emulator.op_list);
        let inject_result = {
            let mut emitter = PcodeEmitCache::new(&mut ops, uniq_reserve);
            payload.inject(icontext, &mut emitter)
        };
        let exe = ExecutablePcode::executable_part(payload)?;
        exe.emulator.op_list = ops;
        inject_result?;
        if !exe.emulator.check_for_legal_code() {
            return Err(Error::Lowlevel("Illegal p-code in executable snippet".to_string()));
        }
        exe.built = true;
        Ok(())
    }

    pub fn evaluate(payload: &mut dyn InjectPayload, input: &[u64], glb: &mut Architecture) -> Result<u64> {
        ExecutablePcode::build(payload, glb)?;
        let exe = ExecutablePcode::executable_part(payload)?;
        exe.emulator.reset_memory();
        if input.len() != exe.input_list.len() {
            return Err(Error::Lowlevel(
                "Wrong number of input parameters to executable snippet".to_string(),
            ));
        }
        if exe.output_list.is_empty() {
            return Err(Error::Lowlevel(
                "No registered outputs to executable snippet".to_string(),
            ));
        }
        for (index, value) in input.iter().enumerate() {
            let offset = exe.input_list[index];
            exe.emulator.set_varnode_value(offset, *value);
        }
        while !Emulate::get_halt(&exe.emulator) {
            Emulate::execute_current_op(&mut exe.emulator, glb)?;
        }
        Ok(exe.emulator.get_temp_value(exe.output_list[0]))
    }
}

#[derive(Default)]
pub struct PcodeInjectLibraryBase {
    pub tempbase: u32,
    pub injection: Vec<Option<Box<dyn InjectPayload>>>,
    pub call_fixup_map: BTreeMap<String, i32>,
    pub call_other_fixup_map: BTreeMap<String, i32>,
    pub call_mech_fixup_map: BTreeMap<String, i32>,
    pub script_map: BTreeMap<String, i32>,
    pub call_fixup_names: Vec<String>,
    pub call_other_target: Vec<String>,
    pub call_mech_target: Vec<String>,
    pub script_names: Vec<String>,
}

impl PcodeInjectLibraryBase {
    pub fn new(tmpbase: u32) -> PcodeInjectLibraryBase {
        PcodeInjectLibraryBase {
            tempbase: tmpbase,
            ..PcodeInjectLibraryBase::default()
        }
    }
}

fn register_name(
    map: &mut BTreeMap<String, i32>,
    names: &mut Vec<String>,
    name: &str,
    injectid: i32,
    tag: &str,
) -> Result<()> {
    if map.contains_key(name) {
        return Err(Error::Lowlevel(format!("Duplicate <{}>: {}", tag, name)));
    }
    map.insert(name.to_string(), injectid);
    while names.len() as i32 <= injectid {
        names.push(String::new());
    }
    names[injectid as usize] = name.to_string();
    Ok(())
}

fn name_by_id(names: &[String], injectid: i32) -> String {
    if injectid < 0 || injectid as usize >= names.len() {
        return String::new();
    }
    names[injectid as usize].clone()
}

pub trait PcodeInjectLibrary: Send {
    fn base(&self) -> &PcodeInjectLibraryBase;

    fn base_mut(&mut self) -> &mut PcodeInjectLibraryBase;

    fn register_call_fixup(&mut self, fixup_name: &str, injectid: i32) -> Result<()> {
        let base = self.base_mut();
        register_name(
            &mut base.call_fixup_map,
            &mut base.call_fixup_names,
            fixup_name,
            injectid,
            "callfixup",
        )
    }

    fn register_call_other_fixup(&mut self, fixup_name: &str, injectid: i32) -> Result<()> {
        let base = self.base_mut();
        register_name(
            &mut base.call_other_fixup_map,
            &mut base.call_other_target,
            fixup_name,
            injectid,
            "callotherfixup",
        )
    }

    fn register_call_mechanism(&mut self, fixup_name: &str, injectid: i32) -> Result<()> {
        let base = self.base_mut();
        register_name(
            &mut base.call_mech_fixup_map,
            &mut base.call_mech_target,
            fixup_name,
            injectid,
            "callmechanism",
        )
    }

    fn register_exe_script(&mut self, script_name: &str, injectid: i32) -> Result<()> {
        let base = self.base_mut();
        register_name(
            &mut base.script_map,
            &mut base.script_names,
            script_name,
            injectid,
            "script",
        )
    }

    fn allocate_inject(&mut self, source_name: &str, name: &str, tp: i32) -> Result<i32>;

    fn register_inject(&mut self, injectid: i32, glb: &mut Architecture) -> Result<()>;

    fn get_unique_base(&self) -> u32 {
        self.base().tempbase
    }

    fn get_payload_id(&self, tp: i32, nm: &str) -> i32 {
        let base = self.base();
        let map = if tp == CALLFIXUP_TYPE {
            &base.call_fixup_map
        } else if tp == CALLOTHERFIXUP_TYPE {
            &base.call_other_fixup_map
        } else if tp == CALLMECHANISM_TYPE {
            &base.call_mech_fixup_map
        } else {
            &base.script_map
        };
        match map.get(nm) {
            None => -1,
            Some(id) => *id,
        }
    }

    fn get_payload(&self, id: i32) -> &dyn InjectPayload {
        self.base().injection[id as usize]
            .as_deref()
            .expect("inject payload is taken out of the library")
    }

    fn get_payload_mut(&mut self, id: i32) -> &mut dyn InjectPayload {
        self.base_mut().injection[id as usize]
            .as_deref_mut()
            .expect("inject payload is taken out of the library")
    }

    fn take_payload(&mut self, id: i32) -> Box<dyn InjectPayload> {
        self.base_mut().injection[id as usize]
            .take()
            .expect("inject payload is taken out of the library")
    }

    fn restore_payload(&mut self, id: i32, payload: Box<dyn InjectPayload>) {
        self.base_mut().injection[id as usize] = Some(payload);
    }

    fn get_call_fixup_name(&self, injectid: i32) -> String {
        name_by_id(&self.base().call_fixup_names, injectid)
    }

    fn get_call_other_target(&self, injectid: i32) -> String {
        name_by_id(&self.base().call_other_target, injectid)
    }

    fn get_call_mechanism_name(&self, injectid: i32) -> String {
        name_by_id(&self.base().call_mech_target, injectid)
    }

    fn decode_inject(
        &mut self,
        src: &str,
        suffix: &str,
        tp: i32,
        decoder: &mut dyn Decoder,
        glb: &mut Architecture,
    ) -> Result<i32> {
        let injectid = self.allocate_inject(src, suffix, tp)?;
        self.get_payload_mut(injectid).decode(decoder)?;
        self.register_inject(injectid, glb)?;
        Ok(injectid)
    }

    fn decode_debug(&mut self, _decoder: &mut dyn Decoder) -> Result<()> {
        Ok(())
    }

    fn manual_call_fixup(&mut self, name: &str, snippetstring: &str, glb: &mut Architecture) -> Result<i32>;

    fn manual_call_other_fixup(
        &mut self,
        name: &str,
        outname: &str,
        inname: &[String],
        snippet: &str,
        glb: &mut Architecture,
    ) -> Result<i32>;

    fn get_cached_context(&mut self) -> &mut dyn InjectContext;

    fn get_behaviors(&self) -> &[Option<OpBehaviorRef>];
}

pub fn with_inject_library<T>(
    glb: &mut Architecture,
    body: impl FnOnce(&mut dyn PcodeInjectLibrary, &mut Architecture) -> Result<T>,
) -> Result<T> {
    let mut library = glb
        .pcodeinjectlib
        .take()
        .ok_or_else(|| Error::Lowlevel("missing p-code inject library".to_string()))?;
    let res = body(library.as_mut(), glb);
    glb.pcodeinjectlib = Some(library);
    res
}

pub fn decode_inject_in(
    glb: &mut Architecture,
    src: &str,
    suffix: &str,
    tp: i32,
    decoder: &mut dyn Decoder,
) -> Result<i32> {
    with_inject_library(glb, |library, glb| library.decode_inject(src, suffix, tp, decoder, glb))
}

pub fn evaluate_executable(glb: &mut Architecture, injectid: i32, input: &[u64]) -> Result<u64> {
    let mut payload = glb
        .pcodeinjectlib
        .as_deref_mut()
        .ok_or_else(|| Error::Lowlevel("missing p-code inject library".to_string()))?
        .take_payload(injectid);
    let res = ExecutablePcode::evaluate(payload.as_mut(), input, glb);
    glb.pcodeinjectlib
        .as_deref_mut()
        .expect("missing p-code inject library")
        .restore_payload(injectid, payload);
    res
}
