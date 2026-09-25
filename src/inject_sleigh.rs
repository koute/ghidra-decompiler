use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::{Arc, OnceLock};

use crate::address::Address;
use crate::architecture::Architecture;
use crate::context::{ParserContext, ParserWalkerChange};
use crate::error::{Error, Result};
use crate::marshal::{ATTRIB_CONTENT, ATTRIB_NAME, ATTRIB_TYPE, Decoder, ELEM_TARGET, Encoder, XmlDecode, XmlEncode};
use crate::opbehavior::OpBehaviorRef;
use crate::pcodeinject::{
    ATTRIB_TARGETOP, CALLFIXUP_TYPE, CALLMECHANISM_TYPE, CALLOTHERFIXUP_TYPE, ELEM_ADDR_PCODE, ELEM_BODY,
    ELEM_CALLFIXUP, ELEM_CALLOTHERFIXUP, ELEM_CASE_PCODE, ELEM_DEFAULT_PCODE, ELEM_INJECT, ELEM_INJECTDEBUG, ELEM_INST,
    ELEM_PAYLOAD, ELEM_PCODE, ELEM_SIZE_PCODE, EXECUTABLEPCODE_TYPE, ExecutablePcode, InjectContext, InjectContextBase,
    InjectParameter, InjectPayload, InjectPayloadBase, PcodeInjectLibrary, PcodeInjectLibraryBase,
};
use crate::pcodeparse::PcodeSnippet;
use crate::semantics::ConstructTpl;
use crate::sleigh::PcodeCacher;
use crate::sleigh_arch::BehaviorCell;
use crate::slghsymbol::SymbolTable;
use crate::space::SpaceRef;
use crate::translate::{PcodeEmit, UniqueLayout};
use crate::xml::{self, Document};

#[derive(Clone, Debug)]
pub struct InjectEnvironment {
    pub const_space: SpaceRef,
    pub uniq_space: SpaceRef,
    pub bitrange_ea: u64,
}

#[derive(Debug, Default)]
pub struct InjectContextSleigh {
    pub base: InjectContextBase,
    pub cacher: PcodeCacher,
    pub pos: Option<ParserContext>,
}

impl InjectContextSleigh {
    pub fn new() -> InjectContextSleigh {
        InjectContextSleigh::default()
    }
}

impl InjectContext for InjectContextSleigh {
    fn base(&self) -> &InjectContextBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut InjectContextBase {
        &mut self.base
    }

    fn encode(&self, _encoder: &mut dyn Encoder) -> Result<()> {
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct SleighPayloadData {
    pub tpl: Option<ConstructTpl>,
    pub parsestring: String,
    pub env: Option<InjectEnvironment>,
    pub cacher: PcodeCacher,
    pub pos: Option<ParserContext>,
}

pub type SleighPayloadRef = Arc<Mutex<SleighPayloadData>>;

fn check_parameter_restrictions(
    con: &InjectContextBase,
    inputlist: &[InjectParameter],
    output: &[InjectParameter],
    source: &str,
) -> Result<()> {
    if inputlist.len() != con.inputlist.len() {
        return Err(Error::Lowlevel(format!(
            "Injection parameter list has different number of parameters than p-code operation: {source}"
        )));
    }
    for (param, data) in inputlist.iter().zip(con.inputlist.iter()) {
        let sz = param.get_size();
        if sz != 0 && sz != data.size {
            return Err(Error::Lowlevel(format!(
                "P-code input parameter size does not match injection specification: {source}"
            )));
        }
    }
    if output.len() != con.output.len() {
        return Err(Error::Lowlevel(format!(
            "Injection output does not match output of p-code operation: {source}"
        )));
    }
    for (param, data) in output.iter().zip(con.output.iter()) {
        let sz = param.get_size();
        if sz != 0 && sz != data.size {
            return Err(Error::Lowlevel(format!(
                "P-code output size does not match injection specification: {source}"
            )));
        }
    }
    Ok(())
}

fn setup_parameters(
    con: &InjectContextBase,
    walker: &mut ParserWalkerChange<'_>,
    inputlist: &[InjectParameter],
    output: &[InjectParameter],
    source: &str,
) -> Result<()> {
    check_parameter_restrictions(con, inputlist, output, source)?;
    for (param, data) in inputlist.iter().zip(con.inputlist.iter()) {
        walker.allocate_operand(param.get_index())?;
        let hand = walker.get_parent_handle_mut();
        hand.space = data.space.clone();
        hand.offset_offset = data.offset;
        hand.size = data.size;
        hand.offset_space = None;
        walker.pop_operand();
    }
    for (param, data) in output.iter().zip(con.output.iter()) {
        walker.allocate_operand(param.get_index())?;
        let hand = walker.get_parent_handle_mut();
        hand.space = data.space.clone();
        hand.offset_offset = data.offset;
        hand.size = data.size;
        hand.offset_space = None;
        walker.pop_operand();
    }
    Ok(())
}

fn inject_template(
    data: &SleighPayloadRef,
    base: &InjectPayloadBase,
    source: &str,
    context: &mut dyn InjectContext,
    emit: &mut dyn PcodeEmit,
) -> Result<()> {
    let mut guard = data.lock().expect("poisoned payload lock");
    let SleighPayloadData {
        tpl, env, cacher, pos, ..
    } = &mut *guard;
    cacher.clear();
    let con = context.base();
    let pos = pos
        .as_mut()
        .ok_or_else(|| Error::Lowlevel("injection payload has no parser context".to_string()))?;
    pos.set_addr(&con.baseaddr);
    pos.set_naddr(&con.nextaddr);
    pos.set_calladdr(&con.calladdr);
    let symtab = SymbolTable::new();
    let mut walker = ParserWalkerChange::new(pos, &symtab);
    walker.deallocate_state();
    setup_parameters(con, &mut walker, &base.inputlist, &base.output, source)?;
    let env = env
        .as_ref()
        .ok_or_else(|| Error::Lowlevel("injection payload is not compiled".to_string()))?;
    let tpl = tpl
        .as_ref()
        .ok_or_else(|| Error::Lowlevel("injection payload is not compiled".to_string()))?;
    cacher.build_injection(
        walker.view(),
        tpl,
        env.const_space.clone(),
        env.uniq_space.clone(),
        env.bitrange_ea,
        &con.baseaddr,
        emit,
    )
}

fn print_payload_template(data: &SleighPayloadRef, out: &mut String) {
    let mut encoder = XmlEncode::new(true);
    if let Some(tpl) = data.lock().expect("poisoned payload lock").tpl.as_ref() {
        tpl.encode(&mut encoder, -1);
    }
    out.push_str(encoder.as_str());
}

fn decode_body(data: &SleighPayloadRef, dynamic: bool, source: &str, decoder: &mut dyn Decoder) -> Result<()> {
    let elem_id = decoder.open_element()?;
    if elem_id == ELEM_BODY {
        data.lock().expect("poisoned payload lock").parsestring = decoder.read_string_attr(ATTRIB_CONTENT)?;
        decoder.close_element(elem_id)?;
    }
    if data.lock().expect("poisoned payload lock").parsestring.is_empty() && !dynamic {
        return Err(Error::Lowlevel(format!("Missing <body> subtag in <pcode>: {source}")));
    }
    Ok(())
}

pub struct InjectPayloadSleigh {
    pub base: InjectPayloadBase,
    pub data: SleighPayloadRef,
    pub source: String,
}

impl InjectPayloadSleigh {
    pub fn new(src: &str, nm: &str, tp: i32) -> InjectPayloadSleigh {
        let mut base = InjectPayloadBase::new(nm, tp);
        base.paramshift = 0;
        InjectPayloadSleigh {
            base,
            data: Arc::new(Mutex::new(SleighPayloadData::default())),
            source: src.to_string(),
        }
    }

    pub fn decode_body(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        decode_body(&self.data, self.base.dynamic, &self.source, decoder)
    }

    pub fn check_parameter_restrictions(
        con: &InjectContextBase,
        inputlist: &[InjectParameter],
        output: &[InjectParameter],
        source: &str,
    ) -> Result<()> {
        check_parameter_restrictions(con, inputlist, output, source)
    }

    pub fn setup_parameters(
        con: &InjectContextBase,
        walker: &mut ParserWalkerChange<'_>,
        inputlist: &[InjectParameter],
        output: &[InjectParameter],
        source: &str,
    ) -> Result<()> {
        setup_parameters(con, walker, inputlist, output, source)
    }
}

impl InjectPayload for InjectPayloadSleigh {
    fn base(&self) -> &InjectPayloadBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut InjectPayloadBase {
        &mut self.base
    }

    fn inject(&self, context: &mut dyn InjectContext, emit: &mut dyn PcodeEmit) -> Result<()> {
        inject_template(&self.data, &self.base, &self.source, context, emit)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_PCODE)?;
        self.base.decode_payload_attributes(decoder)?;
        self.base.decode_payload_params(decoder)?;
        self.decode_body(decoder)?;
        decoder.close_element(elem_id)
    }

    fn print_template(&self, out: &mut String) {
        print_payload_template(&self.data, out)
    }

    fn get_source(&self) -> String {
        self.source.clone()
    }
}

pub struct InjectPayloadCallfixup {
    pub payload: InjectPayloadSleigh,
    pub target_symbol_names: Vec<String>,
}

impl InjectPayloadCallfixup {
    pub fn new(source_name: &str) -> InjectPayloadCallfixup {
        InjectPayloadCallfixup {
            payload: InjectPayloadSleigh::new(source_name, "unknown", CALLFIXUP_TYPE),
            target_symbol_names: Vec::new(),
        }
    }
}

impl InjectPayload for InjectPayloadCallfixup {
    fn base(&self) -> &InjectPayloadBase {
        &self.payload.base
    }

    fn base_mut(&mut self) -> &mut InjectPayloadBase {
        &mut self.payload.base
    }

    fn inject(&self, context: &mut dyn InjectContext, emit: &mut dyn PcodeEmit) -> Result<()> {
        self.payload.inject(context, emit)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CALLFIXUP)?;
        self.payload.base.name = decoder.read_string_attr(ATTRIB_NAME)?;
        let mut pcode_subtag = false;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_PCODE {
                self.payload.base.decode_payload_attributes(decoder)?;
                self.payload.base.decode_payload_params(decoder)?;
                self.payload.decode_body(decoder)?;
                pcode_subtag = true;
            } else if sub_id == ELEM_TARGET {
                self.target_symbol_names.push(decoder.read_string_attr(ATTRIB_NAME)?);
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)?;
        if !pcode_subtag {
            return Err(Error::Lowlevel(format!(
                "<callfixup> is missing <pcode> subtag: {}",
                self.payload.base.name
            )));
        }
        Ok(())
    }

    fn print_template(&self, out: &mut String) {
        self.payload.print_template(out)
    }

    fn get_source(&self) -> String {
        self.payload.get_source()
    }
}

pub struct InjectPayloadCallother {
    pub payload: InjectPayloadSleigh,
}

impl InjectPayloadCallother {
    pub fn new(source_name: &str) -> InjectPayloadCallother {
        InjectPayloadCallother {
            payload: InjectPayloadSleigh::new(source_name, "unknown", CALLOTHERFIXUP_TYPE),
        }
    }
}

impl InjectPayload for InjectPayloadCallother {
    fn base(&self) -> &InjectPayloadBase {
        &self.payload.base
    }

    fn base_mut(&mut self) -> &mut InjectPayloadBase {
        &mut self.payload.base
    }

    fn inject(&self, context: &mut dyn InjectContext, emit: &mut dyn PcodeEmit) -> Result<()> {
        self.payload.inject(context, emit)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CALLOTHERFIXUP)?;
        self.payload.base.name = decoder.read_string_attr(ATTRIB_TARGETOP)?;
        let sub_id = decoder.open_element()?;
        if sub_id != ELEM_PCODE {
            return Err(Error::Lowlevel(
                "<callotherfixup> does not contain a <pcode> tag".to_string(),
            ));
        }
        self.payload.base.decode_payload_attributes(decoder)?;
        self.payload.base.decode_payload_params(decoder)?;
        self.payload.decode_body(decoder)?;
        decoder.close_element(sub_id)?;
        decoder.close_element(elem_id)
    }

    fn print_template(&self, out: &mut String) {
        self.payload.print_template(out)
    }

    fn get_source(&self) -> String {
        self.payload.get_source()
    }
}

pub struct ExecutablePcodeSleigh {
    pub executable: ExecutablePcode,
    pub data: SleighPayloadRef,
}

impl ExecutablePcodeSleigh {
    pub fn new(src: &str, nm: &str) -> ExecutablePcodeSleigh {
        ExecutablePcodeSleigh {
            executable: ExecutablePcode::new(src, nm),
            data: Arc::new(Mutex::new(SleighPayloadData::default())),
        }
    }
}

impl InjectPayload for ExecutablePcodeSleigh {
    fn base(&self) -> &InjectPayloadBase {
        &self.executable.base
    }

    fn base_mut(&mut self) -> &mut InjectPayloadBase {
        &mut self.executable.base
    }

    fn inject(&self, context: &mut dyn InjectContext, emit: &mut dyn PcodeEmit) -> Result<()> {
        inject_template(
            &self.data,
            &self.executable.base,
            &self.executable.get_source(),
            context,
            emit,
        )
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element()?;
        if elem_id != ELEM_PCODE
            && elem_id != ELEM_CASE_PCODE
            && elem_id != ELEM_ADDR_PCODE
            && elem_id != ELEM_DEFAULT_PCODE
            && elem_id != ELEM_SIZE_PCODE
        {
            return Err(Error::Decoder(
                "Expecting <pcode>, <case_pcode>, <addr_pcode>, <default_pcode>, or <size_pcode>".to_string(),
            ));
        }
        self.executable.base.decode_payload_attributes(decoder)?;
        self.executable.base.decode_payload_params(decoder)?;
        let sub_id = decoder.open_element_expect(ELEM_BODY)?;
        self.data.lock().expect("poisoned payload lock").parsestring = decoder.read_string_attr(ATTRIB_CONTENT)?;
        decoder.close_element(sub_id)?;
        decoder.close_element(elem_id)
    }

    fn print_template(&self, out: &mut String) {
        print_payload_template(&self.data, out)
    }

    fn get_source(&self) -> String {
        self.executable.get_source()
    }

    fn as_executable(&self) -> Option<&ExecutablePcode> {
        Some(&self.executable)
    }

    fn as_executable_mut(&mut self) -> Option<&mut ExecutablePcode> {
        Some(&mut self.executable)
    }
}

pub type DynamicPayloadRef = Arc<Mutex<BTreeMap<Address, Arc<Document>>>>;

pub struct InjectPayloadDynamic {
    pub base: InjectPayloadBase,
    pub addr_map: DynamicPayloadRef,
}

impl InjectPayloadDynamic {
    pub fn new(payload: &dyn InjectPayload) -> InjectPayloadDynamic {
        let mut base = InjectPayloadBase::new(&payload.get_name(), payload.get_type());
        base.dynamic = true;
        base.incidental_copy = payload.is_incidental_copy();
        base.paramshift = payload.get_param_shift();
        base.inputlist = payload.base().inputlist.clone();
        base.output = payload.base().output.clone();
        InjectPayloadDynamic {
            base,
            addr_map: Arc::new(Mutex::new(BTreeMap::new())),
        }
    }

    pub fn decode_entry(addr_map: &DynamicPayloadRef, decoder: &mut dyn Decoder) -> Result<()> {
        let addr = Address::decode(decoder)?;
        let sub_id = decoder.open_element_expect(ELEM_PAYLOAD)?;
        let content = decoder.read_string_attr(ATTRIB_CONTENT)?;
        match xml::xml_tree(content.as_bytes()) {
            Ok(doc) => {
                addr_map
                    .lock()
                    .expect("poisoned payload lock")
                    .insert(addr, Arc::new(doc));
            }
            Err(Error::Decoder(_)) => {
                return Err(Error::Lowlevel("Error decoding dynamic payload".to_string()));
            }
            Err(err) => return Err(err),
        }
        decoder.close_element(sub_id)
    }
}

impl InjectPayload for InjectPayloadDynamic {
    fn base(&self) -> &InjectPayloadBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut InjectPayloadBase {
        &mut self.base
    }

    fn inject(&self, context: &mut dyn InjectContext, emit: &mut dyn PcodeEmit) -> Result<()> {
        let map = self.addr_map.lock().expect("poisoned payload lock");
        let Some(doc) = map.get(&context.base().baseaddr) else {
            return Err(Error::Lowlevel("Missing dynamic inject".to_string()));
        };
        let el = doc.get_root().clone();
        let mut decoder = XmlDecode::with_root(None, el, 0);
        let root_id = decoder.open_element_expect(ELEM_INST)?;
        let addr = Address::decode(&mut decoder)?;
        while decoder.peek_element()? != 0 {
            emit.decode_op(&addr, &mut decoder)?;
        }
        decoder.close_element(root_id)
    }

    fn decode(&mut self, _decoder: &mut dyn Decoder) -> Result<()> {
        Err(Error::Lowlevel(
            "decode not supported for InjectPayloadDynamic".to_string(),
        ))
    }

    fn print_template(&self, out: &mut String) {
        out.push_str("dynamic");
    }

    fn get_source(&self) -> String {
        "dynamic".to_string()
    }
}

#[derive(Clone)]
enum PayloadHandle {
    Empty,
    Sleigh(SleighPayloadRef),
    Dynamic(DynamicPayloadRef),
}

pub struct PcodeInjectLibrarySleigh {
    pub base: PcodeInjectLibraryBase,
    pub behaviors: BehaviorCell,
    pub context_cache: InjectContextSleigh,
    env: InjectEnvironment,
    handles: Vec<PayloadHandle>,
}

impl PcodeInjectLibrarySleigh {
    pub fn new(glb: &mut Architecture) -> Result<PcodeInjectLibrarySleigh> {
        let translate = glb
            .translate
            .as_deref()
            .ok_or_else(|| Error::Lowlevel("Registering pcode snippet before language is instantiated".to_string()))?;
        let tempbase = translate.get_unique_start(UniqueLayout::Inject);
        let bitrange_ea = translate.get_unique_start(UniqueLayout::RuntimeBitrangeEa) as u64;
        let const_space = glb
            .manager
            .get_constant_space()
            .or_else(|| translate.manager().get_constant_space())
            .ok_or_else(|| Error::Lowlevel("missing constant space".to_string()))?;
        let uniq_space = glb
            .manager
            .get_unique_space()
            .or_else(|| translate.manager().get_unique_space())
            .ok_or_else(|| Error::Lowlevel("missing unique space".to_string()))?;
        Ok(PcodeInjectLibrarySleigh {
            base: PcodeInjectLibraryBase::new(tempbase),
            behaviors: new_behavior_cell(),
            context_cache: InjectContextSleigh::new(),
            env: InjectEnvironment {
                const_space,
                uniq_space,
                bitrange_ea,
            },
            handles: Vec::new(),
        })
    }

    pub fn behavior_cell(&self) -> BehaviorCell {
        self.behaviors.clone()
    }

    fn set_handle(&mut self, injectid: i32, handle: PayloadHandle) {
        let index = injectid as usize;
        if self.handles.len() <= index {
            self.handles.resize(index + 1, PayloadHandle::Empty);
        }
        self.handles[index] = handle;
    }

    fn handle(&self, injectid: i32) -> PayloadHandle {
        self.handles
            .get(injectid as usize)
            .cloned()
            .unwrap_or(PayloadHandle::Empty)
    }

    fn sleigh_data(&self, injectid: i32) -> Result<SleighPayloadRef> {
        match self.handle(injectid) {
            PayloadHandle::Sleigh(data) => Ok(data),
            _ => Err(Error::Lowlevel("inject payload is not a sleigh payload".to_string())),
        }
    }

    fn force_debug_dynamic(&mut self, injectid: i32) -> DynamicPayloadRef {
        let old_payload = self.take_payload(injectid);
        let new_payload = InjectPayloadDynamic::new(old_payload.as_ref());
        let addr_map = new_payload.addr_map.clone();
        self.restore_payload(injectid, Box::new(new_payload));
        self.set_handle(injectid, PayloadHandle::Dynamic(addr_map.clone()));
        addr_map
    }

    fn parse_inject(&mut self, injectid: i32, glb: &mut Architecture) -> Result<()> {
        let payload = self.get_payload(injectid);
        if payload.is_dynamic() {
            return Ok(());
        }
        let Some(sleigh) = glb.translate.as_deref().and_then(|trans| trans.as_sleigh()) else {
            return Err(Error::Lowlevel(
                "Registering pcode snippet before language is instantiated".to_string(),
            ));
        };
        let data = self.sleigh_data(injectid)?;
        let mut compiler = PcodeSnippet::new(sleigh.base());
        for param in payload.base().inputlist.iter() {
            compiler.add_operand(param.get_name(), param.get_index());
        }
        for param in payload.base().output.iter() {
            compiler.add_operand(param.get_name(), param.get_index());
        }
        let source = payload.get_source();
        let tp = payload.get_type();
        let mut payload_data = data.lock().expect("poisoned payload lock");
        if tp == EXECUTABLEPCODE_TYPE {
            compiler.set_unique_base(0x2000);
            if !compiler.parse_stream(payload_data.parsestring.as_bytes())? {
                return Err(Error::Lowlevel(format!(
                    "{source}: Unable to compile pcode: {}",
                    compiler.get_error_message()
                )));
            }
        } else {
            compiler.set_unique_base(self.base.tempbase);
            if !compiler.parse_stream(payload_data.parsestring.as_bytes())? {
                return Err(Error::Lowlevel(format!(
                    "{source}: Unable to compile pcode: {}",
                    compiler.get_error_message()
                )));
            }
            self.base.tempbase = compiler.get_unique_base();
        }
        payload_data.tpl = compiler.release_result();
        payload_data.parsestring = String::new();
        payload_data.env = Some(self.env.clone());
        if payload_data.pos.is_none() {
            let mut pos = ParserContext::new(0);
            pos.initialize(self.env.const_space.clone(), 8);
            payload_data.pos = Some(pos);
        }
        Ok(())
    }
}

impl PcodeInjectLibrary for PcodeInjectLibrarySleigh {
    fn base(&self) -> &PcodeInjectLibraryBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut PcodeInjectLibraryBase {
        &mut self.base
    }

    fn allocate_inject(&mut self, source_name: &str, name: &str, tp: i32) -> Result<i32> {
        let injectid = self.base.injection.len() as i32;
        let (payload, handle): (Box<dyn InjectPayload>, PayloadHandle) = if tp == CALLFIXUP_TYPE {
            let payload = InjectPayloadCallfixup::new(source_name);
            let data = payload.payload.data.clone();
            (Box::new(payload), PayloadHandle::Sleigh(data))
        } else if tp == CALLOTHERFIXUP_TYPE {
            let payload = InjectPayloadCallother::new(source_name);
            let data = payload.payload.data.clone();
            (Box::new(payload), PayloadHandle::Sleigh(data))
        } else if tp == EXECUTABLEPCODE_TYPE {
            let payload = ExecutablePcodeSleigh::new(source_name, name);
            let data = payload.data.clone();
            (Box::new(payload), PayloadHandle::Sleigh(data))
        } else {
            let payload = InjectPayloadSleigh::new(source_name, name, tp);
            let data = payload.data.clone();
            (Box::new(payload), PayloadHandle::Sleigh(data))
        };
        self.base.injection.push(Some(payload));
        self.set_handle(injectid, handle);
        Ok(injectid)
    }

    fn register_inject(&mut self, injectid: i32, glb: &mut Architecture) -> Result<()> {
        if self.get_payload(injectid).is_dynamic() {
            let old_payload = self.take_payload(injectid);
            let sub = InjectPayloadDynamic::new(old_payload.as_ref());
            let addr_map = sub.addr_map.clone();
            self.restore_payload(injectid, Box::new(sub));
            self.set_handle(injectid, PayloadHandle::Dynamic(addr_map));
        }
        let tp = self.get_payload(injectid).get_type();
        let name = self.get_payload(injectid).get_name();
        match tp {
            CALLFIXUP_TYPE => {
                self.register_call_fixup(&name, injectid)?;
                self.parse_inject(injectid, glb)
            }
            CALLOTHERFIXUP_TYPE => {
                self.register_call_other_fixup(&name, injectid)?;
                self.parse_inject(injectid, glb)
            }
            CALLMECHANISM_TYPE => {
                self.register_call_mechanism(&name, injectid)?;
                self.parse_inject(injectid, glb)
            }
            EXECUTABLEPCODE_TYPE => {
                self.register_exe_script(&name, injectid)?;
                self.parse_inject(injectid, glb)
            }
            _ => Err(Error::Lowlevel("Unknown p-code inject type".to_string())),
        }
    }

    fn decode_debug(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_INJECTDEBUG)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id != ELEM_INJECT {
                break;
            }
            let name = decoder.read_string_attr(ATTRIB_NAME)?;
            let tp = decoder.read_signed_integer_attr(ATTRIB_TYPE)? as i32;
            let id = self.get_payload_id(tp, &name);
            let addr_map = match self.handle(id) {
                PayloadHandle::Dynamic(addr_map) => addr_map,
                _ => self.force_debug_dynamic(id),
            };
            InjectPayloadDynamic::decode_entry(&addr_map, decoder)?;
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    fn manual_call_fixup(&mut self, name: &str, snippetstring: &str, glb: &mut Architecture) -> Result<i32> {
        let source_name = format!("(manual callfixup name=\"{name}\")");
        let injectid = self.allocate_inject(&source_name, name, CALLFIXUP_TYPE)?;
        self.sleigh_data(injectid)?
            .lock()
            .expect("poisoned payload lock")
            .parsestring = snippetstring.to_string();
        self.register_inject(injectid, glb)?;
        Ok(injectid)
    }

    fn manual_call_other_fixup(
        &mut self,
        name: &str,
        outname: &str,
        inname: &[String],
        snippet: &str,
        glb: &mut Architecture,
    ) -> Result<i32> {
        let source_name = format!("<manual callotherfixup name=\"{name}\")");
        let injectid = self.allocate_inject(&source_name, name, CALLOTHERFIXUP_TYPE)?;
        {
            let payload = self.get_payload_mut(injectid);
            let base = payload.base_mut();
            for input_name in inname.iter() {
                base.inputlist.push(InjectParameter::new(input_name, 0));
            }
            if !outname.is_empty() {
                base.output.push(InjectParameter::new(outname, 0));
            }
            base.order_parameters();
        }
        self.sleigh_data(injectid)?
            .lock()
            .expect("poisoned payload lock")
            .parsestring = snippet.to_string();
        self.register_inject(injectid, glb)?;
        Ok(injectid)
    }

    fn get_cached_context(&mut self) -> &mut dyn InjectContext {
        &mut self.context_cache
    }

    fn get_behaviors(&self) -> &[Option<OpBehaviorRef>] {
        match self.behaviors.get() {
            Some(list) => list,
            None => &[],
        }
    }
}

pub fn new_behavior_cell() -> BehaviorCell {
    Arc::new(OnceLock::new())
}
