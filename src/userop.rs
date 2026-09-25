use std::collections::BTreeMap;
use std::sync::Arc;

use crate::architecture::Architecture;
use crate::database::Database;
use crate::define_id;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_FORMAT, ATTRIB_NAME, ATTRIB_SPACE, AttributeId, Decoder, ElementId};
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::pcodeinject::{
    CALLOTHERFIXUP_TYPE, ELEM_ADDR_PCODE, ELEM_CASE_PCODE, ELEM_DEFAULT_PCODE, ELEM_PCODE, ELEM_SIZE_PCODE,
    EXECUTABLEPCODE_TYPE, decode_inject_in, evaluate_executable, with_inject_library,
};
use crate::pcoderaw::VarnodeData;
use crate::space::SpaceRef;
use crate::types::{TypeId, TypeMetatype};
use crate::varnode::VarnodeId;

pub const ATTRIB_FARPOINTER: AttributeId = AttributeId::new("farpointer", 85);
pub const ATTRIB_INPUTOP: AttributeId = AttributeId::new("inputop", 86);
pub const ATTRIB_OUTPUTOP: AttributeId = AttributeId::new("outputop", 87);
pub const ATTRIB_USEROP: AttributeId = AttributeId::new("userop", 88);
pub const ELEM_CONSTRESOLVE: ElementId = ElementId::new("constresolve", 127);
pub const ELEM_JUMPASSIST: ElementId = ElementId::new("jumpassist", 128);
pub const ELEM_SEGMENTOP: ElementId = ElementId::new("segmentop", 129);

define_id!(UserOpId);

#[repr(u32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UserOpType {
    Unspecialized = 1,
    Injected = 2,
    VolatileRead = 3,
    VolatileWrite = 4,
    Segment = 5,
    Jumpassist = 6,
    StringData = 7,
    Datatype = 8,
}

#[derive(Clone, Debug)]
pub struct SegmentOpData {
    pub spc: Option<SpaceRef>,
    pub inject_id: i32,
    pub baseinsize: i32,
    pub innerinsize: i32,
    pub supportsfarpointer: bool,
    pub constresolve: VarnodeData,
}

impl SegmentOpData {
    pub fn get_space(&self) -> Option<&SpaceRef> {
        self.spc.as_ref()
    }

    pub fn has_far_pointer_support(&self) -> bool {
        self.supportsfarpointer
    }

    pub fn get_base_size(&self) -> i32 {
        self.baseinsize
    }

    pub fn get_inner_size(&self) -> i32 {
        self.innerinsize
    }

    pub fn get_resolve(&self) -> &VarnodeData {
        &self.constresolve
    }
}

#[derive(Clone, Debug)]
pub struct JumpAssistData {
    pub index2case: i32,
    pub index2addr: i32,
    pub defaultaddr: i32,
    pub calcsize: i32,
}

impl JumpAssistData {
    pub fn get_index2_case(&self) -> i32 {
        self.index2case
    }

    pub fn get_index2_addr(&self) -> i32 {
        self.index2addr
    }

    pub fn get_default_addr(&self) -> i32 {
        self.defaultaddr
    }

    pub fn get_calc_size(&self) -> i32 {
        self.calcsize
    }
}

#[derive(Clone, Debug)]
pub enum UserPcodeOpKind {
    Unspecialized,
    Datatype {
        out_type: Option<TypeId>,
        in_types: Vec<Option<TypeId>>,
    },
    Injected {
        injectid: u32,
    },
    VolatileRead,
    VolatileWrite,
    Segment(SegmentOpData),
    JumpAssist(JumpAssistData),
    InternalString,
}

#[derive(Clone, Debug)]
pub struct UserPcodeOp {
    pub name: String,
    pub tp: UserOpType,
    pub useropindex: i32,
    pub flags: u32,
    pub kind: UserPcodeOpKind,
}

fn global_sized_type(
    glb: &mut Architecture,
    data: &Funcdata,
    op: OpId,
    addr_vn: VarnodeId,
    size: i32,
) -> Result<Option<TypeId>> {
    let addr = data.vn(addr_vn).get_addr().clone();
    let usepoint = data.op(op).get_addr().clone();
    let mut vflags: u32 = 0;
    let entry = {
        let symboltab = glb.symboltab_ref()?;
        let global = symboltab
            .get_global_scope()
            .ok_or_else(|| Error::Lowlevel("missing global scope".to_string()))?;
        symboltab.scope_query_properties(global, &addr, size, &usepoint, &mut vflags)
    };
    match entry {
        None => Ok(None),
        Some(entry) => Database::entry_get_sized_type(glb, entry, &addr, size),
    }
}

fn lookup_unspecialized_index(glb: &Architecture, name: &str, unknown: &str, overloaded: &str) -> Result<i32> {
    let base = match glb.userops.get_op_by_name(name) {
        None => return Err(Error::Lowlevel(format!("{}{}", unknown, name))),
        Some(base) => base,
    };
    if base.tp != UserOpType::Unspecialized {
        return Err(Error::Lowlevel(format!("{}{}", overloaded, name)));
    }
    Ok(base.get_index())
}

impl UserPcodeOp {
    pub const ANNOTATION_ASSIGNMENT: u32 = 1;
    pub const NO_OPERATOR: u32 = 2;
    pub const DISPLAY_STRING: u32 = 4;

    pub const BUILTIN_STRINGDATA: u32 = 0x10000000;
    pub const BUILTIN_VOLATILE_READ: u32 = 0x10000001;
    pub const BUILTIN_VOLATILE_WRITE: u32 = 0x10000002;
    pub const BUILTIN_MEMCPY: u32 = 0x10000003;
    pub const BUILTIN_STRNCPY: u32 = 0x10000004;
    pub const BUILTIN_WCSNCPY: u32 = 0x10000005;

    pub fn new(nm: &str, tp: UserOpType, ind: i32, kind: UserPcodeOpKind) -> UserPcodeOp {
        UserPcodeOp {
            name: nm.to_string(),
            tp,
            useropindex: ind,
            flags: 0,
            kind,
        }
    }

    pub fn new_unspecialized(nm: &str, ind: i32) -> UserPcodeOp {
        UserPcodeOp::new(nm, UserOpType::Unspecialized, ind, UserPcodeOpKind::Unspecialized)
    }

    pub fn new_datatype(
        nm: &str,
        ind: i32,
        out: Option<TypeId>,
        in0: Option<TypeId>,
        in1: Option<TypeId>,
        in2: Option<TypeId>,
        in3: Option<TypeId>,
    ) -> UserPcodeOp {
        let in_types: Vec<Option<TypeId>> = [in0, in1, in2, in3].into_iter().filter(|tp| tp.is_some()).collect();
        UserPcodeOp::new(
            nm,
            UserOpType::Datatype,
            ind,
            UserPcodeOpKind::Datatype {
                out_type: out,
                in_types,
            },
        )
    }

    pub fn new_injected(nm: &str, ind: i32, injid: i32) -> UserPcodeOp {
        UserPcodeOp::new(
            nm,
            UserOpType::Injected,
            ind,
            UserPcodeOpKind::Injected { injectid: injid as u32 },
        )
    }

    pub fn new_volatile_read(nm: &str, functional: bool) -> UserPcodeOp {
        let mut res = UserPcodeOp::new(
            nm,
            UserOpType::VolatileRead,
            UserPcodeOp::BUILTIN_VOLATILE_READ as i32,
            UserPcodeOpKind::VolatileRead,
        );
        res.flags = if functional { 0 } else { UserPcodeOp::NO_OPERATOR };
        res
    }

    pub fn new_volatile_write(nm: &str, functional: bool) -> UserPcodeOp {
        let mut res = UserPcodeOp::new(
            nm,
            UserOpType::VolatileWrite,
            UserPcodeOp::BUILTIN_VOLATILE_WRITE as i32,
            UserPcodeOpKind::VolatileWrite,
        );
        res.flags = if functional {
            0
        } else {
            UserPcodeOp::ANNOTATION_ASSIGNMENT
        };
        res
    }

    pub fn new_segment(nm: &str, ind: i32) -> UserPcodeOp {
        UserPcodeOp::new(
            nm,
            UserOpType::Segment,
            ind,
            UserPcodeOpKind::Segment(SegmentOpData {
                spc: None,
                inject_id: -1,
                baseinsize: 0,
                innerinsize: 0,
                supportsfarpointer: false,
                constresolve: VarnodeData::default(),
            }),
        )
    }

    pub fn new_jump_assist() -> UserPcodeOp {
        UserPcodeOp::new(
            "",
            UserOpType::Jumpassist,
            0,
            UserPcodeOpKind::JumpAssist(JumpAssistData {
                index2case: -1,
                index2addr: -1,
                defaultaddr: -1,
                calcsize: -1,
            }),
        )
    }

    pub fn new_internal_string() -> UserPcodeOp {
        let mut res = UserPcodeOp::new(
            "stringdata",
            UserOpType::StringData,
            UserPcodeOp::BUILTIN_STRINGDATA as i32,
            UserPcodeOpKind::InternalString,
        );
        res.flags |= UserPcodeOp::DISPLAY_STRING;
        res
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_type(&self) -> UserOpType {
        self.tp
    }

    pub fn get_index(&self) -> i32 {
        self.useropindex
    }

    pub fn get_display(&self) -> u32 {
        self.flags & (UserPcodeOp::ANNOTATION_ASSIGNMENT | UserPcodeOp::NO_OPERATOR | UserPcodeOp::DISPLAY_STRING)
    }

    pub fn get_operator_name(&self, op: OpId, data: &Funcdata) -> String {
        match &self.kind {
            UserPcodeOpKind::VolatileRead => match data.op(op).get_out() {
                None => self.name.clone(),
                Some(out) => UserPcodeOp::append_size(&self.name, data.vn(out).get_size()),
            },
            UserPcodeOpKind::VolatileWrite => {
                let pcode_op = data.op(op);
                if pcode_op.num_input() < 3 {
                    return self.name.clone();
                }
                UserPcodeOp::append_size(&self.name, data.vn(pcode_op.get_in(2)).get_size())
            }
            _ => self.name.clone(),
        }
    }

    pub fn get_output_local(&self, op: OpId, data: &Funcdata, glb: &mut Architecture) -> Result<Option<TypeId>> {
        match &self.kind {
            UserPcodeOpKind::Datatype { out_type, .. } => Ok(*out_type),
            UserPcodeOpKind::VolatileRead => {
                let pcode_op = data.op(op);
                if !pcode_op.does_special_propagation() {
                    return Ok(None);
                }
                let addr_vn = pcode_op.get_in(1);
                let size = data
                    .vn(pcode_op.get_out().expect("volatile read without output"))
                    .get_size();
                global_sized_type(glb, data, op, addr_vn, size)
            }
            UserPcodeOpKind::InternalString => {
                let out = data.op(op).get_out().expect("stringdata op without output");
                Ok(Some(data.vn(out).get_type()))
            }
            _ => Ok(None),
        }
    }

    pub fn get_input_local(
        &self,
        op: OpId,
        slot: i32,
        data: &Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        match &self.kind {
            UserPcodeOpKind::Datatype { in_types, .. } => {
                let index = slot - 1;
                if index >= 0 && (index as usize) < in_types.len() {
                    return Ok(in_types[index as usize]);
                }
                Ok(None)
            }
            UserPcodeOpKind::VolatileWrite => {
                let pcode_op = data.op(op);
                if !pcode_op.does_special_propagation() || slot != 2 {
                    return Ok(None);
                }
                let addr_vn = pcode_op.get_in(1);
                let size = data.vn(pcode_op.get_in(2)).get_size();
                global_sized_type(glb, data, op, addr_vn, size)
            }
            _ => Ok(None),
        }
    }

    pub fn extract_annotation_size(&self, _vn: VarnodeId, op: OpId, data: &Funcdata) -> Result<i32> {
        match &self.kind {
            UserPcodeOpKind::VolatileRead => match data.op(op).get_out() {
                Some(outvn) => Ok(data.vn(outvn).get_size()),
                None => Ok(1),
            },
            UserPcodeOpKind::VolatileWrite => Ok(data.vn(data.op(op).get_in(2)).get_size()),
            _ => Err(Error::Lowlevel(format!(
                "Unexpected annotation input for CALLOTHER {}",
                self.name
            ))),
        }
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        match self.tp {
            UserOpType::Injected => self.decode_injected(decoder, glb),
            UserOpType::Segment => self.decode_segment(decoder, glb),
            UserOpType::Jumpassist => self.decode_jump_assist(decoder, glb),
            _ => Ok(()),
        }
    }

    fn decode_injected(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let injectid = decode_inject_in(glb, "userop", "", CALLOTHERFIXUP_TYPE, decoder)?;
        self.kind = UserPcodeOpKind::Injected {
            injectid: injectid as u32,
        };
        self.name = glb
            .pcodeinjectlib
            .as_deref()
            .ok_or_else(|| Error::Lowlevel("missing p-code inject library".to_string()))?
            .get_call_other_target(injectid);
        self.useropindex = lookup_unspecialized_index(
            glb,
            &self.name,
            "Unknown userop name in <callotherfixup>: ",
            "<callotherfixup> overloads userop with another purpose: ",
        )?;
        Ok(())
    }

    fn decode_segment(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_SEGMENTOP)?;
        let mut data = match &self.kind {
            UserPcodeOpKind::Segment(segment) => segment.clone(),
            _ => panic!("user op {} is not a segment op", self.name),
        };
        data.spc = None;
        data.inject_id = -1;
        data.baseinsize = 0;
        data.innerinsize = 0;
        data.supportsfarpointer = false;
        self.name = "segment".to_string();
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_SPACE {
                data.spc = Some(decoder.read_space()?);
            } else if attrib_id == ATTRIB_FARPOINTER {
                data.supportsfarpointer = true;
            } else if attrib_id == ATTRIB_USEROP {
                self.name = decoder.read_string()?;
            }
        }
        if data.spc.is_none() {
            self.kind = UserPcodeOpKind::Segment(data);
            return Err(Error::Lowlevel("<segmentop> expecting space attribute".to_string()));
        }
        let otherop = match glb.userops.get_op_by_name(&self.name) {
            None => {
                self.kind = UserPcodeOpKind::Segment(data);
                return Err(Error::Lowlevel(format!("<segmentop> unknown userop {}", self.name)));
            }
            Some(otherop) => otherop.clone(),
        };
        self.useropindex = otherop.get_index();
        if otherop.tp != UserOpType::Unspecialized {
            self.kind = UserPcodeOpKind::Segment(data);
            return Err(Error::Lowlevel(format!("Redefining userop {}", self.name)));
        }

        let decode_result = self.decode_segment_children(decoder, glb, &mut data);
        self.kind = UserPcodeOpKind::Segment(data.clone());
        decode_result?;
        decoder.close_element(elem_id)?;
        if data.inject_id < 0 {
            return Err(Error::Lowlevel("Missing <pcode> child in <segmentop> tag".to_string()));
        }
        let (size_output, input_sizes) = {
            let library = glb
                .pcodeinjectlib
                .as_deref()
                .ok_or_else(|| Error::Lowlevel("missing p-code inject library".to_string()))?;
            let payload = library.get_payload(data.inject_id);
            let sizes: Vec<u32> = payload.base().inputlist.iter().map(|param| param.get_size()).collect();
            (payload.size_output(), sizes)
        };
        if size_output != 1 {
            return Err(Error::Lowlevel(
                "<pcode> child of <segmentop> tag must declare one <output>".to_string(),
            ));
        }
        if input_sizes.len() == 1 {
            data.innerinsize = input_sizes[0] as i32;
        } else if input_sizes.len() == 2 {
            data.baseinsize = input_sizes[0] as i32;
            data.innerinsize = input_sizes[1] as i32;
        } else {
            return Err(Error::Lowlevel(
                "<pcode> child of <segmentop> tag must declare one or two <input> tags".to_string(),
            ));
        }
        self.kind = UserPcodeOpKind::Segment(data);
        Ok(())
    }

    fn decode_segment_children(
        &self,
        decoder: &mut dyn Decoder,
        glb: &mut Architecture,
        data: &mut SegmentOpData,
    ) -> Result<()> {
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_CONSTRESOLVE {
                decoder.open_element()?;
                if decoder.peek_element()? != 0 {
                    let (addr, sz) = crate::address::Address::decode_size(decoder)?;
                    data.constresolve.space = addr.get_space().cloned();
                    data.constresolve.offset = addr.get_offset();
                    data.constresolve.size = sz as u32;
                }
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_PCODE {
                let nm = format!("{}_pcode", self.name);
                let source = "cspec";
                data.inject_id = decode_inject_in(glb, source, &nm, EXECUTABLEPCODE_TYPE, decoder)?;
            }
        }
        Ok(())
    }

    fn decode_jump_assist(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_JUMPASSIST)?;
        self.name = decoder.read_string_attr(ATTRIB_NAME)?;
        let mut assist = JumpAssistData {
            index2case: -1,
            index2addr: -1,
            defaultaddr: -1,
            calcsize: -1,
        };
        let children = self.decode_jump_assist_children(decoder, glb, &mut assist);
        self.kind = UserPcodeOpKind::JumpAssist(assist.clone());
        children?;
        decoder.close_element(elem_id)?;

        if assist.index2addr == -1 {
            return Err(Error::Lowlevel(format!(
                "userop: {} is missing <addr_pcode>",
                self.name
            )));
        }
        if assist.defaultaddr == -1 {
            return Err(Error::Lowlevel(format!(
                "userop: {} is missing <default_pcode>",
                self.name
            )));
        }
        self.useropindex = lookup_unspecialized_index(
            glb,
            &self.name,
            "Unknown userop name in <jumpassist>: ",
            "<jumpassist> overloads userop with another purpose: ",
        )?;
        Ok(())
    }

    fn decode_jump_assist_children(
        &self,
        decoder: &mut dyn Decoder,
        glb: &mut Architecture,
        assist: &mut JumpAssistData,
    ) -> Result<()> {
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_CASE_PCODE {
                if assist.index2case != -1 {
                    return Err(Error::Lowlevel("Too many <case_pcode> tags".to_string()));
                }
                assist.index2case = decode_inject_in(
                    glb,
                    "jumpassistop",
                    &format!("{}_index2case", self.name),
                    EXECUTABLEPCODE_TYPE,
                    decoder,
                )?;
            } else if sub_id == ELEM_ADDR_PCODE {
                if assist.index2addr != -1 {
                    return Err(Error::Lowlevel("Too many <addr_pcode> tags".to_string()));
                }
                assist.index2addr = decode_inject_in(
                    glb,
                    "jumpassistop",
                    &format!("{}_index2addr", self.name),
                    EXECUTABLEPCODE_TYPE,
                    decoder,
                )?;
            } else if sub_id == ELEM_DEFAULT_PCODE {
                if assist.defaultaddr != -1 {
                    return Err(Error::Lowlevel("Too many <default_pcode> tags".to_string()));
                }
                assist.defaultaddr = decode_inject_in(
                    glb,
                    "jumpassistop",
                    &format!("{}_defaultaddr", self.name),
                    EXECUTABLEPCODE_TYPE,
                    decoder,
                )?;
            } else if sub_id == ELEM_SIZE_PCODE {
                if assist.calcsize != -1 {
                    return Err(Error::Lowlevel("Too many <size_pcode> tags".to_string()));
                }
                assist.calcsize = decode_inject_in(
                    glb,
                    "jumpassistop",
                    &format!("{}_calcsize", self.name),
                    EXECUTABLEPCODE_TYPE,
                    decoder,
                )?;
            }
        }
        Ok(())
    }

    pub fn append_size(base: &str, size: i32) -> String {
        match size {
            1 => format!("{}_1", base),
            2 => format!("{}_2", base),
            4 => format!("{}_4", base),
            8 => format!("{}_8", base),
            _ => format!("{}_{}", base, size),
        }
    }

    pub fn get_inject_id(&self) -> u32 {
        match &self.kind {
            UserPcodeOpKind::Injected { injectid } => *injectid,
            _ => panic!("user op {} is not an injected op", self.name),
        }
    }

    pub fn as_segment(&self) -> Option<&SegmentOpData> {
        match &self.kind {
            UserPcodeOpKind::Segment(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn as_jump_assist(&self) -> Option<&JumpAssistData> {
        match &self.kind {
            UserPcodeOpKind::JumpAssist(assist) => Some(assist),
            _ => None,
        }
    }

    pub fn get_num_variable_terms(&self) -> i32 {
        match &self.kind {
            UserPcodeOpKind::Segment(segment) => {
                if segment.baseinsize != 0 {
                    return 2;
                }
                1
            }
            _ => panic!("user op {} is not a term pattern op", self.name),
        }
    }

    pub fn unify(
        &self,
        data: &mut Funcdata,
        op: OpId,
        bindlist: &mut Vec<Option<VarnodeId>>,
        glb: &mut Architecture,
    ) -> bool {
        let segment = self.as_segment().expect("unify on a non-segment user op");
        if data.op(op).code() != OpCode::Callother {
            return false;
        }
        if data.vn(data.op(op).get_in(0)).get_offset() != self.useropindex as i64 as u64 {
            return false;
        }
        if data.op(op).num_input() != 3 {
            return false;
        }
        while bindlist.len() < 2 {
            bindlist.push(None);
        }
        let mut innervn = data.op(op).get_in(1);
        if segment.baseinsize != 0 {
            let mut basevn = data.op(op).get_in(1);
            innervn = data.op(op).get_in(2);
            if data.vn(basevn).is_constant() {
                let offset = data.vn(basevn).get_offset();
                basevn = data.new_constant(segment.baseinsize, offset, glb);
            }
            bindlist[0] = Some(basevn);
        } else {
            bindlist[0] = None;
        }
        if data.vn(innervn).is_constant() {
            let offset = data.vn(innervn).get_offset();
            innervn = data.new_constant(segment.innerinsize, offset, glb);
        }
        bindlist[1] = Some(innervn);
        true
    }

    pub fn execute(&self, input: &[u64], glb: &mut Architecture) -> Result<u64> {
        let segment = self.as_segment().expect("execute on a non-segment user op");
        evaluate_executable(glb, segment.inject_id, input)
    }
}

#[derive(Clone, Debug, Default)]
pub struct UserOpManage {
    pub useroplist: Vec<Option<Arc<UserPcodeOp>>>,
    pub builtinmap: BTreeMap<u32, Arc<UserPcodeOp>>,
    pub useropmap: BTreeMap<String, Arc<UserPcodeOp>>,
    pub segmentop: Vec<Option<Arc<UserPcodeOp>>>,
}

impl UserOpManage {
    pub fn new() -> UserOpManage {
        UserOpManage::default()
    }

    pub fn register_op(&mut self, op: UserPcodeOp) -> Result<()> {
        let ind = op.get_index();
        if ind < 0 {
            return Err(Error::Lowlevel("UserOp not assigned an index".to_string()));
        }
        if let Some(other) = self.useropmap.get(op.get_name())
            && other.get_index() != ind
        {
            return Err(Error::Lowlevel(format!(
                "Conflicting indices for userop name {}",
                op.get_name()
            )));
        }
        while self.useroplist.len() <= ind as usize {
            self.useroplist.push(None);
        }
        if let Some(existing) = &self.useroplist[ind as usize]
            && existing.get_name() != op.get_name()
        {
            return Err(Error::Lowlevel(format!(
                "User op {} has same index as {}",
                op.get_name(),
                existing.get_name()
            )));
        }
        let op = Arc::new(op);
        self.useroplist[ind as usize] = Some(op.clone());
        self.useropmap.insert(op.get_name().to_string(), op.clone());

        if let Some(segment) = op.as_segment() {
            let index = segment
                .get_space()
                .ok_or_else(|| Error::Lowlevel("<segmentop> expecting space attribute".to_string()))?
                .get_index() as usize;
            while self.segmentop.len() <= index {
                self.segmentop.push(None);
            }
            if self.segmentop[index].is_some() {
                return Err(Error::Lowlevel(
                    "Multiple segmentops defined for same space".to_string(),
                ));
            }
            self.segmentop[index] = Some(op.clone());
        }
        Ok(())
    }

    pub fn initialize(glb: &mut Architecture) -> Result<()> {
        let mut basicops = Vec::new();
        glb.translate
            .as_deref()
            .ok_or_else(|| Error::Lowlevel("missing translator".to_string()))?
            .get_user_op_names(&mut basicops);
        for (index, name) in basicops.iter().enumerate() {
            if name.is_empty() {
                continue;
            }
            let userop = UserPcodeOp::new_unspecialized(name, index as i32);
            glb.userops.register_op(userop)?;
        }
        Ok(())
    }

    pub fn num_segment_ops(&self) -> i32 {
        self.segmentop.len() as i32
    }

    pub fn get_op(&self, index: u32) -> Option<&Arc<UserPcodeOp>> {
        if (index as usize) < self.useroplist.len() {
            return self.useroplist[index as usize].as_ref();
        }
        self.builtinmap.get(&index)
    }

    pub fn get_op_by_name(&self, nm: &str) -> Option<&Arc<UserPcodeOp>> {
        self.useropmap.get(nm)
    }

    pub fn register_builtin(glb: &mut Architecture, index: u32) -> Result<Arc<UserPcodeOp>> {
        if let Some(existing) = glb.userops.builtinmap.get(&index) {
            return Ok(existing.clone());
        }
        let res = match index {
            UserPcodeOp::BUILTIN_STRINGDATA => UserPcodeOp::new_internal_string(),
            UserPcodeOp::BUILTIN_VOLATILE_READ => UserPcodeOp::new_volatile_read("read_volatile", false),
            UserPcodeOp::BUILTIN_VOLATILE_WRITE => UserPcodeOp::new_volatile_write("write_volatile", false),
            UserPcodeOp::BUILTIN_MEMCPY | UserPcodeOp::BUILTIN_STRNCPY | UserPcodeOp::BUILTIN_WCSNCPY => {
                let word_size = glb
                    .manager
                    .get_default_data_space()
                    .ok_or_else(|| Error::Lowlevel("missing default data space".to_string()))?
                    .get_word_size();
                let types = glb
                    .types
                    .as_deref_mut()
                    .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?;
                let ptr_size = types.get_size_of_pointer();
                let element_type = match index {
                    UserPcodeOp::BUILTIN_MEMCPY => types.get_type_void()?,
                    UserPcodeOp::BUILTIN_STRNCPY => {
                        let char_size = types.get_size_of_char();
                        types.get_type_char(char_size)?
                    }
                    _ => {
                        let wchar_size = types.get_size_of_wchar();
                        types.get_type_char(wchar_size)?
                    }
                };
                let ptr_type = types.get_type_pointer(ptr_size, element_type, word_size)?;
                let int_type = types.get_base(4, TypeMetatype::Int)?;
                let name = match index {
                    UserPcodeOp::BUILTIN_MEMCPY => "builtin_memcpy",
                    UserPcodeOp::BUILTIN_STRNCPY => "builtin_strncpy",
                    _ => "builtin_wcsncpy",
                };
                UserPcodeOp::new_datatype(
                    name,
                    index as i32,
                    Some(ptr_type),
                    Some(ptr_type),
                    Some(ptr_type),
                    Some(int_type),
                    None,
                )
            }
            _ => return Err(Error::Lowlevel("Bad built-in userop id".to_string())),
        };
        let res = Arc::new(res);
        glb.userops.builtinmap.insert(index, res.clone());
        Ok(res)
    }

    pub fn get_segment_op(&self, index: i32) -> Option<&Arc<UserPcodeOp>> {
        if index as usize >= self.segmentop.len() {
            return None;
        }
        self.segmentop[index as usize].as_ref()
    }

    pub fn decode_segment_op(decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let mut s_op = UserPcodeOp::new_segment("", glb.userops.useroplist.len() as i32);
        s_op.decode(decoder, glb)?;
        glb.userops.register_op(s_op)
    }

    pub fn decode_volatile(decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let mut read_op_name = String::new();
        let mut write_op_name = String::new();
        let mut functional_display = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_INPUTOP {
                read_op_name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_OUTPUTOP {
                write_op_name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_FORMAT {
                let format = decoder.read_string()?;
                if format == "functional" {
                    functional_display = true;
                }
            }
        }
        if read_op_name.is_empty() || write_op_name.is_empty() {
            return Err(Error::Lowlevel(
                "Missing inputop/outputop attributes in <volatile> element".to_string(),
            ));
        }
        let manage = &mut glb.userops;
        if manage.builtinmap.contains_key(&UserPcodeOp::BUILTIN_VOLATILE_READ) {
            return Err(Error::Lowlevel(
                "read_volatile user-op registered more than once".to_string(),
            ));
        }
        if manage.builtinmap.contains_key(&UserPcodeOp::BUILTIN_VOLATILE_WRITE) {
            return Err(Error::Lowlevel(
                "write_volatile user-op registered more than once".to_string(),
            ));
        }
        let vr_op = UserPcodeOp::new_volatile_read(&read_op_name, functional_display);
        manage
            .builtinmap
            .insert(UserPcodeOp::BUILTIN_VOLATILE_READ, Arc::new(vr_op));
        let vw_op = UserPcodeOp::new_volatile_write(&write_op_name, functional_display);
        manage
            .builtinmap
            .insert(UserPcodeOp::BUILTIN_VOLATILE_WRITE, Arc::new(vw_op));
        Ok(())
    }

    pub fn decode_call_other_fixup(decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let mut op = UserPcodeOp::new_injected("", 0, 0);
        op.decode(decoder, glb)?;
        glb.userops.register_op(op)
    }

    pub fn decode_jump_assist(decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let mut op = UserPcodeOp::new_jump_assist();
        op.decode(decoder, glb)?;
        glb.userops.register_op(op)
    }

    pub fn manual_call_other_fixup(
        useropname: &str,
        outname: &str,
        inname: &[String],
        snippet: &str,
        glb: &mut Architecture,
    ) -> Result<()> {
        let userop_index = {
            let userop = match glb.userops.get_op_by_name(useropname) {
                None => return Err(Error::Lowlevel(format!("Unknown userop: {}", useropname))),
                Some(userop) => userop,
            };
            if userop.tp != UserOpType::Unspecialized {
                return Err(Error::Lowlevel(format!("Cannot fixup userop: {}", useropname)));
            }
            userop.get_index()
        };
        let injectid = with_inject_library(glb, |library, glb| {
            library.manual_call_other_fixup(useropname, outname, inname, snippet, glb)
        })?;
        let op = UserPcodeOp::new_injected(useropname, userop_index, injectid);
        glb.userops.register_op(op)
    }
}
