use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use crate::address::{Address, SeqNum};
use crate::error::Result;
use crate::marshal::{ATTRIB_NAME, ATTRIB_SPACE, Decoder, ELEM_VOID};
use crate::opcodes::OpCode;
use crate::space::SpaceRef;
use crate::translate::{ATTRIB_CODE, AddrSpaceManager, ELEM_SPACEID};

#[derive(Clone, Debug, Default)]
pub struct VarnodeData {
    pub space: Option<SpaceRef>,
    pub offset: u64,
    pub size: u32,
}

fn space_key(space: &Option<SpaceRef>) -> Option<i32> {
    space.as_ref().map(|spc| spc.get_index())
}

impl VarnodeData {
    pub fn new(space: SpaceRef, offset: u64, size: u32) -> VarnodeData {
        VarnodeData {
            space: Some(space),
            offset,
            size,
        }
    }

    pub fn get_addr(&self) -> Address {
        Address::from_parts(self.space.clone(), self.offset)
    }

    pub fn get_space_from_const(&self, manager: &AddrSpaceManager) -> Option<SpaceRef> {
        if self.offset > i32::MAX as u64 {
            return None;
        }
        manager.get_space(self.offset as i32)
    }

    pub fn decode(decoder: &mut dyn Decoder) -> Result<VarnodeData> {
        let elem_id = decoder.open_element()?;
        let res = VarnodeData::decode_from_attributes(decoder)?;
        decoder.close_element(elem_id)?;
        Ok(res)
    }

    pub fn decode_from_attributes(decoder: &mut dyn Decoder) -> Result<VarnodeData> {
        let mut res = VarnodeData::default();
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_SPACE {
                let space = decoder.read_space()?;
                decoder.rewind_attributes();
                let mut size = res.size;
                res.offset = space.decode_attributes(decoder, &mut size)?;
                res.size = size;
                res.space = Some(space);
                break;
            } else if attrib_id == ATTRIB_NAME {
                let name = decoder.read_string()?;
                res = decoder.get_register(&name)?;
                break;
            }
        }
        Ok(res)
    }

    pub fn contains(&self, op2: &VarnodeData) -> bool {
        if space_key(&self.space) != space_key(&op2.space) {
            return false;
        }
        if op2.offset < self.offset {
            return false;
        }
        let self_end = self.offset.wrapping_add((self.size as u64).wrapping_sub(1));
        let op2_end = op2.offset.wrapping_add((op2.size as u64).wrapping_sub(1));
        if self_end < op2_end {
            return false;
        }
        true
    }

    pub fn is_contiguous(&self, lo: &VarnodeData) -> bool {
        if space_key(&self.space) != space_key(&lo.space) {
            return false;
        }
        let Some(space) = &self.space else {
            return false;
        };
        if space.is_big_endian() {
            let nextoff = space.wrap_offset(self.offset.wrapping_add(self.size as u64));
            if nextoff == lo.offset {
                return true;
            }
        } else {
            let nextoff = space.wrap_offset(lo.offset.wrapping_add(lo.size as u64));
            if nextoff == self.offset {
                return true;
            }
        }
        false
    }
}

impl PartialEq for VarnodeData {
    fn eq(&self, other: &VarnodeData) -> bool {
        space_key(&self.space) == space_key(&other.space) && self.offset == other.offset && self.size == other.size
    }
}

impl Eq for VarnodeData {}

impl Hash for VarnodeData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        space_key(&self.space).hash(state);
        self.offset.hash(state);
        self.size.hash(state);
    }
}

impl PartialOrd for VarnodeData {
    fn partial_cmp(&self, other: &VarnodeData) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VarnodeData {
    fn cmp(&self, other: &VarnodeData) -> Ordering {
        space_key(&self.space)
            .cmp(&space_key(&other.space))
            .then(self.offset.cmp(&other.offset))
            .then(other.size.cmp(&self.size))
    }
}

#[derive(Clone, Debug)]
pub struct PcodeOpRaw {
    opcode: OpCode,
    seq: SeqNum,
    out: Option<VarnodeData>,
    inputs: Vec<VarnodeData>,
}

impl PcodeOpRaw {
    pub fn new(opcode: OpCode) -> PcodeOpRaw {
        PcodeOpRaw {
            opcode,
            seq: SeqNum::default(),
            out: None,
            inputs: Vec::new(),
        }
    }

    pub fn set_opcode(&mut self, opcode: OpCode) {
        self.opcode = opcode;
    }

    pub fn get_opcode(&self) -> OpCode {
        self.opcode
    }

    pub fn set_seq_num(&mut self, addr: &Address, uniq: u32) {
        self.seq = SeqNum::new(addr.clone(), uniq);
    }

    pub fn get_seq_num(&self) -> &SeqNum {
        &self.seq
    }

    pub fn get_addr(&self) -> &Address {
        self.seq.get_addr()
    }

    pub fn set_output(&mut self, out: Option<VarnodeData>) {
        self.out = out;
    }

    pub fn get_output(&self) -> Option<&VarnodeData> {
        self.out.as_ref()
    }

    pub fn add_input(&mut self, input: VarnodeData) {
        self.inputs.push(input);
    }

    pub fn clear_inputs(&mut self) {
        self.inputs.clear();
    }

    pub fn num_input(&self) -> i32 {
        self.inputs.len() as i32
    }

    pub fn get_input(&self, index: i32) -> &VarnodeData {
        &self.inputs[index as usize]
    }

    pub fn decode(decoder: &mut dyn Decoder, isize: i32) -> Result<(OpCode, Option<VarnodeData>, Vec<VarnodeData>)> {
        let opcode = decoder.read_opcode_attr(ATTRIB_CODE)?;
        let sub_id = decoder.peek_element()?;
        let outvar = if sub_id == ELEM_VOID {
            decoder.open_element()?;
            decoder.close_element(sub_id)?;
            None
        } else {
            Some(VarnodeData::decode(decoder)?)
        };
        let mut invar = Vec::with_capacity(isize.max(0) as usize);
        for _ in 0..isize {
            let sub_id = decoder.peek_element()?;
            if sub_id == ELEM_SPACEID {
                decoder.open_element()?;
                let space = decoder.manager()?.get_constant_space();
                let referenced = decoder.read_space_attr(ATTRIB_NAME)?;
                invar.push(VarnodeData {
                    space,
                    offset: referenced.get_index() as u64,
                    size: 8,
                });
                decoder.close_element(sub_id)?;
            } else {
                invar.push(VarnodeData::decode(decoder)?);
            }
        }
        Ok((opcode, outvar, invar))
    }
}
