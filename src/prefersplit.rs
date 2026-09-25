use crate::stdsort::std_sort;
use std::cmp::Ordering;

use crate::address::calc_mask;
use crate::architecture::Architecture;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::marshal::ElementId;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::space::SpaceType;
use crate::varnode::VarnodeId;

pub const ELEM_PREFERSPLIT: ElementId = ElementId::new("prefersplit", 225);

#[derive(Clone, Debug, Default)]
pub struct PreferSplitRecord {
    pub storage: VarnodeData,
    pub splitoffset: i32,
}

impl PreferSplitRecord {
    pub fn less_than(&self, op2: &PreferSplitRecord) -> bool {
        let space_index = self.storage.space.as_ref().map_or(-1, |spc| spc.get_index());
        let other_index = op2.storage.space.as_ref().map_or(-1, |spc| spc.get_index());
        if space_index != other_index {
            return space_index < other_index;
        }
        if self.storage.size != op2.storage.size {
            return self.storage.size > op2.storage.size;
        }
        self.storage.offset < op2.storage.offset
    }
}

impl PartialEq for PreferSplitRecord {
    fn eq(&self, op2: &PreferSplitRecord) -> bool {
        !self.less_than(op2) && !op2.less_than(self)
    }
}

impl Eq for PreferSplitRecord {}

impl PartialOrd for PreferSplitRecord {
    fn partial_cmp(&self, op2: &PreferSplitRecord) -> Option<Ordering> {
        Some(self.cmp(op2))
    }
}

impl Ord for PreferSplitRecord {
    fn cmp(&self, op2: &PreferSplitRecord) -> Ordering {
        if self.less_than(op2) {
            Ordering::Less
        } else if op2.less_than(self) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

#[derive(Clone, Debug)]
pub struct SplitInstance {
    pub(crate) splitoffset: i32,
    pub(crate) vn: VarnodeId,
    pub(crate) hi: Option<VarnodeId>,
    pub(crate) lo: Option<VarnodeId>,
}

impl SplitInstance {
    pub fn new(original: VarnodeId, off: i32) -> SplitInstance {
        SplitInstance {
            vn: original,
            splitoffset: off,
            hi: None,
            lo: None,
        }
    }

    pub fn create_pieces(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        sethi: bool,
        setlo: bool,
    ) -> Result<()> {
        let original = data.vn(self.vn);
        let bigendian = original.get_space().expect("varnode without space").is_big_endian();
        let size = original.get_size();
        let losize = if bigendian {
            size - self.splitoffset
        } else {
            self.splitoffset
        };
        let hisize = size - losize;
        if original.is_constant() {
            let origval = original.get_offset();
            let loval = origval & calc_mask(losize);
            let hival = origval.wrapping_shr((8 * losize) as u32) & calc_mask(hisize);
            if setlo && self.lo.is_none() {
                self.lo = Some(data.new_constant(losize, loval, glb));
            }
            if sethi && self.hi.is_none() {
                self.hi = Some(data.new_constant(hisize, hival, glb));
            }
        } else {
            let addr = original.get_addr().clone();
            let split_addr = addr.add(self.splitoffset as i64);
            if bigendian {
                if setlo && self.lo.is_none() {
                    self.lo = Some(data.new_varnode(losize, &split_addr, None, glb)?);
                }
                if sethi && self.hi.is_none() {
                    self.hi = Some(data.new_varnode(hisize, &addr, None, glb)?);
                }
            } else {
                if setlo && self.lo.is_none() {
                    self.lo = Some(data.new_varnode(losize, &addr, None, glb)?);
                }
                if sethi && self.hi.is_none() {
                    self.hi = Some(data.new_varnode(hisize, &split_addr, None, glb)?);
                }
            }
        }
        Ok(())
    }

    fn get_hi(&self) -> VarnodeId {
        self.hi.expect("missing most significant piece")
    }

    fn get_lo(&self) -> VarnodeId {
        self.lo.expect("missing least significant piece")
    }
}

#[derive(Clone, Debug, Default)]
pub struct PreferSplitManager {
    pub(crate) tempsplits: Vec<OpId>,
}

impl PreferSplitManager {
    fn create_copy_ops(
        &mut self,
        ininst: &SplitInstance,
        outinst: &SplitInstance,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let addr = data.op(op).get_addr().clone();
        let hiop = data.new_op(1, &addr);
        let loop_op = data.new_op(1, &addr);
        data.op_set_opcode(hiop, OpCode::Copy, glb);
        data.op_set_opcode(loop_op, OpCode::Copy, glb);

        data.op_insert_after(loop_op, op);
        data.op_insert_after(hiop, op);
        data.op_unset_input(op, 0);

        data.op_set_output(hiop, outinst.get_hi(), glb)?;
        data.op_set_output(loop_op, outinst.get_lo(), glb)?;
        data.op_set_input(hiop, ininst.get_hi(), 0)?;
        data.op_set_input(loop_op, ininst.get_lo(), 0)?;
        self.tempsplits.push(hiop);
        self.tempsplits.push(loop_op);
        Ok(())
    }

    fn test_defining_copy(&self, inst: &SplitInstance, def: OpId, data: &Funcdata, glb: &Architecture) -> bool {
        let invn = data.op(def).get_in(0);
        let input = data.vn(invn);
        if !input.is_constant() && input.get_space().expect("varnode without space").get_type() != SpaceType::Internal {
            let inrec = match self.find_record(invn, &glb.splitrecords, data) {
                None => return false,
                Some(record) => record,
            };
            if inrec.splitoffset != inst.splitoffset {
                return false;
            }
            if !input.is_free() {
                return false;
            }
        }
        true
    }

    fn split_defining_copy(
        &mut self,
        inst: &mut SplitInstance,
        def: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let invn = data.op(def).get_in(0);
        let mut ininst = SplitInstance::new(invn, inst.splitoffset);
        inst.create_pieces(data, glb, true, true)?;
        ininst.create_pieces(data, glb, true, true)?;
        self.create_copy_ops(&ininst, inst, def, data, glb)
    }

    fn test_reading_copy(&self, inst: &SplitInstance, readop: OpId, data: &Funcdata, glb: &Architecture) -> bool {
        let outvn = data.op(readop).get_out().expect("copy without output");
        let output = data.vn(outvn);
        if !output.has_no_descend() {
            return false;
        }
        if output.get_space().expect("varnode without space").get_type() != SpaceType::Internal {
            let outrec = match self.find_record(outvn, &glb.splitrecords, data) {
                None => return false,
                Some(record) => record,
            };
            if outrec.splitoffset != inst.splitoffset {
                return false;
            }
        }
        true
    }

    fn split_reading_copy(
        &mut self,
        inst: &mut SplitInstance,
        readop: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let outvn = data.op(readop).get_out().expect("copy without output");
        let mut outinst = SplitInstance::new(outvn, inst.splitoffset);
        inst.create_pieces(data, glb, true, true)?;
        outinst.create_pieces(data, glb, true, true)?;
        self.create_copy_ops(inst, &outinst, readop, data, glb)
    }

    fn test_zext(&self, inst: &SplitInstance, op: OpId, data: &Funcdata) -> bool {
        let invn = data.op(op).get_in(0);
        if data.vn(invn).is_constant() {
            return true;
        }
        let whole = data.vn(inst.vn);
        let bigendian = whole.get_space().expect("varnode without space").is_big_endian();
        let losize = if bigendian {
            whole.get_size() - inst.splitoffset
        } else {
            inst.splitoffset
        };
        if data.vn(invn).get_size() != losize {
            return false;
        }
        true
    }

    fn split_zext(
        &mut self,
        inst: &mut SplitInstance,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut ininst = SplitInstance::new(data.op(op).get_in(0), inst.splitoffset);
        let whole = data.vn(inst.vn);
        let bigendian = whole.get_space().expect("varnode without space").is_big_endian();
        let (losize, hisize) = if bigendian {
            (whole.get_size() - inst.splitoffset, inst.splitoffset)
        } else {
            (inst.splitoffset, whole.get_size() - inst.splitoffset)
        };
        let input = data.vn(ininst.vn);
        if input.is_constant() {
            let origval = input.get_offset();
            let loval = origval & calc_mask(losize);
            let hival = origval.wrapping_shr((8 * losize) as u32) & calc_mask(hisize);
            ininst.lo = Some(data.new_constant(losize, loval, glb));
            ininst.hi = Some(data.new_constant(hisize, hival, glb));
        } else {
            ininst.lo = Some(ininst.vn);
            ininst.hi = Some(data.new_constant(hisize, 0, glb));
        }

        inst.create_pieces(data, glb, true, true)?;
        self.create_copy_ops(&ininst, inst, op, data, glb)
    }

    fn test_piece(&self, inst: &SplitInstance, op: OpId, data: &Funcdata) -> bool {
        let piece_op = data.op(op);
        if data
            .vn(inst.vn)
            .get_space()
            .expect("varnode without space")
            .is_big_endian()
        {
            if data.vn(piece_op.get_in(0)).get_size() != inst.splitoffset {
                return false;
            }
        } else if data.vn(piece_op.get_in(1)).get_size() != inst.splitoffset {
            return false;
        }
        true
    }

    fn split_piece(
        &mut self,
        inst: &mut SplitInstance,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut loin = data.op(op).get_in(1);
        let mut hiin = data.op(op).get_in(0);
        inst.create_pieces(data, glb, true, true)?;
        let addr = data.op(op).get_addr().clone();
        let hiop = data.new_op(1, &addr);
        let loop_op = data.new_op(1, &addr);
        data.op_set_opcode(hiop, OpCode::Copy, glb);
        data.op_set_opcode(loop_op, OpCode::Copy, glb);
        data.op_set_output(hiop, inst.get_hi(), glb)?;
        data.op_set_output(loop_op, inst.get_lo(), glb)?;

        data.op_insert_after(loop_op, op);
        data.op_insert_after(hiop, op);
        data.op_unset_input(op, 0);
        data.op_unset_input(op, 1);

        if data.vn(hiin).is_constant() {
            let (size, offset) = (data.vn(hiin).get_size(), data.vn(hiin).get_offset());
            hiin = data.new_constant(size, offset, glb);
        }
        data.op_set_input(hiop, hiin, 0)?;
        if data.vn(loin).is_constant() {
            let (size, offset) = (data.vn(loin).get_size(), data.vn(loin).get_offset());
            loin = data.new_constant(size, offset, glb);
        }
        data.op_set_input(loop_op, loin, 0)?;
        Ok(())
    }

    fn test_subpiece(&self, inst: &SplitInstance, op: OpId, data: &Funcdata) -> bool {
        let subpiece_op = data.op(op);
        let outvn = subpiece_op.get_out().expect("subpiece without output");
        let whole = data.vn(inst.vn);
        let bigendian = whole.get_space().expect("varnode without space").is_big_endian();
        let losize = if bigendian {
            whole.get_size() - inst.splitoffset
        } else {
            inst.splitoffset
        };
        let suboff = data.vn(subpiece_op.get_in(1)).get_offset() as i32;
        if suboff == 0 {
            if losize != data.vn(outvn).get_size() {
                return false;
            }
        } else {
            if losize != suboff {
                return false;
            }
            if data.vn(outvn).get_size() + losize != whole.get_size() {
                return false;
            }
        }
        true
    }

    fn split_subpiece(
        &mut self,
        inst: &mut SplitInstance,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let suboff = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let grabbinglo = suboff == 0;

        inst.create_pieces(data, glb, !grabbinglo, grabbinglo)?;
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_remove_input(op, 1);

        let invn = if grabbinglo { inst.get_lo() } else { inst.get_hi() };
        data.op_set_input(op, invn, 0)
    }

    fn test_load(&self, _inst: &SplitInstance, _op: OpId, _data: &Funcdata) -> bool {
        true
    }

    fn finish_pointer_ops(
        &mut self,
        op: OpId,
        hiop: OpId,
        loop_op: OpId,
        ptrvn: &mut VarnodeId,
        addvn: VarnodeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let spaceid = data.op(op).get_in(0);
        let spc = data
            .vn(spaceid)
            .get_space_from_const(&glb.manager)
            .expect("invalid space constant");
        let (spaceid_size, spaceid_offset) = (data.vn(spaceid).get_size(), data.vn(spaceid).get_offset());
        let hi_spaceid = data.new_constant(spaceid_size, spaceid_offset, glb);
        data.op_set_input(hiop, hi_spaceid, 0)?;
        let lo_spaceid = data.new_constant(spaceid_size, spaceid_offset, glb);
        data.op_set_input(loop_op, lo_spaceid, 0)?;
        if data.vn(*ptrvn).is_free() {
            let pointer = data.vn(*ptrvn);
            let (size, space, offset) = (
                pointer.get_size(),
                pointer.get_space().expect("varnode without space").clone(),
                pointer.get_offset(),
            );
            *ptrvn = data.new_varnode_space_offset(size, &space, offset, glb)?;
        }
        if spc.is_big_endian() {
            data.op_set_input(hiop, *ptrvn, 1)?;
            data.op_set_input(loop_op, addvn, 1)?;
        } else {
            data.op_set_input(hiop, addvn, 1)?;
            data.op_set_input(loop_op, *ptrvn, 1)?;
        }
        Ok(())
    }

    fn split_load(
        &mut self,
        inst: &mut SplitInstance,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        inst.create_pieces(data, glb, true, true)?;
        let addr = data.op(op).get_addr().clone();
        let hiop = data.new_op(2, &addr);
        let loop_op = data.new_op(2, &addr);
        let addop = data.new_op(2, &addr);

        data.op_set_opcode(hiop, OpCode::Load, glb);
        data.op_set_opcode(loop_op, OpCode::Load, glb);
        data.op_set_opcode(addop, OpCode::IntAdd, glb);

        data.op_insert_after(loop_op, op);
        data.op_insert_after(hiop, op);
        data.op_insert_after(addop, op);
        let ptrvn = data.op(op).get_in(1);
        data.op_unset_input(op, 1);

        let ptr_size = data.vn(ptrvn).get_size();
        let addvn = data.new_unique_out(ptr_size, addop, glb)?;
        data.op_set_input(addop, ptrvn, 0)?;
        let offset_vn = data.new_constant(ptr_size, inst.splitoffset as i64 as u64, glb);
        data.op_set_input(addop, offset_vn, 1)?;

        data.op_set_output(hiop, inst.get_hi(), glb)?;
        data.op_set_output(loop_op, inst.get_lo(), glb)?;
        let mut pointer = ptrvn;
        self.finish_pointer_ops(op, hiop, loop_op, &mut pointer, addvn, data, glb)
    }

    fn test_store(&self, _inst: &SplitInstance, _op: OpId, _data: &Funcdata) -> bool {
        true
    }

    fn split_store(
        &mut self,
        inst: &mut SplitInstance,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        inst.create_pieces(data, glb, true, true)?;
        let addr = data.op(op).get_addr().clone();
        let hiop = data.new_op(3, &addr);
        let loop_op = data.new_op(3, &addr);
        let addop = data.new_op(2, &addr);

        data.op_set_opcode(hiop, OpCode::Store, glb);
        data.op_set_opcode(loop_op, OpCode::Store, glb);
        data.op_set_opcode(addop, OpCode::IntAdd, glb);

        data.op_insert_after(loop_op, op);
        data.op_insert_after(hiop, op);
        data.op_insert_after(addop, op);
        let ptrvn = data.op(op).get_in(1);
        data.op_unset_input(op, 1);
        data.op_unset_input(op, 2);

        let ptr_size = data.vn(ptrvn).get_size();
        let addvn = data.new_unique_out(ptr_size, addop, glb)?;
        data.op_set_input(addop, ptrvn, 0)?;
        let offset_vn = data.new_constant(ptr_size, inst.splitoffset as i64 as u64, glb);
        data.op_set_input(addop, offset_vn, 1)?;

        data.op_set_input(hiop, inst.get_hi(), 2)?;
        data.op_set_input(loop_op, inst.get_lo(), 2)?;
        let mut pointer = ptrvn;
        self.finish_pointer_ops(op, hiop, loop_op, &mut pointer, addvn, data, glb)
    }

    fn split_varnode(&mut self, inst: &mut SplitInstance, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        if data.vn(inst.vn).is_written() {
            if !data.vn(inst.vn).has_no_descend() {
                return Ok(false);
            }
            let op = data.vn(inst.vn).get_def().expect("written varnode without defining op");
            match data.op(op).code() {
                OpCode::Copy => {
                    if !self.test_defining_copy(inst, op, data, glb) {
                        return Ok(false);
                    }
                    self.split_defining_copy(inst, op, data, glb)?;
                }
                OpCode::Piece => {
                    if !self.test_piece(inst, op, data) {
                        return Ok(false);
                    }
                    self.split_piece(inst, op, data, glb)?;
                }
                OpCode::Load => {
                    if !self.test_load(inst, op, data) {
                        return Ok(false);
                    }
                    self.split_load(inst, op, data, glb)?;
                }
                OpCode::IntZext => {
                    if !self.test_zext(inst, op, data) {
                        return Ok(false);
                    }
                    self.split_zext(inst, op, data, glb)?;
                }
                _ => return Ok(false),
            }
            data.op_destroy(op)?;
        } else {
            if !data.vn(inst.vn).is_free() {
                return Ok(false);
            }
            let op = match data.vn(inst.vn).lone_descend() {
                None => return Ok(false),
                Some(op) => op,
            };
            match data.op(op).code() {
                OpCode::Copy => {
                    if !self.test_reading_copy(inst, op, data, glb) {
                        return Ok(false);
                    }
                    self.split_reading_copy(inst, op, data, glb)?;
                }
                OpCode::Subpiece => {
                    if !self.test_subpiece(inst, op, data) {
                        return Ok(false);
                    }
                    self.split_subpiece(inst, op, data, glb)?;
                    return Ok(true);
                }
                OpCode::Store => {
                    if !self.test_store(inst, op, data) {
                        return Ok(false);
                    }
                    self.split_store(inst, op, data, glb)?;
                }
                _ => return Ok(false),
            }
            data.op_destroy(op)?;
        }
        Ok(true)
    }

    fn split_record(&mut self, rec: &PreferSplitRecord, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let addr = rec.storage.get_addr();
        let size = rec.storage.size as i32;
        let mut inst = SplitInstance::new(VarnodeId(0), rec.splitoffset);
        let mut iter = data.begin_loc_size(size, &addr);
        let mut enditer = data.end_loc_size(size, &addr);
        while iter != enditer {
            inst.vn = data.vbank.loc_at(&iter).expect("invalid varnode location iterator");
            iter = data.vbank.loc_next(&iter);
            inst.lo = None;
            inst.hi = None;
            if self.split_varnode(&mut inst, data, glb)? {
                iter = data.begin_loc_size(size, &addr);
                enditer = data.end_loc_size(size, &addr);
            }
        }
        Ok(())
    }

    fn test_temporary(&self, inst: &SplitInstance, data: &Funcdata) -> bool {
        let op = data.vn(inst.vn).get_def().expect("temporary without defining op");
        match data.op(op).code() {
            OpCode::Piece => {
                if !self.test_piece(inst, op, data) {
                    return false;
                }
            }
            OpCode::Load => {
                if !self.test_load(inst, op, data) {
                    return false;
                }
            }
            OpCode::IntZext => {
                if !self.test_zext(inst, op, data) {
                    return false;
                }
            }
            _ => return false,
        }
        for &readop in data.vn(inst.vn).descend() {
            match data.op(readop).code() {
                OpCode::Subpiece => {
                    if !self.test_subpiece(inst, readop, data) {
                        return false;
                    }
                }
                OpCode::Store => {
                    if !self.test_store(inst, readop, data) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn split_temporary(&mut self, inst: &mut SplitInstance, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let op = data.vn(inst.vn).get_def().expect("temporary without defining op");
        match data.op(op).code() {
            OpCode::Piece => self.split_piece(inst, op, data, glb)?,
            OpCode::Load => self.split_load(inst, op, data, glb)?,
            OpCode::IntZext => self.split_zext(inst, op, data, glb)?,
            _ => {}
        }

        while let Some(&readop) = data.vn(inst.vn).descend().first() {
            match data.op(readop).code() {
                OpCode::Subpiece => self.split_subpiece(inst, readop, data, glb)?,
                OpCode::Store => {
                    self.split_store(inst, readop, data, glb)?;
                    data.op_destroy(readop)?;
                }
                _ => {}
            }
        }
        data.op_destroy(op)
    }

    pub fn init(&mut self) {}

    pub fn find_record<'records>(
        &self,
        vn: VarnodeId,
        records: &'records [PreferSplitRecord],
        data: &Funcdata,
    ) -> Option<&'records PreferSplitRecord> {
        let original = data.vn(vn);
        let templ = PreferSplitRecord {
            storage: VarnodeData {
                space: original.get_space().cloned(),
                offset: original.get_offset(),
                size: original.get_size() as u32,
            },
            splitoffset: 0,
        };
        let position = records.partition_point(|record| record.less_than(&templ));
        let found = records.get(position)?;
        if templ.less_than(found) {
            return None;
        }
        Some(found)
    }

    pub fn initialize(records: &mut [PreferSplitRecord]) {
        std_sort(records, |first, second| first < second);
    }

    pub fn split(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        for index in 0..glb.splitrecords.len() {
            let rec = glb.splitrecords[index].clone();
            self.split_record(&rec, data, glb)?;
        }
        Ok(())
    }

    pub fn split_additional(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut defops: Vec<OpId> = Vec::new();
        for index in 0..self.tempsplits.len() {
            let op = self.tempsplits[index];
            if data.op(op).is_dead() {
                continue;
            }
            let vn = data.op(op).get_in(0);
            if data.vn(vn).is_written() {
                let defop = data.vn(vn).get_def().expect("written varnode without defining op");
                if data.op(defop).code() == OpCode::Subpiece {
                    let invn = data.op(defop).get_in(0);
                    if data.vn(invn).get_space().expect("varnode without space").get_type() == SpaceType::Internal {
                        defops.push(defop);
                    }
                }
            }
            let outvn = data.op(op).get_out().expect("copy without output");
            for &defop in data.vn(outvn).descend() {
                if data.op(defop).code() == OpCode::Piece {
                    let piece_out = data.op(defop).get_out().expect("piece without output");
                    if data
                        .vn(piece_out)
                        .get_space()
                        .expect("varnode without space")
                        .get_type()
                        == SpaceType::Internal
                    {
                        defops.push(defop);
                    }
                }
            }
        }
        for &op in &defops {
            if data.op(op).is_dead() {
                continue;
            }
            if data.op(op).code() == OpCode::Piece {
                let vn = data.op(op).get_out().expect("piece without output");
                let splitoff = if data.vn(vn).get_space().expect("varnode without space").is_big_endian() {
                    data.vn(data.op(op).get_in(0)).get_size()
                } else {
                    data.vn(data.op(op).get_in(1)).get_size()
                };
                let mut inst = SplitInstance::new(vn, splitoff);
                if self.test_temporary(&inst, data) {
                    self.split_temporary(&mut inst, data, glb)?;
                }
            } else if data.op(op).code() == OpCode::Subpiece {
                let vn = data.op(op).get_in(0);
                let suboff = data.vn(data.op(op).get_in(1)).get_offset();
                let out_size = data
                    .vn(data.op(op).get_out().expect("subpiece without output"))
                    .get_size();
                let whole_size = data.vn(vn).get_size();
                let splitoff = if data.vn(vn).get_space().expect("varnode without space").is_big_endian() {
                    if suboff == 0 {
                        whole_size - out_size
                    } else {
                        whole_size - suboff as i32
                    }
                } else if suboff == 0 {
                    out_size
                } else {
                    suboff as i32
                };
                let mut inst = SplitInstance::new(vn, splitoff);
                if self.test_temporary(&inst, data) {
                    self.split_temporary(&mut inst, data, glb)?;
                }
            }
        }
        Ok(())
    }
}
