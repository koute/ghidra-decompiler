use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{Address, calc_mask};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::space::{SpaceRef, SpaceType};
use crate::varnode::VarnodeId;

fn present<T>(value: Option<T>) -> T {
    value.expect("double precision form references an unset piece")
}

fn op_out(data: &Funcdata, op: OpId) -> VarnodeId {
    data.op(op).get_out().expect("p-code op has no output varnode")
}

fn def_op(data: &Funcdata, vn: VarnodeId) -> OpId {
    data.vn(vn).get_def().expect("written varnode has no defining op")
}

fn op_block(data: &Funcdata, op: OpId) -> BlockId {
    data.op(op).get_parent().expect("p-code op is not in a basic block")
}

fn op_order(data: &Funcdata, op: OpId) -> u32 {
    data.op(op).get_seq_num().get_order()
}

fn op_input(data: &Funcdata, op: OpId, slot: i32) -> VarnodeId {
    data.op(op).get_in(slot)
}

fn input_offset(data: &Funcdata, op: OpId, slot: i32) -> u64 {
    data.vn(data.op(op).get_in(slot)).get_offset()
}

fn next_basic_op(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.op(op).links[PcodeOp::BASIC_LIST].next
}

fn set_precis_lo(data: &mut Funcdata, vn: VarnodeId) {
    data.vbank.get_mut(vn).set_precis_lo(&mut data.highs);
}

fn set_precis_hi(data: &mut Funcdata, vn: VarnodeId) {
    data.vbank.get_mut(vn).set_precis_hi(&mut data.highs);
}

fn space_matches(space: Option<&SpaceRef>, spc: &SpaceRef) -> bool {
    space.map(|candidate| candidate.get_index()) == Some(spc.get_index())
}

fn space_type_of(data: &Funcdata, vn: VarnodeId) -> Option<SpaceType> {
    data.vn(vn).get_space().map(|space| space.get_type())
}

fn dominated_by(data: &Funcdata, start: BlockId, dominator: BlockId) -> bool {
    let mut curbl = Some(start);
    while let Some(current) = curbl {
        curbl = data.block(current).get_immed_dom();
        if curbl == Some(dominator) {
            return true;
        }
    }
    false
}

#[derive(Clone, Debug)]
pub struct SplitVarnode {
    lo: Option<VarnodeId>,
    hi: Option<VarnodeId>,
    whole: Option<VarnodeId>,
    defpoint: Option<OpId>,
    defblock: Option<BlockId>,
    val: u64,
    wholesize: i32,
}

impl Default for SplitVarnode {
    fn default() -> SplitVarnode {
        SplitVarnode::new()
    }
}

impl SplitVarnode {
    pub fn new() -> SplitVarnode {
        SplitVarnode {
            lo: None,
            hi: None,
            whole: None,
            defpoint: None,
            defblock: None,
            val: 0,
            wholesize: 0,
        }
    }

    pub fn new_constant(size: i32, value: u64) -> SplitVarnode {
        let mut result = SplitVarnode::new();
        result.init_partial_constant(size, value);
        result
    }

    pub fn new_pieces(lo_vn: VarnodeId, hi_vn: VarnodeId, data: &Funcdata) -> SplitVarnode {
        let mut result = SplitVarnode::new();
        let size = data.vn(lo_vn).get_size() + data.vn(hi_vn).get_size();
        result.init_partial(size, lo_vn, Some(hi_vn), data);
        result
    }

    pub fn is_constant(&self) -> bool {
        self.lo.is_none()
    }

    pub fn has_both_pieces(&self) -> bool {
        self.hi.is_some() && self.lo.is_some()
    }

    pub fn get_size(&self) -> i32 {
        self.wholesize
    }

    pub fn get_lo(&self) -> Option<VarnodeId> {
        self.lo
    }

    pub fn get_hi(&self) -> Option<VarnodeId> {
        self.hi
    }

    pub fn get_whole(&self) -> Option<VarnodeId> {
        self.whole
    }

    pub fn get_def_point(&self) -> Option<OpId> {
        self.defpoint
    }

    pub fn get_def_block(&self) -> Option<BlockId> {
        self.defblock
    }

    pub fn get_value(&self) -> u64 {
        self.val
    }

    fn find_whole_split_to_pieces(&mut self, data: &Funcdata) -> bool {
        if self.whole.is_none() {
            let Some(hi) = self.hi else {
                return false;
            };
            let Some(lo) = self.lo else {
                return false;
            };
            if !data.vn(hi).is_written() {
                return false;
            }
            let mut subhi = def_op(data, hi);
            if data.op(subhi).code() == OpCode::Copy {
                let otherhi = op_input(data, subhi, 0);
                if !data.vn(otherhi).is_written() {
                    return false;
                }
                subhi = def_op(data, otherhi);
            }
            if data.op(subhi).code() != OpCode::Subpiece {
                return false;
            }
            if input_offset(data, subhi, 1) != (self.wholesize - data.vn(hi).get_size()) as i64 as u64 {
                return false;
            }
            let putative_whole = op_input(data, subhi, 0);
            if data.vn(putative_whole).get_size() != self.wholesize {
                return false;
            }
            if !data.vn(lo).is_written() {
                return false;
            }
            let mut sublo = def_op(data, lo);
            if data.op(sublo).code() == OpCode::Copy {
                let otherlo = op_input(data, sublo, 0);
                if !data.vn(otherlo).is_written() {
                    return false;
                }
                sublo = def_op(data, otherlo);
            }
            if data.op(sublo).code() != OpCode::Subpiece {
                return false;
            }
            if putative_whole != op_input(data, sublo, 0) {
                return false;
            }
            if input_offset(data, sublo, 1) != 0 {
                return false;
            }
            self.whole = Some(putative_whole);
        }
        let whole = present(self.whole);
        if data.vn(whole).is_written() {
            let defpoint = def_op(data, whole);
            self.defpoint = Some(defpoint);
            self.defblock = data.op(defpoint).get_parent();
        } else if data.vn(whole).is_input() {
            self.defpoint = None;
            self.defblock = None;
        }
        true
    }

    fn find_definition_point(&mut self, data: &Funcdata) -> bool {
        if let Some(hi) = self.hi
            && data.vn(hi).is_constant()
        {
            return false;
        }
        let lo = present(self.lo);
        if data.vn(lo).is_constant() {
            return false;
        }
        match self.hi {
            None => {
                if data.vn(lo).is_input() {
                    self.defblock = None;
                    self.defpoint = None;
                } else if data.vn(lo).is_written() {
                    let defpoint = def_op(data, lo);
                    self.defpoint = Some(defpoint);
                    self.defblock = data.op(defpoint).get_parent();
                } else {
                    return false;
                }
            }
            Some(hi) => {
                if data.vn(hi).is_written() {
                    if !data.vn(lo).is_written() {
                        return false;
                    }
                    let mut lastop = def_op(data, hi);
                    let defblock = op_block(data, lastop);
                    self.defblock = Some(defblock);
                    let lastop2 = def_op(data, lo);
                    let otherblock = op_block(data, lastop2);
                    if defblock != otherblock {
                        self.defpoint = Some(lastop);
                        if dominated_by(data, defblock, otherblock) {
                            return true;
                        }
                        self.defblock = Some(otherblock);
                        let secondblock = op_block(data, lastop);
                        self.defpoint = Some(lastop2);
                        if dominated_by(data, otherblock, secondblock) {
                            return true;
                        }
                        self.defblock = None;
                        return false;
                    }
                    if op_order(data, lastop2) > op_order(data, lastop) {
                        lastop = lastop2;
                    }
                    self.defpoint = Some(lastop);
                } else if data.vn(hi).is_input() {
                    if !data.vn(lo).is_input() {
                        return false;
                    }
                    self.defblock = None;
                    self.defpoint = None;
                }
            }
        }
        true
    }

    fn find_whole_built_from_pieces(&mut self, data: &Funcdata) -> Result<bool> {
        let Some(hi) = self.hi else {
            return Ok(false);
        };
        let Some(lo) = self.lo else {
            return Ok(false);
        };
        let basic_block = if data.vn(lo).is_written() {
            Some(op_block(data, def_op(data, lo)))
        } else if data.vn(lo).is_input() {
            None
        } else {
            return Err(Error::Lowlevel("Trying to find whole on free varnode".to_string()));
        };
        let mut res: Option<OpId> = None;
        for &op in data.vn(lo).descend() {
            if data.op(op).code() != OpCode::Piece {
                continue;
            }
            if op_input(data, op, 0) != hi {
                continue;
            }
            match basic_block {
                Some(block) => {
                    if data.op(op).get_parent() != Some(block) {
                        continue;
                    }
                }
                None => {
                    if !data.block(op_block(data, op)).is_entry_point() {
                        continue;
                    }
                }
            }
            match res {
                None => res = Some(op),
                Some(previous) => {
                    if op_order(data, op) < op_order(data, previous) {
                        res = Some(op);
                    }
                }
            }
        }
        match res {
            None => self.whole = None,
            Some(found) => {
                self.defpoint = Some(found);
                self.defblock = data.op(found).get_parent();
                self.whole = data.op(found).get_out();
            }
        }
        Ok(self.whole.is_some())
    }

    pub fn init_all(&mut self, whole_vn: VarnodeId, lo_vn: VarnodeId, hi_vn: Option<VarnodeId>, data: &Funcdata) {
        self.wholesize = data.vn(whole_vn).get_size();
        self.lo = Some(lo_vn);
        self.hi = hi_vn;
        self.whole = Some(whole_vn);
        self.defpoint = None;
        self.defblock = None;
    }

    pub fn init_partial_constant(&mut self, size: i32, value: u64) {
        self.val = value;
        self.wholesize = size;
        self.lo = None;
        self.hi = None;
        self.whole = None;
        self.defpoint = None;
        self.defblock = None;
    }

    pub fn init_partial(&mut self, size: i32, lo_vn: VarnodeId, hi_vn: Option<VarnodeId>, data: &Funcdata) {
        match hi_vn {
            None => {
                self.hi = None;
                if data.vn(lo_vn).is_constant() {
                    self.val = data.vn(lo_vn).get_offset();
                    self.lo = None;
                } else {
                    self.lo = Some(lo_vn);
                }
            }
            Some(hi) => {
                if data.vn(lo_vn).is_constant() && data.vn(hi).is_constant() {
                    self.val = data.vn(hi).get_offset();
                    self.val = self.val.wrapping_shl((data.vn(lo_vn).get_size() * 8) as u32);
                    self.val |= data.vn(lo_vn).get_offset();
                    self.lo = None;
                    self.hi = None;
                } else {
                    self.lo = Some(lo_vn);
                    self.hi = Some(hi);
                }
            }
        }
        self.wholesize = size;
        self.whole = None;
        self.defpoint = None;
        self.defblock = None;
    }

    pub fn in_hand_hi(&mut self, hi_vn: VarnodeId, data: &Funcdata) -> bool {
        if !data.vn(hi_vn).is_precis_hi() {
            return false;
        }
        if data.vn(hi_vn).is_written() {
            let op = def_op(data, hi_vn);
            if data.op(op).code() == OpCode::Subpiece {
                let whole_vn = op_input(data, op, 0);
                if input_offset(data, op, 1) != (data.vn(whole_vn).get_size() - data.vn(hi_vn).get_size()) as i64 as u64
                {
                    return false;
                }
                for &tmpop in data.vn(whole_vn).descend() {
                    if data.op(tmpop).code() != OpCode::Subpiece {
                        continue;
                    }
                    let tmplo = op_out(data, tmpop);
                    if !data.vn(tmplo).is_precis_lo() {
                        continue;
                    }
                    if data.vn(tmplo).get_size() + data.vn(hi_vn).get_size() != data.vn(whole_vn).get_size() {
                        continue;
                    }
                    if input_offset(data, tmpop, 1) != 0 {
                        continue;
                    }
                    self.init_all(whole_vn, tmplo, Some(hi_vn), data);
                    return true;
                }
            }
        }
        false
    }

    pub fn in_hand_lo(&mut self, lo_vn: VarnodeId, data: &Funcdata) -> bool {
        if !data.vn(lo_vn).is_precis_lo() {
            return false;
        }
        if data.vn(lo_vn).is_written() {
            let op = def_op(data, lo_vn);
            if data.op(op).code() == OpCode::Subpiece {
                let whole_vn = op_input(data, op, 0);
                if input_offset(data, op, 1) != 0 {
                    return false;
                }
                for &tmpop in data.vn(whole_vn).descend() {
                    if data.op(tmpop).code() != OpCode::Subpiece {
                        continue;
                    }
                    let tmphi = op_out(data, tmpop);
                    if !data.vn(tmphi).is_precis_hi() {
                        continue;
                    }
                    if data.vn(tmphi).get_size() + data.vn(lo_vn).get_size() != data.vn(whole_vn).get_size() {
                        continue;
                    }
                    if input_offset(data, tmpop, 1) != data.vn(lo_vn).get_size() as i64 as u64 {
                        continue;
                    }
                    self.init_all(whole_vn, lo_vn, Some(tmphi), data);
                    return true;
                }
            }
        }
        false
    }

    pub fn in_hand_lo_no_hi(&mut self, lo_vn: VarnodeId, data: &Funcdata) -> bool {
        if !data.vn(lo_vn).is_precis_lo() {
            return false;
        }
        if !data.vn(lo_vn).is_written() {
            return false;
        }
        let op = def_op(data, lo_vn);
        if data.op(op).code() != OpCode::Subpiece {
            return false;
        }
        if input_offset(data, op, 1) != 0 {
            return false;
        }
        let whole_vn = op_input(data, op, 0);
        for &tmpop in data.vn(whole_vn).descend() {
            if data.op(tmpop).code() != OpCode::Subpiece {
                continue;
            }
            let tmphi = op_out(data, tmpop);
            if !data.vn(tmphi).is_precis_hi() {
                continue;
            }
            if data.vn(tmphi).get_size() + data.vn(lo_vn).get_size() != data.vn(whole_vn).get_size() {
                continue;
            }
            if input_offset(data, tmpop, 1) != data.vn(lo_vn).get_size() as i64 as u64 {
                continue;
            }
            self.init_all(whole_vn, lo_vn, Some(tmphi), data);
            return true;
        }
        self.init_all(whole_vn, lo_vn, None, data);
        true
    }

    pub fn in_hand_hi_out(&mut self, hi_vn: VarnodeId, data: &Funcdata) -> bool {
        let mut lo_tmp: Option<VarnodeId> = None;
        let mut outvn: Option<VarnodeId> = None;
        for &pieceop in data.vn(hi_vn).descend() {
            if data.op(pieceop).code() != OpCode::Piece {
                continue;
            }
            if op_input(data, pieceop, 0) != hi_vn {
                continue;
            }
            let lo_candidate = op_input(data, pieceop, 1);
            if !data.vn(lo_candidate).is_precis_lo() {
                continue;
            }
            if lo_tmp.is_some() {
                return false;
            }
            lo_tmp = Some(lo_candidate);
            outvn = data.op(pieceop).get_out();
        }
        if let Some(lo_found) = lo_tmp {
            self.init_all(present(outvn), lo_found, Some(hi_vn), data);
            return true;
        }
        false
    }

    pub fn in_hand_lo_out(&mut self, lo_vn: VarnodeId, data: &Funcdata) -> bool {
        let mut hi_tmp: Option<VarnodeId> = None;
        let mut outvn: Option<VarnodeId> = None;
        for &pieceop in data.vn(lo_vn).descend() {
            if data.op(pieceop).code() != OpCode::Piece {
                continue;
            }
            if op_input(data, pieceop, 1) != lo_vn {
                continue;
            }
            let hi_candidate = op_input(data, pieceop, 0);
            if !data.vn(hi_candidate).is_precis_hi() {
                continue;
            }
            if hi_tmp.is_some() {
                return false;
            }
            hi_tmp = Some(hi_candidate);
            outvn = data.op(pieceop).get_out();
        }
        if let Some(hi_found) = hi_tmp {
            self.init_all(present(outvn), lo_vn, Some(hi_found), data);
            return true;
        }
        false
    }

    pub fn is_whole_feasible(&mut self, existop: OpId, data: &Funcdata) -> Result<bool> {
        if self.is_constant() {
            return Ok(true);
        }
        if let (Some(lo), Some(hi)) = (self.lo, self.hi)
            && data.vn(lo).is_constant() != data.vn(hi).is_constant()
        {
            return Ok(false);
        }
        if !self.find_whole_split_to_pieces(data)
            && !self.find_whole_built_from_pieces(data)?
            && !self.find_definition_point(data)
        {
            return Ok(false);
        }
        let Some(defblock) = self.defblock else {
            return Ok(true);
        };
        let curbl = op_block(data, existop);
        if curbl == defblock {
            return Ok(op_order(data, present(self.defpoint)) <= op_order(data, existop));
        }
        Ok(dominated_by(data, curbl, defblock))
    }

    pub fn is_whole_phi_feasible(&mut self, bl: BlockId, data: &Funcdata) -> Result<bool> {
        if self.is_constant() {
            return Ok(false);
        }
        if !self.find_whole_split_to_pieces(data)
            && !self.find_whole_built_from_pieces(data)?
            && !self.find_definition_point(data)
        {
            return Ok(false);
        }
        let Some(defblock) = self.defblock else {
            return Ok(true);
        };
        if bl == defblock {
            return Ok(true);
        }
        Ok(dominated_by(data, bl, defblock))
    }

    pub fn find_create_whole(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if self.is_constant() {
            self.whole = Some(data.new_constant(self.wholesize, self.val, glb));
            return Ok(());
        }
        if let Some(lo) = self.lo {
            set_precis_lo(data, lo);
        }
        if let Some(hi) = self.hi {
            set_precis_hi(data, hi);
        }
        if self.whole.is_some() {
            return Ok(());
        }
        let mut topblock: Option<BlockId> = None;
        let addr = if self.defblock.is_some() {
            data.op(present(self.defpoint)).get_addr().clone()
        } else {
            let startblock = data.block_get_start_block(data.get_basic_blocks())?;
            topblock = Some(startblock);
            data.block(startblock).get_start()
        };
        let concatop;
        if let Some(hi) = self.hi {
            concatop = data.new_op(2, &addr);
            let whole = data.new_unique_out(self.wholesize, concatop, glb)?;
            self.whole = Some(whole);
            data.op_set_opcode(concatop, OpCode::Piece, glb);
            data.op_set_output(concatop, whole, glb)?;
            data.op_set_input(concatop, hi, 0)?;
            data.op_set_input(concatop, present(self.lo), 1)?;
        } else {
            concatop = data.new_op(1, &addr);
            let whole = data.new_unique_out(self.wholesize, concatop, glb)?;
            self.whole = Some(whole);
            data.op_set_opcode(concatop, OpCode::IntZext, glb);
            data.op_set_output(concatop, whole, glb)?;
            data.op_set_input(concatop, present(self.lo), 0)?;
        }
        if self.defblock.is_some() {
            data.op_insert_after(concatop, present(self.defpoint));
        } else {
            data.op_insert_begin(concatop, present(topblock));
        }
        self.defpoint = Some(concatop);
        self.defblock = data.op(concatop).get_parent();
        Ok(())
    }

    pub fn find_create_output_whole(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        set_precis_lo(data, present(self.lo));
        set_precis_hi(data, present(self.hi));
        if self.whole.is_some() {
            return Ok(());
        }
        self.whole = Some(data.new_unique(self.wholesize, None, glb));
        Ok(())
    }

    pub fn create_joined_whole(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let lo = present(self.lo);
        let hi = present(self.hi);
        set_precis_lo(data, lo);
        set_precis_hi(data, hi);
        if self.whole.is_some() {
            return Ok(());
        }
        let mut newaddr = Address::invalid();
        if !SplitVarnode::is_addr_tied_contiguous(lo, hi, &mut newaddr, data, glb) {
            let translate = glb.translate.as_deref().expect("architecture has no translator");
            newaddr = glb.manager.construct_join_address(
                translate,
                data.vn(hi).get_addr(),
                data.vn(hi).get_size(),
                data.vn(lo).get_addr(),
                data.vn(lo).get_size(),
            )?;
        }
        let whole = data.new_varnode(self.wholesize, &newaddr, None, glb)?;
        data.vn_mut(whole).set_write_mask();
        self.whole = Some(whole);
        Ok(())
    }

    fn build_piece_from_whole(
        &mut self,
        piece: VarnodeId,
        offset: u64,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let Some(pieceop) = data.vn(piece).get_def() else {
            return Err(Error::Lowlevel(
                "Building low piece that was originally undefined".to_string(),
            ));
        };
        let constvn = data.new_constant(4, offset, glb);
        let inlist = [present(self.whole), constvn];
        match data.op(pieceop).code() {
            OpCode::Multiequal => {
                let bl = op_block(data, pieceop);
                data.op_uninsert(pieceop);
                data.op_set_opcode(pieceop, OpCode::Subpiece, glb);
                data.op_set_all_input(pieceop, &inlist)?;
                data.op_insert_begin(pieceop, bl);
            }
            OpCode::Indirect => {
                let affector = PcodeOp::get_op_from_const(data.vn(op_input(data, pieceop, 1)).get_addr());
                if !data.op(affector).is_dead() {
                    data.op_uninsert(pieceop);
                }
                data.op_set_opcode(pieceop, OpCode::Subpiece, glb);
                data.op_set_all_input(pieceop, &inlist)?;
                if !data.op(affector).is_dead() {
                    data.op_insert_after(pieceop, affector);
                }
            }
            _ => {
                data.op_set_opcode(pieceop, OpCode::Subpiece, glb);
                data.op_set_all_input(pieceop, &inlist)?;
            }
        }
        Ok(())
    }

    pub fn build_lo_from_whole(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let lo = present(self.lo);
        self.build_piece_from_whole(lo, 0, data, glb)
    }

    pub fn build_hi_from_whole(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let hi = present(self.hi);
        let lo_size = data.vn(present(self.lo)).get_size();
        self.build_piece_from_whole(hi, lo_size as i64 as u64, data, glb)
    }

    pub fn find_earliest_split_point(&mut self, data: &Funcdata) -> Option<OpId> {
        let hi = present(self.hi);
        let lo = present(self.lo);
        if !data.vn(hi).is_written() {
            return None;
        }
        if !data.vn(lo).is_written() {
            return None;
        }
        let hiop = def_op(data, hi);
        let lo_op = def_op(data, lo);
        if data.op(lo_op).get_parent() != data.op(hiop).get_parent() {
            return None;
        }
        if op_order(data, lo_op) < op_order(data, hiop) {
            Some(lo_op)
        } else {
            Some(hiop)
        }
    }

    pub fn find_out_exist(&mut self, data: &Funcdata) -> Result<Option<OpId>> {
        if self.find_whole_built_from_pieces(data)? {
            return Ok(self.defpoint);
        }
        Ok(self.find_earliest_split_point(data))
    }

    pub fn exceeds_const_precision(&self) -> bool {
        self.is_constant() && (self.wholesize as i64 as u64 > std::mem::size_of::<u64>() as u64)
    }

    pub fn adjacent_offsets(vn1: VarnodeId, vn2: VarnodeId, size1: u64, data: &Funcdata) -> bool {
        if data.vn(vn1).is_constant() {
            if !data.vn(vn2).is_constant() {
                return false;
            }
            return data.vn(vn1).get_offset().wrapping_add(size1) == data.vn(vn2).get_offset();
        }
        if !data.vn(vn2).is_written() {
            return false;
        }
        let op2 = def_op(data, vn2);
        if data.op(op2).code() != OpCode::IntAdd {
            return false;
        }
        if !data.vn(op_input(data, op2, 1)).is_constant() {
            return false;
        }
        let const2 = input_offset(data, op2, 1);
        if op_input(data, op2, 0) == vn1 {
            return size1 == const2;
        }
        if !data.vn(vn1).is_written() {
            return false;
        }
        let op1 = def_op(data, vn1);
        if data.op(op1).code() != OpCode::IntAdd {
            return false;
        }
        if !data.vn(op_input(data, op1, 1)).is_constant() {
            return false;
        }
        let const1 = input_offset(data, op1, 1);
        if op_input(data, op1, 0) != op_input(data, op2, 0) {
            return false;
        }
        const1.wrapping_add(size1) == const2
    }

    pub fn test_contiguous_pointers(
        most: OpId,
        least: OpId,
        first: &mut Option<OpId>,
        second: &mut Option<OpId>,
        spc: &mut Option<SpaceRef>,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let least_space = data.vn(op_input(data, least, 0)).get_space_from_const(&glb.manager);
        *spc = least_space.clone();
        let most_space = data.vn(op_input(data, most, 0)).get_space_from_const(&glb.manager);
        if most_space.as_ref().map(|space| space.get_index()) != least_space.as_ref().map(|space| space.get_index()) {
            return false;
        }
        let Some(space) = least_space else {
            return false;
        };
        let (first_op, second_op) = if space.is_big_endian() {
            (most, least)
        } else {
            (least, most)
        };
        *first = Some(first_op);
        *second = Some(second_op);
        let firstptr = op_input(data, first_op, 1);
        if data.vn(firstptr).is_free() {
            return false;
        }
        let sizeres = if data.op(first_op).code() == OpCode::Load {
            data.vn(op_out(data, first_op)).get_size()
        } else {
            data.vn(op_input(data, first_op, 2)).get_size()
        };
        SplitVarnode::adjacent_offsets(
            op_input(data, first_op, 1),
            op_input(data, second_op, 1),
            sizeres as i64 as u64,
            data,
        )
    }

    pub fn is_addr_tied_contiguous(
        lo_vn: VarnodeId,
        hi_vn: VarnodeId,
        res: &mut Address,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let lo = data.vn(lo_vn);
        let hi = data.vn(hi_vn);
        if !lo.is_addr_tied() {
            return false;
        }
        if !hi.is_addr_tied() {
            return false;
        }
        let entry_lo = lo.get_symbol_entry();
        let entry_hi = hi.get_symbol_entry();
        if entry_lo.is_some() || entry_hi.is_some() {
            let (Some(entry_lo), Some(entry_hi)) = (entry_lo, entry_hi) else {
                return false;
            };
            let symboltab = glb.symboltab.as_deref().expect("architecture has no symbol table");
            if symboltab.entry(entry_lo).get_symbol() != symboltab.entry(entry_hi).get_symbol() {
                return false;
            }
        }
        let Some(spc) = lo.get_space() else {
            return false;
        };
        if !space_matches(hi.get_space(), spc) {
            return false;
        }
        let looffset = lo.get_offset();
        let hioffset = hi.get_offset();
        if spc.is_big_endian() {
            if hioffset >= looffset {
                return false;
            }
            if hioffset.wrapping_add(hi.get_size() as i64 as u64) != looffset {
                return false;
            }
            *res = hi.get_addr().clone();
        } else {
            if looffset >= hioffset {
                return false;
            }
            if looffset.wrapping_add(lo.get_size() as i64 as u64) != hioffset {
                return false;
            }
            *res = lo.get_addr().clone();
        }
        true
    }

    pub fn whole_list(whole_vn: VarnodeId, splitvec: &mut Vec<SplitVarnode>, data: &Funcdata) {
        let mut basic = SplitVarnode::new();
        basic.whole = Some(whole_vn);
        basic.hi = None;
        basic.lo = None;
        basic.wholesize = data.vn(whole_vn).get_size();
        let mut res = 0;
        for &subop in data.vn(whole_vn).descend() {
            if data.op(subop).code() != OpCode::Subpiece {
                continue;
            }
            let vn = op_out(data, subop);
            if data.vn(vn).is_precis_hi() {
                if input_offset(data, subop, 1) != (basic.wholesize - data.vn(vn).get_size()) as i64 as u64 {
                    continue;
                }
                basic.hi = Some(vn);
                res |= 2;
            } else if data.vn(vn).is_precis_lo() {
                if input_offset(data, subop, 1) != 0 {
                    continue;
                }
                basic.lo = Some(vn);
                res |= 1;
            }
        }
        if res == 0 {
            return;
        }
        if res == 3
            && (data.vn(present(basic.lo)).get_size() + data.vn(present(basic.hi)).get_size() != basic.wholesize)
        {
            return;
        }
        splitvec.push(basic.clone());
        SplitVarnode::find_copies(&basic, splitvec, data);
    }

    pub fn find_copies(input: &SplitVarnode, splitvec: &mut Vec<SplitVarnode>, data: &Funcdata) {
        if !input.has_both_pieces() {
            return;
        }
        let lo = present(input.lo);
        let hi = present(input.hi);
        for &lo_op in data.vn(lo).descend() {
            if data.op(lo_op).code() != OpCode::Copy {
                continue;
            }
            let locpy = op_out(data, lo_op);
            let mut addr = data.vn(locpy).get_addr().clone();
            if addr.is_big_endian() {
                addr = addr.sub(data.vn(hi).get_size() as i64);
            } else {
                addr = addr.add(data.vn(locpy).get_size() as i64);
            }
            for &hiop in data.vn(hi).descend() {
                if data.op(hiop).code() != OpCode::Copy {
                    continue;
                }
                let hicpy = op_out(data, hiop);
                if *data.vn(hicpy).get_addr() != addr {
                    continue;
                }
                if data.op(hiop).get_parent() != data.op(lo_op).get_parent() {
                    continue;
                }
                let mut newsplit = SplitVarnode::new();
                newsplit.init_all(present(input.whole), locpy, Some(hicpy), data);
                splitvec.push(newsplit);
            }
        }
    }

    pub fn get_true_false(
        boolop: OpId,
        flip: bool,
        trueout: &mut Option<BlockId>,
        falseout: &mut Option<BlockId>,
        data: &Funcdata,
    ) {
        let parent = data.block(op_block(data, boolop));
        let trueblock = parent.get_true_out();
        let falseblock = parent.get_false_out();
        if data.op(boolop).is_boolean_flip() != flip {
            *trueout = Some(falseblock);
            *falseout = Some(trueblock);
        } else {
            *trueout = Some(trueblock);
            *falseout = Some(falseblock);
        }
    }

    pub fn otherwise_empty(branchop: OpId, data: &Funcdata) -> bool {
        let bl = op_block(data, branchop);
        if data.block(bl).size_in() != 1 {
            return false;
        }
        let vn = op_input(data, branchop, 1);
        let otherop = if data.vn(vn).is_written() {
            data.vn(vn).get_def()
        } else {
            None
        };
        let mut iter = data.block(bl).get_op_list().front();
        while let Some(op) = iter {
            iter = next_basic_op(data, op);
            if Some(op) == otherop {
                continue;
            }
            if op == branchop {
                continue;
            }
            return false;
        }
        true
    }

    pub fn prepare_binary_op(
        out: &mut SplitVarnode,
        in1: &mut SplitVarnode,
        in2: &mut SplitVarnode,
        data: &Funcdata,
    ) -> Result<Option<OpId>> {
        let Some(existop) = out.find_out_exist(data)? else {
            return Ok(None);
        };
        if !in1.is_whole_feasible(existop, data)? {
            return Ok(None);
        }
        if !in2.is_whole_feasible(existop, data)? {
            return Ok(None);
        }
        Ok(Some(existop))
    }

    pub fn create_binary_op(
        data: &mut Funcdata,
        glb: &mut Architecture,
        out: &mut SplitVarnode,
        in1: &mut SplitVarnode,
        in2: &mut SplitVarnode,
        existop: OpId,
        opc: OpCode,
    ) -> Result<()> {
        out.find_create_output_whole(data, glb)?;
        in1.find_create_whole(data, glb)?;
        in2.find_create_whole(data, glb)?;
        if data.op(existop).code() != OpCode::Piece {
            let addr = data.op(existop).get_addr().clone();
            let newop = data.new_op(2, &addr);
            data.op_set_opcode(newop, opc, glb);
            data.op_set_output(newop, present(out.whole), glb)?;
            data.op_set_input(newop, present(in1.whole), 0)?;
            data.op_set_input(newop, present(in2.whole), 1)?;
            data.op_insert_before(newop, existop);
            out.build_lo_from_whole(data, glb)?;
            out.build_hi_from_whole(data, glb)?;
        } else {
            data.op_set_opcode(existop, opc, glb);
            data.op_set_input(existop, present(in1.whole), 0)?;
            data.op_set_input(existop, present(in2.whole), 1)?;
        }
        Ok(())
    }

    pub fn prepare_shift_op(out: &mut SplitVarnode, input: &mut SplitVarnode, data: &Funcdata) -> Result<Option<OpId>> {
        let Some(existop) = out.find_out_exist(data)? else {
            return Ok(None);
        };
        if !input.is_whole_feasible(existop, data)? {
            return Ok(None);
        }
        Ok(Some(existop))
    }

    pub fn create_shift_op(
        data: &mut Funcdata,
        glb: &mut Architecture,
        out: &mut SplitVarnode,
        input: &mut SplitVarnode,
        shift_amount: VarnodeId,
        existop: OpId,
        opc: OpCode,
    ) -> Result<()> {
        out.find_create_output_whole(data, glb)?;
        input.find_create_whole(data, glb)?;
        let mut shift_vn = shift_amount;
        if data.vn(shift_vn).is_constant() {
            let size = data.vn(shift_vn).get_size();
            let offset = data.vn(shift_vn).get_offset();
            shift_vn = data.new_constant(size, offset, glb);
        }
        if data.op(existop).code() != OpCode::Piece {
            let addr = data.op(existop).get_addr().clone();
            let newop = data.new_op(2, &addr);
            data.op_set_opcode(newop, opc, glb);
            data.op_set_output(newop, present(out.whole), glb)?;
            data.op_set_input(newop, present(input.whole), 0)?;
            data.op_set_input(newop, shift_vn, 1)?;
            data.op_insert_before(newop, existop);
            out.build_lo_from_whole(data, glb)?;
            out.build_hi_from_whole(data, glb)?;
        } else {
            data.op_set_opcode(existop, opc, glb);
            data.op_set_input(existop, present(input.whole), 0)?;
            data.op_set_input(existop, shift_vn, 1)?;
        }
        Ok(())
    }

    pub fn replace_bool_op(
        data: &mut Funcdata,
        glb: &mut Architecture,
        boolop: OpId,
        in1: &mut SplitVarnode,
        in2: &mut SplitVarnode,
        opc: OpCode,
    ) -> Result<()> {
        in1.find_create_whole(data, glb)?;
        in2.find_create_whole(data, glb)?;
        data.op_set_opcode(boolop, opc, glb);
        data.op_set_input(boolop, present(in1.whole), 0)?;
        data.op_set_input(boolop, present(in2.whole), 1)?;
        Ok(())
    }

    pub fn prepare_bool_op(
        in1: &mut SplitVarnode,
        in2: &mut SplitVarnode,
        testop: OpId,
        data: &Funcdata,
    ) -> Result<bool> {
        if !in1.is_whole_feasible(testop, data)? {
            return Ok(false);
        }
        if !in2.is_whole_feasible(testop, data)? {
            return Ok(false);
        }
        Ok(true)
    }

    pub fn create_bool_op(
        data: &mut Funcdata,
        glb: &mut Architecture,
        cbranch: OpId,
        in1: &mut SplitVarnode,
        in2: &mut SplitVarnode,
        opc: OpCode,
    ) -> Result<()> {
        let mut addrop = cbranch;
        let boolvn = op_input(data, cbranch, 1);
        if data.vn(boolvn).is_written() {
            addrop = def_op(data, boolvn);
        }
        in1.find_create_whole(data, glb)?;
        in2.find_create_whole(data, glb)?;
        let addr = data.op(addrop).get_addr().clone();
        let newop = data.new_op(2, &addr);
        data.op_set_opcode(newop, opc, glb);
        let newbool = data.new_unique_out(1, newop, glb)?;
        data.op_set_input(newop, present(in1.whole), 0)?;
        data.op_set_input(newop, present(in2.whole), 1)?;
        data.op_insert_before(newop, cbranch);
        data.op_set_input(cbranch, newbool, 1)?;
        Ok(())
    }

    pub fn prepare_phi_op(
        out: &mut SplitVarnode,
        inlist: &mut [SplitVarnode],
        data: &Funcdata,
    ) -> Result<Option<OpId>> {
        let Some(existop) = out.find_earliest_split_point(data) else {
            return Ok(None);
        };
        if data.op(existop).code() != OpCode::Multiequal {
            return Err(Error::Lowlevel(
                "Trying to create phi-node double precision op with phi-node pieces".to_string(),
            ));
        }
        let bl = op_block(data, existop);
        for (index, item) in inlist.iter_mut().enumerate() {
            let inblock = data.block(bl).get_in(index as i32);
            if !item.is_whole_phi_feasible(inblock, data)? {
                return Ok(None);
            }
        }
        Ok(Some(existop))
    }

    pub fn create_phi_op(
        data: &mut Funcdata,
        glb: &mut Architecture,
        out: &mut SplitVarnode,
        inlist: &mut [SplitVarnode],
        existop: OpId,
    ) -> Result<()> {
        out.find_create_output_whole(data, glb)?;
        let numin = inlist.len();
        for item in inlist.iter_mut() {
            item.find_create_whole(data, glb)?;
        }
        let addr = data.op(existop).get_addr().clone();
        let newop = data.new_op(numin as i32, &addr);
        data.op_set_opcode(newop, OpCode::Multiequal, glb);
        data.op_set_output(newop, present(out.whole), glb)?;
        for (index, item) in inlist.iter().enumerate() {
            data.op_set_input(newop, present(item.whole), index as i32)?;
        }
        data.op_insert_before(newop, existop);
        out.build_lo_from_whole(data, glb)?;
        out.build_hi_from_whole(data, glb)?;
        Ok(())
    }

    pub fn prepare_indirect_op(input: &mut SplitVarnode, affector: OpId, data: &Funcdata) -> Result<bool> {
        if !input.is_whole_feasible(affector, data)? {
            return Ok(false);
        }
        Ok(true)
    }

    pub fn replace_indirect_op(
        data: &mut Funcdata,
        glb: &mut Architecture,
        out: &mut SplitVarnode,
        input: &mut SplitVarnode,
        affector: OpId,
    ) -> Result<()> {
        out.create_joined_whole(data, glb)?;
        input.find_create_whole(data, glb)?;
        let newop = data.new_indirect(affector, glb)?;
        data.op_set_output(newop, present(out.whole), glb)?;
        data.op_set_input(newop, present(input.whole), 0)?;
        data.op_insert_before(newop, affector);
        out.build_lo_from_whole(data, glb)?;
        out.build_hi_from_whole(data, glb)?;
        Ok(())
    }

    pub fn replace_copy_force(
        data: &mut Funcdata,
        glb: &mut Architecture,
        addr: &Address,
        input: &mut SplitVarnode,
        copylo: OpId,
        copyhi: OpId,
    ) -> Result<()> {
        let mut in_vn = present(input.whole);
        let return_form = data.op(copyhi).is_return_copy();
        if return_form && data.vn(in_vn).get_addr() != addr {
            let mut other_point1 = def_op(data, op_input(data, copyhi, 0));
            let other_point2 = def_op(data, op_input(data, copylo, 0));
            if op_order(data, other_point1) < op_order(data, other_point2) {
                other_point1 = other_point2;
            }
            let other_addr = data.op(other_point1).get_addr().clone();
            let other_copy = data.new_op(1, &other_addr);
            data.op_set_opcode(other_copy, OpCode::Copy, glb);
            let vn = data.new_varnode_out(input.get_size(), addr, other_copy, glb)?;
            data.op_set_input(other_copy, in_vn, 0)?;
            data.op_insert_before(other_copy, other_point1);
            in_vn = vn;
        }
        let copy_addr = data.op(copyhi).get_addr().clone();
        let whole_copy = data.new_op(1, &copy_addr);
        data.op_set_opcode(whole_copy, OpCode::Copy, glb);
        let out_vn = data.new_varnode_out(input.get_size(), addr, whole_copy, glb)?;
        data.vbank.get_mut(out_vn).set_addr_force(&mut data.highs);
        if return_form {
            data.mark_return_copy(whole_copy);
        }
        data.op_set_input(whole_copy, in_vn, 0)?;
        data.op_insert_before(whole_copy, copyhi);
        data.op_destroy(copyhi)?;
        data.op_destroy(copylo)?;
        Ok(())
    }

    pub fn apply_rule_in(input: &mut SplitVarnode, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        for index in 0..2 {
            let piece = if index == 0 { input.get_hi() } else { input.get_lo() };
            let Some(vn) = piece else {
                continue;
            };
            let workishi = index == 0;
            let mut position = 0;
            while position < data.vn(vn).descend().len() {
                let workop = data.vn(vn).descend()[position];
                position += 1;
                match data.op(workop).code() {
                    OpCode::IntAdd => {
                        let mut addform = AddForm::new();
                        if addform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                        let mut subform = SubForm::new();
                        if subform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntAnd => {
                        let mut equal3form = Equal3Form::new();
                        if equal3form.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                        let mut logicalform = LogicalForm::new();
                        if logicalform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntOr | OpCode::IntXor => {
                        let mut logicalform = LogicalForm::new();
                        if logicalform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntEqual | OpCode::IntNotequal => {
                        let mut lessthreeway = LessThreeWay::new();
                        if lessthreeway.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                        let mut equal1form = Equal1Form::new();
                        if equal1form.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                        let mut equal2form = Equal2Form::new();
                        if equal2form.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntLess | OpCode::IntLessequal => {
                        let mut lessthreeway = LessThreeWay::new();
                        if lessthreeway.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                        let mut lessconstform = LessConstForm::new();
                        if lessconstform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntSless | OpCode::IntSlessequal => {
                        let mut lessconstform = LessConstForm::new();
                        if lessconstform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntLeft => {
                        let mut shiftform = ShiftForm::new();
                        if shiftform.apply_rule_left(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntRight | OpCode::IntSright => {
                        let mut shiftform = ShiftForm::new();
                        if shiftform.apply_rule_right(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::IntMult => {
                        let mut multform = MultForm::new();
                        if multform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::Multiequal => {
                        let mut phiform = PhiForm::new();
                        if phiform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::Indirect => {
                        let mut indform = IndirectForm::new();
                        if indform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    OpCode::Copy if data.vn(op_out(data, workop)).is_addr_force() => {
                        let mut copyform = CopyForceForm::new();
                        if copyform.apply_rule(input, workop, workishi, data, glb)? {
                            return Ok(1);
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(0)
    }
}

#[derive(Clone, Debug)]
pub struct AddForm {
    pub(crate) input: SplitVarnode,
    pub(crate) hi1: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo1: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) reshi: Option<VarnodeId>,
    pub(crate) reslo: Option<VarnodeId>,
    pub(crate) zextop: Option<OpId>,
    pub(crate) loadd: Option<OpId>,
    pub(crate) add2: Option<OpId>,
    pub(crate) hizext1: Option<VarnodeId>,
    pub(crate) hizext2: Option<VarnodeId>,
    pub(crate) slot1: i32,
    pub(crate) negconst: u64,
    pub(crate) existop: Option<OpId>,
    pub(crate) indoub: SplitVarnode,
    pub(crate) outdoub: SplitVarnode,
}

impl Default for AddForm {
    fn default() -> AddForm {
        AddForm::new()
    }
}

impl AddForm {
    pub fn new() -> AddForm {
        AddForm {
            input: SplitVarnode::new(),
            hi1: None,
            hi2: None,
            lo1: None,
            lo2: None,
            reshi: None,
            reslo: None,
            zextop: None,
            loadd: None,
            add2: None,
            hizext1: None,
            hizext2: None,
            slot1: 0,
            negconst: 0,
            existop: None,
            indoub: SplitVarnode::new(),
            outdoub: SplitVarnode::new(),
        }
    }

    fn check_for_carry(&mut self, op: OpId, data: &Funcdata) -> bool {
        if data.op(op).code() != OpCode::IntZext {
            return false;
        }
        let carryin = op_input(data, op, 0);
        if !data.vn(carryin).is_written() {
            return false;
        }
        let lo1 = present(self.lo1);
        let carryop = def_op(data, carryin);
        match data.op(carryop).code() {
            OpCode::IntCarry => {
                if op_input(data, carryop, 0) == lo1 {
                    self.lo2 = Some(op_input(data, carryop, 1));
                } else if op_input(data, carryop, 1) == lo1 {
                    self.lo2 = Some(op_input(data, carryop, 0));
                } else {
                    return false;
                }
                if data.vn(present(self.lo2)).is_constant() {
                    return false;
                }
                true
            }
            OpCode::IntLess => {
                let tmpvn = op_input(data, carryop, 0);
                if data.vn(tmpvn).is_constant() {
                    if op_input(data, carryop, 1) != lo1 {
                        return false;
                    }
                    self.negconst = data.vn(tmpvn).get_offset();
                    self.negconst = (!self.negconst) & calc_mask(data.vn(lo1).get_size());
                    self.lo2 = None;
                    return true;
                } else if data.vn(tmpvn).is_written() {
                    let loadd_op = def_op(data, tmpvn);
                    if data.op(loadd_op).code() != OpCode::IntAdd {
                        return false;
                    }
                    let othervn = if op_input(data, loadd_op, 0) == lo1 {
                        op_input(data, loadd_op, 1)
                    } else if op_input(data, loadd_op, 1) == lo1 {
                        op_input(data, loadd_op, 0)
                    } else {
                        return false;
                    };
                    if data.vn(othervn).is_constant() {
                        self.negconst = data.vn(othervn).get_offset();
                        self.lo2 = None;
                        let relvn = op_input(data, carryop, 1);
                        if relvn == lo1 {
                            return true;
                        }
                        if !data.vn(relvn).is_constant() {
                            return false;
                        }
                        if data.vn(relvn).get_offset() != self.negconst {
                            return false;
                        }
                        return true;
                    } else {
                        self.lo2 = Some(othervn);
                        let compvn = op_input(data, carryop, 1);
                        if compvn == othervn || compvn == lo1 {
                            return true;
                        }
                    }
                }
                false
            }
            OpCode::IntNotequal => {
                if !data.vn(op_input(data, carryop, 1)).is_constant() {
                    return false;
                }
                if op_input(data, carryop, 0) != lo1 {
                    return false;
                }
                if input_offset(data, carryop, 1) != 0 {
                    return false;
                }
                self.negconst = calc_mask(data.vn(lo1).get_size());
                self.lo2 = None;
                true
            }
            _ => false,
        }
    }

    pub fn verify(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, op: OpId, data: &Funcdata) -> bool {
        self.hi1 = Some(hi_vn);
        self.lo1 = Some(lo_vn);
        self.slot1 = data.op(op).get_slot(hi_vn);
        let opout = op_out(data, op);
        for index in 0..3 {
            if index == 0 {
                self.add2 = data.vn(opout).lone_descend();
                let Some(add2) = self.add2 else {
                    continue;
                };
                if data.op(add2).code() != OpCode::IntAdd {
                    continue;
                }
                self.reshi = data.op(add2).get_out();
                self.hizext1 = Some(op_input(data, op, 1 - self.slot1));
                self.hizext2 = Some(op_input(data, add2, 1 - data.op(add2).get_slot(opout)));
            } else if index == 1 {
                let tmpvn = op_input(data, op, 1 - self.slot1);
                if !data.vn(tmpvn).is_written() {
                    continue;
                }
                let add2 = def_op(data, tmpvn);
                self.add2 = Some(add2);
                if data.op(add2).code() != OpCode::IntAdd {
                    continue;
                }
                self.reshi = Some(opout);
                self.hizext1 = Some(op_input(data, add2, 0));
                self.hizext2 = Some(op_input(data, add2, 1));
            } else {
                self.reshi = Some(opout);
                self.hizext1 = Some(op_input(data, op, 1 - self.slot1));
                self.hizext2 = None;
            }
            for inner in 0..2 {
                if index == 2 {
                    let hizext1 = present(self.hizext1);
                    if !data.vn(hizext1).is_written() {
                        continue;
                    }
                    self.zextop = Some(def_op(data, hizext1));
                    self.hi2 = None;
                } else if inner == 0 {
                    let hizext1 = present(self.hizext1);
                    if !data.vn(hizext1).is_written() {
                        continue;
                    }
                    self.zextop = Some(def_op(data, hizext1));
                    self.hi2 = self.hizext2;
                } else {
                    let hizext2 = present(self.hizext2);
                    if !data.vn(hizext2).is_written() {
                        continue;
                    }
                    self.zextop = Some(def_op(data, hizext2));
                    self.hi2 = self.hizext1;
                }
                if !self.check_for_carry(present(self.zextop), data) {
                    continue;
                }
                for &loadd in data.vn(lo_vn).descend() {
                    self.loadd = Some(loadd);
                    if data.op(loadd).code() != OpCode::IntAdd {
                        continue;
                    }
                    let tmpvn = op_input(data, loadd, 1 - data.op(loadd).get_slot(lo_vn));
                    match self.lo2 {
                        None => {
                            if !data.vn(tmpvn).is_constant() {
                                continue;
                            }
                            if data.vn(tmpvn).get_offset() != self.negconst {
                                continue;
                            }
                            self.lo2 = Some(tmpvn);
                        }
                        Some(lo2) if data.vn(lo2).is_constant() => {
                            if !data.vn(tmpvn).is_constant() {
                                continue;
                            }
                            if data.vn(lo2).get_offset() != data.vn(tmpvn).get_offset() {
                                continue;
                            }
                        }
                        Some(lo2) => {
                            if tmpvn != lo2 {
                                continue;
                            }
                        }
                    }
                    self.reslo = data.op(loadd).get_out();
                    return true;
                }
            }
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(present(self.input.get_hi()), present(self.input.get_lo()), op, data) {
            return Ok(false);
        }
        let size = self.input.get_size();
        self.indoub.init_partial(size, present(self.lo2), self.hi2, data);
        if self.indoub.exceeds_const_precision() {
            return Ok(false);
        }
        self.outdoub.init_partial(size, present(self.reslo), self.reshi, data);
        self.existop = SplitVarnode::prepare_binary_op(&mut self.outdoub, &mut self.input, &mut self.indoub, data)?;
        let Some(existop) = self.existop else {
            return Ok(false);
        };
        SplitVarnode::create_binary_op(
            data,
            glb,
            &mut self.outdoub,
            &mut self.input,
            &mut self.indoub,
            existop,
            OpCode::IntAdd,
        )?;
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct SubForm {
    pub(crate) input: SplitVarnode,
    pub(crate) hi1: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo1: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) reshi: Option<VarnodeId>,
    pub(crate) reslo: Option<VarnodeId>,
    pub(crate) zextop: Option<OpId>,
    pub(crate) lessop: Option<OpId>,
    pub(crate) negop: Option<OpId>,
    pub(crate) loadd: Option<OpId>,
    pub(crate) add2: Option<OpId>,
    pub(crate) hineg1: Option<VarnodeId>,
    pub(crate) hineg2: Option<VarnodeId>,
    pub(crate) hizext1: Option<VarnodeId>,
    pub(crate) hizext2: Option<VarnodeId>,
    pub(crate) slot1: i32,
    pub(crate) existop: Option<OpId>,
    pub(crate) indoub: SplitVarnode,
    pub(crate) outdoub: SplitVarnode,
}

impl Default for SubForm {
    fn default() -> SubForm {
        SubForm::new()
    }
}

impl SubForm {
    pub fn new() -> SubForm {
        SubForm {
            input: SplitVarnode::new(),
            hi1: None,
            hi2: None,
            lo1: None,
            lo2: None,
            reshi: None,
            reslo: None,
            zextop: None,
            lessop: None,
            negop: None,
            loadd: None,
            add2: None,
            hineg1: None,
            hineg2: None,
            hizext1: None,
            hizext2: None,
            slot1: 0,
            existop: None,
            indoub: SplitVarnode::new(),
            outdoub: SplitVarnode::new(),
        }
    }

    pub fn verify(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, op: OpId, data: &Funcdata) -> bool {
        self.hi1 = Some(hi_vn);
        self.lo1 = Some(lo_vn);
        self.slot1 = data.op(op).get_slot(hi_vn);
        let opout = op_out(data, op);
        for index in 0..2 {
            if index == 0 {
                self.add2 = data.vn(opout).lone_descend();
                let Some(add2) = self.add2 else {
                    continue;
                };
                if data.op(add2).code() != OpCode::IntAdd {
                    continue;
                }
                self.reshi = data.op(add2).get_out();
                self.hineg1 = Some(op_input(data, op, 1 - self.slot1));
                self.hineg2 = Some(op_input(data, add2, 1 - data.op(add2).get_slot(opout)));
            } else {
                let tmpvn = op_input(data, op, 1 - self.slot1);
                if !data.vn(tmpvn).is_written() {
                    continue;
                }
                let add2 = def_op(data, tmpvn);
                self.add2 = Some(add2);
                if data.op(add2).code() != OpCode::IntAdd {
                    continue;
                }
                self.reshi = Some(opout);
                self.hineg1 = Some(op_input(data, add2, 0));
                self.hineg2 = Some(op_input(data, add2, 1));
            }
            let hineg1 = present(self.hineg1);
            let hineg2 = present(self.hineg2);
            if !data.vn(hineg1).is_written() {
                continue;
            }
            if !data.vn(hineg2).is_written() {
                continue;
            }
            if !data.op_verify_mult_neg_one(def_op(data, hineg1)) {
                continue;
            }
            if !data.op_verify_mult_neg_one(def_op(data, hineg2)) {
                continue;
            }
            self.hizext1 = Some(op_input(data, def_op(data, hineg1), 0));
            self.hizext2 = Some(op_input(data, def_op(data, hineg2), 0));
            for inner in 0..2 {
                if inner == 0 {
                    let hizext1 = present(self.hizext1);
                    if !data.vn(hizext1).is_written() {
                        continue;
                    }
                    self.zextop = Some(def_op(data, hizext1));
                    self.hi2 = self.hizext2;
                } else {
                    let hizext2 = present(self.hizext2);
                    if !data.vn(hizext2).is_written() {
                        continue;
                    }
                    self.zextop = Some(def_op(data, hizext2));
                    self.hi2 = self.hizext1;
                }
                let zextop = present(self.zextop);
                if data.op(zextop).code() != OpCode::IntZext {
                    continue;
                }
                let zextin = op_input(data, zextop, 0);
                if !data.vn(zextin).is_written() {
                    continue;
                }
                let lessop = def_op(data, zextin);
                self.lessop = Some(lessop);
                if data.op(lessop).code() != OpCode::IntLess {
                    continue;
                }
                if op_input(data, lessop, 0) != lo_vn {
                    continue;
                }
                let lo2 = op_input(data, lessop, 1);
                self.lo2 = Some(lo2);
                for &loadd in data.vn(lo_vn).descend() {
                    self.loadd = Some(loadd);
                    if data.op(loadd).code() != OpCode::IntAdd {
                        continue;
                    }
                    let tmpvn = op_input(data, loadd, 1 - data.op(loadd).get_slot(lo_vn));
                    if !data.vn(tmpvn).is_written() {
                        continue;
                    }
                    let negop = def_op(data, tmpvn);
                    self.negop = Some(negop);
                    if !data.op_verify_mult_neg_one(negop) {
                        continue;
                    }
                    if op_input(data, negop, 0) != lo2 {
                        continue;
                    }
                    self.reslo = data.op(loadd).get_out();
                    return true;
                }
            }
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(present(self.input.get_hi()), present(self.input.get_lo()), op, data) {
            return Ok(false);
        }
        let size = self.input.get_size();
        self.indoub.init_partial(size, present(self.lo2), self.hi2, data);
        if self.indoub.exceeds_const_precision() {
            return Ok(false);
        }
        self.outdoub.init_partial(size, present(self.reslo), self.reshi, data);
        self.existop = SplitVarnode::prepare_binary_op(&mut self.outdoub, &mut self.input, &mut self.indoub, data)?;
        let Some(existop) = self.existop else {
            return Ok(false);
        };
        SplitVarnode::create_binary_op(
            data,
            glb,
            &mut self.outdoub,
            &mut self.input,
            &mut self.indoub,
            existop,
            OpCode::IntSub,
        )?;
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct LogicalForm {
    pub(crate) input: SplitVarnode,
    pub(crate) lo_op: Option<OpId>,
    pub(crate) hiop: Option<OpId>,
    pub(crate) hi1: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo1: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) existop: Option<OpId>,
    pub(crate) indoub: SplitVarnode,
    pub(crate) outdoub: SplitVarnode,
}

impl Default for LogicalForm {
    fn default() -> LogicalForm {
        LogicalForm::new()
    }
}

impl LogicalForm {
    pub fn new() -> LogicalForm {
        LogicalForm {
            input: SplitVarnode::new(),
            lo_op: None,
            hiop: None,
            hi1: None,
            hi2: None,
            lo1: None,
            lo2: None,
            existop: None,
            indoub: SplitVarnode::new(),
            outdoub: SplitVarnode::new(),
        }
    }

    fn find_hi_match(&mut self, data: &Funcdata) -> i32 {
        let lo1_tmp = present(self.input.get_lo());
        let lo_op = present(self.lo_op);
        let hi1 = present(self.hi1);
        let lo_code = data.op(lo_op).code();
        let vn2 = op_input(data, lo_op, 1 - data.op(lo_op).get_slot(lo1_tmp));

        let mut out = SplitVarnode::new();
        if out.in_hand_lo_out(lo1_tmp, data) {
            let hi = present(out.get_hi());
            if data.vn(hi).is_written() {
                let maybeop = def_op(data, hi);
                if data.op(maybeop).code() == lo_code {
                    if op_input(data, maybeop, 0) == hi1 {
                        if data.vn(op_input(data, maybeop, 1)).is_constant() == data.vn(vn2).is_constant() {
                            self.hiop = Some(maybeop);
                            return 0;
                        }
                    } else if op_input(data, maybeop, 1) == hi1
                        && data.vn(op_input(data, maybeop, 0)).is_constant() == data.vn(vn2).is_constant()
                    {
                        self.hiop = Some(maybeop);
                        return 0;
                    }
                }
            }
        }

        if !data.vn(vn2).is_constant() {
            let mut in2 = SplitVarnode::new();
            if in2.in_hand_lo(vn2, data) {
                for &maybeop in data.vn(present(in2.get_hi())).descend() {
                    if data.op(maybeop).code() == lo_code
                        && (op_input(data, maybeop, 0) == hi1 || op_input(data, maybeop, 1) == hi1)
                    {
                        self.hiop = Some(maybeop);
                        return 0;
                    }
                }
            }
            return -1;
        } else {
            let mut count = 0;
            let mut lastop: Option<OpId> = None;
            for &maybeop in data.vn(hi1).descend() {
                if data.op(maybeop).code() == lo_code && data.vn(op_input(data, maybeop, 1)).is_constant() {
                    count += 1;
                    if count > 1 {
                        break;
                    }
                    lastop = Some(maybeop);
                }
            }
            if count == 1 {
                self.hiop = lastop;
                return 0;
            }
            if count > 1 {
                return -1;
            }
        }
        -2
    }

    pub fn verify(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, lo_op: OpId, data: &Funcdata) -> bool {
        self.lo_op = Some(lo_op);
        self.lo1 = Some(lo_vn);
        self.hi1 = Some(hi_vn);
        let res = self.find_hi_match(data);
        if res == 0 {
            let hiop = present(self.hiop);
            let lo2 = op_input(data, lo_op, 1 - data.op(lo_op).get_slot(lo_vn));
            let hi2 = op_input(data, hiop, 1 - data.op(hiop).get_slot(hi_vn));
            self.lo2 = Some(lo2);
            self.hi2 = Some(hi2);
            if lo2 == lo_vn || lo2 == hi_vn || hi2 == hi_vn || hi2 == lo_vn {
                return false;
            }
            if lo2 == hi2 {
                return false;
            }
            return true;
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        lo_op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(present(self.input.get_hi()), present(self.input.get_lo()), lo_op, data) {
            return Ok(false);
        }
        let size = self.input.get_size();
        let hiop = present(self.hiop);
        self.outdoub
            .init_partial(size, op_out(data, lo_op), data.op(hiop).get_out(), data);
        self.indoub.init_partial(size, present(self.lo2), self.hi2, data);
        if self.indoub.exceeds_const_precision() {
            return Ok(false);
        }
        self.existop = SplitVarnode::prepare_binary_op(&mut self.outdoub, &mut self.input, &mut self.indoub, data)?;
        let Some(existop) = self.existop else {
            return Ok(false);
        };
        let opc = data.op(lo_op).code();
        SplitVarnode::create_binary_op(
            data,
            glb,
            &mut self.outdoub,
            &mut self.input,
            &mut self.indoub,
            existop,
            opc,
        )?;
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct Equal1Form {
    pub(crate) in1: SplitVarnode,
    pub(crate) in2: SplitVarnode,
    pub(crate) lo_op: Option<OpId>,
    pub(crate) hiop: Option<OpId>,
    pub(crate) hibool: Option<OpId>,
    pub(crate) lobool: Option<OpId>,
    pub(crate) hi1: Option<VarnodeId>,
    pub(crate) lo1: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) hi1slot: i32,
    pub(crate) lo1slot: i32,
    pub(crate) notequalformhi: bool,
    pub(crate) notequalformlo: bool,
    pub(crate) setonlow: bool,
}

impl Default for Equal1Form {
    fn default() -> Equal1Form {
        Equal1Form::new()
    }
}

impl Equal1Form {
    pub fn new() -> Equal1Form {
        Equal1Form {
            in1: SplitVarnode::new(),
            in2: SplitVarnode::new(),
            lo_op: None,
            hiop: None,
            hibool: None,
            lobool: None,
            hi1: None,
            lo1: None,
            hi2: None,
            lo2: None,
            hi1slot: 0,
            lo1slot: 0,
            notequalformhi: false,
            notequalformlo: false,
            setonlow: false,
        }
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        hop: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.in1 = split_in.clone();
        self.hiop = Some(hop);
        let hi1 = present(self.in1.get_hi());
        let lo1 = present(self.in1.get_lo());
        self.hi1 = Some(hi1);
        self.lo1 = Some(lo1);
        self.hi1slot = data.op(hop).get_slot(hi1);
        let hi2 = op_input(data, hop, 1 - self.hi1slot);
        self.hi2 = Some(hi2);
        self.notequalformhi = data.op(hop).code() == OpCode::IntNotequal;

        let lo_descend = data.vn(lo1).descend().to_vec();
        for lo_op in lo_descend {
            self.lo_op = Some(lo_op);
            match data.op(lo_op).code() {
                OpCode::IntEqual => self.notequalformlo = false,
                OpCode::IntNotequal => self.notequalformlo = true,
                _ => continue,
            }
            self.lo1slot = data.op(lo_op).get_slot(lo1);
            let lo2 = op_input(data, lo_op, 1 - self.lo1slot);
            self.lo2 = Some(lo2);

            let hi_descend = data.vn(op_out(data, hop)).descend().to_vec();
            for hibool in hi_descend {
                self.hibool = Some(hibool);
                let lo_bool_descend = data.vn(op_out(data, lo_op)).descend().to_vec();
                for lobool in lo_bool_descend {
                    self.lobool = Some(lobool);

                    let size = self.in1.get_size();
                    self.in2.init_partial(size, lo2, Some(hi2), data);
                    if self.in2.exceeds_const_precision() {
                        continue;
                    }

                    if data.op(hibool).code() == OpCode::Cbranch && data.op(lobool).code() == OpCode::Cbranch {
                        let mut hibooltrue = None;
                        let mut hiboolfalse = None;
                        let mut lobooltrue = None;
                        let mut loboolfalse = None;
                        SplitVarnode::get_true_false(
                            hibool,
                            self.notequalformhi,
                            &mut hibooltrue,
                            &mut hiboolfalse,
                            data,
                        );
                        SplitVarnode::get_true_false(
                            lobool,
                            self.notequalformlo,
                            &mut lobooltrue,
                            &mut loboolfalse,
                            data,
                        );

                        if hibooltrue == data.op(lobool).get_parent()
                            && hiboolfalse == loboolfalse
                            && SplitVarnode::otherwise_empty(lobool, data)
                        {
                            if SplitVarnode::prepare_bool_op(&mut self.in1, &mut self.in2, hibool, data)? {
                                self.setonlow = true;
                                let opc = if self.notequalformhi {
                                    OpCode::IntNotequal
                                } else {
                                    OpCode::IntEqual
                                };
                                SplitVarnode::create_bool_op(data, glb, hibool, &mut self.in1, &mut self.in2, opc)?;
                                let constvn = data.new_constant(1, if self.notequalformlo { 0 } else { 1 }, glb);
                                data.op_set_input(lobool, constvn, 1)?;
                                return Ok(true);
                            }
                        } else if lobooltrue == data.op(hibool).get_parent()
                            && hiboolfalse == loboolfalse
                            && SplitVarnode::otherwise_empty(hibool, data)
                            && SplitVarnode::prepare_bool_op(&mut self.in1, &mut self.in2, lobool, data)?
                        {
                            self.setonlow = false;
                            let opc = if self.notequalformlo {
                                OpCode::IntNotequal
                            } else {
                                OpCode::IntEqual
                            };
                            SplitVarnode::create_bool_op(data, glb, lobool, &mut self.in1, &mut self.in2, opc)?;
                            let constvn = data.new_constant(1, if self.notequalformhi { 0 } else { 1 }, glb);
                            data.op_set_input(hibool, constvn, 1)?;
                            return Ok(true);
                        }
                    }
                }
            }
        }
        Ok(false)
    }
}

#[derive(Clone, Debug)]
pub struct Equal2Form {
    pub(crate) input: SplitVarnode,
    pub(crate) hi1: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo1: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) bool_and_or: Option<OpId>,
    pub(crate) param2: SplitVarnode,
}

impl Default for Equal2Form {
    fn default() -> Equal2Form {
        Equal2Form::new()
    }
}

impl Equal2Form {
    pub fn new() -> Equal2Form {
        Equal2Form {
            input: SplitVarnode::new(),
            hi1: None,
            hi2: None,
            lo1: None,
            lo2: None,
            bool_and_or: None,
            param2: SplitVarnode::new(),
        }
    }

    fn replace(&mut self, data: &Funcdata) -> Result<bool> {
        let hi2 = present(self.hi2);
        let lo2 = present(self.lo2);
        let lo1 = present(self.lo1);
        let bool_and_or = present(self.bool_and_or);
        let size = self.input.get_size();
        if data.vn(hi2).is_constant() && data.vn(lo2).is_constant() {
            let mut val = data.vn(hi2).get_offset();
            val = val.wrapping_shl((8 * data.vn(lo1).get_size()) as u32);
            val |= data.vn(lo2).get_offset();
            self.param2.init_partial_constant(size, val);
            return SplitVarnode::prepare_bool_op(&mut self.input, &mut self.param2, bool_and_or, data);
        }
        if data.vn(hi2).is_constant() || data.vn(lo2).is_constant() {
            return Ok(false);
        }
        self.param2.init_partial(size, lo2, Some(hi2), data);
        SplitVarnode::prepare_bool_op(&mut self.input, &mut self.param2, bool_and_or, data)
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        let hi1 = present(self.input.get_hi());
        let lo1 = present(self.input.get_lo());
        self.hi1 = Some(hi1);
        self.lo1 = Some(lo1);
        let eq_code = data.op(op).code();
        let hi1slot = data.op(op).get_slot(hi1);
        self.hi2 = Some(op_input(data, op, 1 - hi1slot));
        let outvn = op_out(data, op);
        let out_descend = data.vn(outvn).descend().to_vec();
        for bool_and_or in out_descend {
            self.bool_and_or = Some(bool_and_or);
            if eq_code == OpCode::IntEqual && data.op(bool_and_or).code() != OpCode::BoolAnd {
                continue;
            }
            if eq_code == OpCode::IntNotequal && data.op(bool_and_or).code() != OpCode::BoolOr {
                continue;
            }
            let slot = data.op(bool_and_or).get_slot(outvn);
            let othervn = op_input(data, bool_and_or, 1 - slot);
            if !data.vn(othervn).is_written() {
                continue;
            }
            let equal_lo = def_op(data, othervn);
            if data.op(equal_lo).code() != eq_code {
                continue;
            }
            if op_input(data, equal_lo, 0) == lo1 {
                self.lo2 = Some(op_input(data, equal_lo, 1));
            } else if op_input(data, equal_lo, 1) == lo1 {
                self.lo2 = Some(op_input(data, equal_lo, 0));
            } else {
                continue;
            }
            if !self.replace(data)? {
                continue;
            }
            if self.param2.exceeds_const_precision() {
                continue;
            }
            SplitVarnode::replace_bool_op(data, glb, bool_and_or, &mut self.input, &mut self.param2, eq_code)?;
            return Ok(true);
        }
        Ok(false)
    }
}

#[derive(Clone, Debug)]
pub struct Equal3Form {
    pub(crate) input: SplitVarnode,
    pub(crate) hi: Option<VarnodeId>,
    pub(crate) lo: Option<VarnodeId>,
    pub(crate) andop: Option<OpId>,
    pub(crate) compareop: Option<OpId>,
    pub(crate) smallc: Option<VarnodeId>,
}

impl Default for Equal3Form {
    fn default() -> Equal3Form {
        Equal3Form::new()
    }
}

impl Equal3Form {
    pub fn new() -> Equal3Form {
        Equal3Form {
            input: SplitVarnode::new(),
            hi: None,
            lo: None,
            andop: None,
            compareop: None,
            smallc: None,
        }
    }

    pub fn verify(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, aop: OpId, data: &Funcdata) -> bool {
        if data.op(aop).code() != OpCode::IntAnd {
            return false;
        }
        self.hi = Some(hi_vn);
        self.lo = Some(lo_vn);
        self.andop = Some(aop);
        let hislot = data.op(aop).get_slot(hi_vn);
        if op_input(data, aop, 1 - hislot) != lo_vn {
            return false;
        }
        self.compareop = data.vn(op_out(data, aop)).lone_descend();
        let Some(compareop) = self.compareop else {
            return false;
        };
        let compare_code = data.op(compareop).code();
        if compare_code != OpCode::IntEqual && compare_code != OpCode::IntNotequal {
            return false;
        }
        let allonesval = calc_mask(data.vn(lo_vn).get_size());
        let smallc = op_input(data, compareop, 1);
        self.smallc = Some(smallc);
        if !data.vn(smallc).is_constant() {
            return false;
        }
        if data.vn(smallc).get_offset() != allonesval {
            return false;
        }
        true
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(present(self.input.get_hi()), present(self.input.get_lo()), op, data) {
            return Ok(false);
        }
        let size = self.input.get_size();
        let mut in2 = SplitVarnode::new_constant(size, calc_mask(size));
        if in2.exceeds_const_precision() {
            return Ok(false);
        }
        let compareop = present(self.compareop);
        if !SplitVarnode::prepare_bool_op(&mut self.input, &mut in2, compareop, data)? {
            return Ok(false);
        }
        let opc = data.op(compareop).code();
        SplitVarnode::replace_bool_op(data, glb, compareop, &mut self.input, &mut in2, opc)?;
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct LessThreeWay {
    pub(crate) input: SplitVarnode,
    pub(crate) in2: SplitVarnode,
    pub(crate) hilessbl: Option<BlockId>,
    pub(crate) lolessbl: Option<BlockId>,
    pub(crate) hieqbl: Option<BlockId>,
    pub(crate) hilesstrue: Option<BlockId>,
    pub(crate) hilessfalse: Option<BlockId>,
    pub(crate) hieqtrue: Option<BlockId>,
    pub(crate) hieqfalse: Option<BlockId>,
    pub(crate) lolesstrue: Option<BlockId>,
    pub(crate) lolessfalse: Option<BlockId>,
    pub(crate) hilessbool: Option<OpId>,
    pub(crate) lolessbool: Option<OpId>,
    pub(crate) hieqbool: Option<OpId>,
    pub(crate) hiless: Option<OpId>,
    pub(crate) hiequal: Option<OpId>,
    pub(crate) loless: Option<OpId>,
    pub(crate) vnhil1: Option<VarnodeId>,
    pub(crate) vnhil2: Option<VarnodeId>,
    pub(crate) vnhie1: Option<VarnodeId>,
    pub(crate) vnhie2: Option<VarnodeId>,
    pub(crate) vnlo1: Option<VarnodeId>,
    pub(crate) vnlo2: Option<VarnodeId>,
    pub(crate) hi: Option<VarnodeId>,
    pub(crate) lo: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) hislot: i32,
    pub(crate) hiflip: bool,
    pub(crate) equalflip: bool,
    pub(crate) loflip: bool,
    pub(crate) lolessiszerocomp: bool,
    pub(crate) lolessequalform: bool,
    pub(crate) hilessequalform: bool,
    pub(crate) signcompare: bool,
    pub(crate) midlessform: bool,
    pub(crate) midlessequal: bool,
    pub(crate) midsigncompare: bool,
    pub(crate) hiconstform: bool,
    pub(crate) midconstform: bool,
    pub(crate) loconstform: bool,
    pub(crate) hival: u64,
    pub(crate) midval: u64,
    pub(crate) loval: u64,
    pub(crate) finalopc: OpCode,
}

impl Default for LessThreeWay {
    fn default() -> LessThreeWay {
        LessThreeWay::new()
    }
}

impl LessThreeWay {
    pub fn new() -> LessThreeWay {
        LessThreeWay {
            input: SplitVarnode::new(),
            in2: SplitVarnode::new(),
            hilessbl: None,
            lolessbl: None,
            hieqbl: None,
            hilesstrue: None,
            hilessfalse: None,
            hieqtrue: None,
            hieqfalse: None,
            lolesstrue: None,
            lolessfalse: None,
            hilessbool: None,
            lolessbool: None,
            hieqbool: None,
            hiless: None,
            hiequal: None,
            loless: None,
            vnhil1: None,
            vnhil2: None,
            vnhie1: None,
            vnhie2: None,
            vnlo1: None,
            vnlo2: None,
            hi: None,
            lo: None,
            hi2: None,
            lo2: None,
            hislot: 0,
            hiflip: false,
            equalflip: false,
            loflip: false,
            lolessiszerocomp: false,
            lolessequalform: false,
            hilessequalform: false,
            signcompare: false,
            midlessform: false,
            midlessequal: false,
            midsigncompare: false,
            hiconstform: false,
            midconstform: false,
            loconstform: false,
            hival: 0,
            midval: 0,
            loval: 0,
            finalopc: OpCode::Blank,
        }
    }

    fn map_blocks_from_low(&mut self, lobl: BlockId, data: &Funcdata) -> bool {
        self.lolessbl = Some(lobl);
        if data.block(lobl).size_in() != 1 {
            return false;
        }
        if data.block(lobl).size_out() != 2 {
            return false;
        }
        let hieqbl = data.block(lobl).get_in(0);
        self.hieqbl = Some(hieqbl);
        if data.block(hieqbl).size_in() != 1 {
            return false;
        }
        if data.block(hieqbl).size_out() != 2 {
            return false;
        }
        let hilessbl = data.block(hieqbl).get_in(0);
        self.hilessbl = Some(hilessbl);
        if data.block(hilessbl).size_out() != 2 {
            return false;
        }
        true
    }

    fn map_ops_from_blocks(&mut self, data: &Funcdata) -> bool {
        self.lolessbool = data.block_last_op(present(self.lolessbl));
        let Some(lolessbool) = self.lolessbool else {
            return false;
        };
        if data.op(lolessbool).code() != OpCode::Cbranch {
            return false;
        }
        self.hieqbool = data.block_last_op(present(self.hieqbl));
        let Some(hieqbool) = self.hieqbool else {
            return false;
        };
        if data.op(hieqbool).code() != OpCode::Cbranch {
            return false;
        }
        self.hilessbool = data.block_last_op(present(self.hilessbl));
        let Some(hilessbool) = self.hilessbool else {
            return false;
        };
        if data.op(hilessbool).code() != OpCode::Cbranch {
            return false;
        }

        self.hiflip = false;
        self.equalflip = false;
        self.loflip = false;
        self.midlessform = false;
        self.lolessiszerocomp = false;

        let vn = op_input(data, hieqbool, 1);
        if !data.vn(vn).is_written() {
            return false;
        }
        let hiequal = def_op(data, vn);
        self.hiequal = Some(hiequal);
        match data.op(hiequal).code() {
            OpCode::IntEqual | OpCode::IntNotequal => {
                self.midlessform = false;
            }
            OpCode::IntLess => {
                self.midlessequal = false;
                self.midsigncompare = false;
                self.midlessform = true;
            }
            OpCode::IntLessequal => {
                self.midlessequal = true;
                self.midsigncompare = false;
                self.midlessform = true;
            }
            OpCode::IntSless => {
                self.midlessequal = false;
                self.midsigncompare = true;
                self.midlessform = true;
            }
            OpCode::IntSlessequal => {
                self.midlessequal = true;
                self.midsigncompare = true;
                self.midlessform = true;
            }
            _ => return false,
        }

        let vn = op_input(data, lolessbool, 1);
        if !data.vn(vn).is_written() {
            return false;
        }
        let loless = def_op(data, vn);
        self.loless = Some(loless);
        match data.op(loless).code() {
            OpCode::IntLess => {
                self.lolessequalform = false;
            }
            OpCode::IntLessequal => {
                self.lolessequalform = true;
            }
            OpCode::IntEqual => {
                if !data.vn(op_input(data, loless, 1)).is_constant() {
                    return false;
                }
                if input_offset(data, loless, 1) != 0 {
                    return false;
                }
                self.lolessiszerocomp = true;
                self.lolessequalform = true;
            }
            OpCode::IntNotequal => {
                if !data.vn(op_input(data, loless, 1)).is_constant() {
                    return false;
                }
                if input_offset(data, loless, 1) != 0 {
                    return false;
                }
                self.lolessiszerocomp = true;
                self.lolessequalform = false;
            }
            _ => return false,
        }

        let vn = op_input(data, hilessbool, 1);
        if !data.vn(vn).is_written() {
            return false;
        }
        let hiless = def_op(data, vn);
        self.hiless = Some(hiless);
        match data.op(hiless).code() {
            OpCode::IntLess => {
                self.hilessequalform = false;
                self.signcompare = false;
            }
            OpCode::IntLessequal => {
                self.hilessequalform = true;
                self.signcompare = false;
            }
            OpCode::IntSless => {
                self.hilessequalform = false;
                self.signcompare = true;
            }
            OpCode::IntSlessequal => {
                self.hilessequalform = true;
                self.signcompare = true;
            }
            _ => return false,
        }
        true
    }

    fn check_signedness(&mut self) -> bool {
        if self.midlessform && self.midsigncompare != self.signcompare {
            return false;
        }
        true
    }

    fn normalize_hi(&mut self, data: &Funcdata) -> bool {
        let hiless = present(self.hiless);
        self.vnhil1 = Some(op_input(data, hiless, 0));
        self.vnhil2 = Some(op_input(data, hiless, 1));
        if data.vn(present(self.vnhil1)).is_constant() {
            self.hiflip = !self.hiflip;
            self.hilessequalform = !self.hilessequalform;
            std::mem::swap(&mut self.vnhil1, &mut self.vnhil2);
        }
        self.hiconstform = false;
        if data.vn(present(self.vnhil2)).is_constant() {
            if self.input.get_size() as i64 as u64 > std::mem::size_of::<u64>() as u64 {
                return false;
            }
            self.hiconstform = true;
            self.hival = data.vn(present(self.vnhil2)).get_offset();
            let mut hilesstrue = None;
            let mut hilessfalse = None;
            SplitVarnode::get_true_false(
                present(self.hilessbool),
                self.hiflip,
                &mut hilesstrue,
                &mut hilessfalse,
                data,
            );
            self.hilesstrue = hilesstrue;
            self.hilessfalse = hilessfalse;
            let mut inc: i32 = 1;
            if self.hilessfalse != self.hieqbl {
                self.hiflip = !self.hiflip;
                self.hilessequalform = !self.hilessequalform;
                std::mem::swap(&mut self.vnhil1, &mut self.vnhil2);
                inc = -1;
            }
            if self.hilessequalform {
                self.hival = self.hival.wrapping_add(inc as i64 as u64);
                self.hival &= calc_mask(self.input.get_size());
                self.hilessequalform = false;
            }
            let lo_size = data.vn(present(self.input.get_lo())).get_size();
            self.hival = self.hival.wrapping_shr((lo_size * 8) as u32);
        } else if self.hilessequalform {
            self.hilessequalform = false;
            self.hiflip = !self.hiflip;
            std::mem::swap(&mut self.vnhil1, &mut self.vnhil2);
        }
        true
    }

    fn normalize_mid(&mut self, data: &Funcdata) -> bool {
        let hiequal = present(self.hiequal);
        self.vnhie1 = Some(op_input(data, hiequal, 0));
        self.vnhie2 = Some(op_input(data, hiequal, 1));
        if data.vn(present(self.vnhie1)).is_constant() {
            std::mem::swap(&mut self.vnhie1, &mut self.vnhie2);
            if self.midlessform {
                self.equalflip = !self.equalflip;
                self.midlessequal = !self.midlessequal;
            }
        }
        self.midconstform = false;
        let vnhie2 = present(self.vnhie2);
        if data.vn(vnhie2).is_constant() {
            if !self.hiconstform {
                return false;
            }
            self.midconstform = true;
            self.midval = data.vn(vnhie2).get_offset();
            let lo_size = data.vn(present(self.input.get_lo())).get_size();
            if data.vn(vnhie2).get_size() == self.input.get_size() {
                let lopart = self.midval & calc_mask(lo_size);
                self.midval = self.midval.wrapping_shr((lo_size * 8) as u32);
                if self.midlessform {
                    if self.midlessequal {
                        if lopart != calc_mask(lo_size) {
                            return false;
                        }
                    } else if lopart != 0 {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            if self.midval != self.hival {
                if !self.midlessform {
                    return false;
                }
                let adjust: i64 = if self.midlessequal { 1 } else { -1 };
                self.midval = self.midval.wrapping_add(adjust as u64);
                self.midval &= calc_mask(lo_size);
                self.midlessequal = !self.midlessequal;
                if self.midval != self.hival {
                    return false;
                }
            }
        }
        if self.midlessform {
            if !self.midlessequal {
                self.equalflip = !self.equalflip;
            }
        } else if data.op(hiequal).code() == OpCode::IntNotequal {
            self.equalflip = !self.equalflip;
        }
        true
    }

    fn normalize_lo(&mut self, data: &Funcdata) -> bool {
        let loless = present(self.loless);
        self.vnlo1 = Some(op_input(data, loless, 0));
        self.vnlo2 = Some(op_input(data, loless, 1));
        if self.lolessiszerocomp {
            self.loconstform = true;
            if self.lolessequalform {
                self.loval = 1;
                self.lolessequalform = false;
            } else {
                self.loflip = !self.loflip;
                self.loval = 1;
            }
            return true;
        }
        if data.vn(present(self.vnlo1)).is_constant() {
            self.loflip = !self.loflip;
            self.lolessequalform = !self.lolessequalform;
            std::mem::swap(&mut self.vnlo1, &mut self.vnlo2);
        }
        self.loconstform = false;
        let vnlo2 = present(self.vnlo2);
        if data.vn(vnlo2).is_constant() {
            self.loconstform = true;
            self.loval = data.vn(vnlo2).get_offset();
            if self.lolessequalform {
                self.loval = self.loval.wrapping_add(1);
                self.loval &= calc_mask(data.vn(vnlo2).get_size());
                self.lolessequalform = false;
            }
        } else if self.lolessequalform {
            self.lolessequalform = false;
            self.loflip = !self.loflip;
            std::mem::swap(&mut self.vnlo1, &mut self.vnlo2);
        }
        true
    }

    fn check_block_form(&mut self, data: &Funcdata) -> bool {
        let mut hilesstrue = None;
        let mut hilessfalse = None;
        let mut lolesstrue = None;
        let mut lolessfalse = None;
        let mut hieqtrue = None;
        let mut hieqfalse = None;
        SplitVarnode::get_true_false(
            present(self.hilessbool),
            self.hiflip,
            &mut hilesstrue,
            &mut hilessfalse,
            data,
        );
        SplitVarnode::get_true_false(
            present(self.lolessbool),
            self.loflip,
            &mut lolesstrue,
            &mut lolessfalse,
            data,
        );
        SplitVarnode::get_true_false(
            present(self.hieqbool),
            self.equalflip,
            &mut hieqtrue,
            &mut hieqfalse,
            data,
        );
        self.hilesstrue = hilesstrue;
        self.hilessfalse = hilessfalse;
        self.lolesstrue = lolesstrue;
        self.lolessfalse = lolessfalse;
        self.hieqtrue = hieqtrue;
        self.hieqfalse = hieqfalse;
        if self.hilesstrue == self.lolesstrue
            && self.hieqfalse == self.lolessfalse
            && self.hilessfalse == self.hieqbl
            && self.hieqtrue == self.lolessbl
            && SplitVarnode::otherwise_empty(present(self.hieqbool), data)
            && SplitVarnode::otherwise_empty(present(self.lolessbool), data)
        {
            return true;
        }
        false
    }

    fn check_op_form(&mut self, data: &Funcdata) -> bool {
        self.lo = self.input.get_lo();
        self.hi = self.input.get_hi();

        if self.midconstform {
            if !self.hiconstform {
                return false;
            }
            if data.vn(present(self.vnhie2)).get_size() == self.input.get_size() {
                if self.vnhie1 != self.vnhil1 && self.vnhie1 != self.vnhil2 {
                    return false;
                }
            } else if self.vnhie1 != self.input.get_hi() {
                return false;
            }
        } else {
            if self.vnhil1 != self.vnhie1 && self.vnhil1 != self.vnhie2 {
                return false;
            }
            if self.vnhil2 != self.vnhie1 && self.vnhil2 != self.vnhie2 {
                return false;
            }
        }
        if self.hi.is_some() && self.hi == self.vnhil1 {
            if self.hiconstform {
                return false;
            }
            self.hislot = 0;
            self.hi2 = self.vnhil2;
            if self.vnlo1 != self.lo {
                std::mem::swap(&mut self.vnlo1, &mut self.vnlo2);
                if self.vnlo1 != self.lo {
                    return false;
                }
                self.loflip = !self.loflip;
                self.lolessequalform = !self.lolessequalform;
            }
            self.lo2 = self.vnlo2;
        } else if self.hi.is_some() && self.hi == self.vnhil2 {
            if self.hiconstform {
                return false;
            }
            self.hislot = 1;
            self.hi2 = self.vnhil1;
            if self.vnlo2 != self.lo {
                std::mem::swap(&mut self.vnlo1, &mut self.vnlo2);
                if self.vnlo2 != self.lo {
                    return false;
                }
                self.loflip = !self.loflip;
                self.lolessequalform = !self.lolessequalform;
            }
            self.lo2 = self.vnlo1;
        } else if self.input.get_whole() == self.vnhil1 {
            if !self.hiconstform {
                return false;
            }
            if !self.loconstform {
                return false;
            }
            if self.vnlo1 != self.lo {
                return false;
            }
            self.hislot = 0;
        } else if self.input.get_whole() == self.vnhil2 {
            if !self.hiconstform {
                return false;
            }
            if !self.loconstform {
                return false;
            }
            if self.vnlo2 != self.lo {
                self.loflip = !self.loflip;
                self.loval = self.loval.wrapping_sub(1);
                self.loval &= calc_mask(data.vn(present(self.lo)).get_size());
                if self.vnlo1 != self.lo {
                    return false;
                }
            }
            self.hislot = 1;
        } else {
            return false;
        }
        true
    }

    fn set_op_code(&mut self) {
        if self.lolessequalform != self.hiflip {
            self.finalopc = if self.signcompare {
                OpCode::IntSlessequal
            } else {
                OpCode::IntLessequal
            };
        } else {
            self.finalopc = if self.signcompare {
                OpCode::IntSless
            } else {
                OpCode::IntLess
            };
        }
        if self.hiflip {
            self.hislot = 1 - self.hislot;
            self.hiflip = false;
        }
    }

    fn set_bool_op(&mut self, data: &Funcdata) -> Result<bool> {
        let hilessbool = present(self.hilessbool);
        if self.hislot == 0 {
            if SplitVarnode::prepare_bool_op(&mut self.input, &mut self.in2, hilessbool, data)? {
                return Ok(true);
            }
        } else if SplitVarnode::prepare_bool_op(&mut self.in2, &mut self.input, hilessbool, data)? {
            return Ok(true);
        }
        Ok(false)
    }

    fn map_from_low(&mut self, op: OpId, data: &Funcdata) -> bool {
        let Some(lo_op) = data.vn(op_out(data, op)).lone_descend() else {
            return false;
        };
        if !self.map_blocks_from_low(op_block(data, lo_op), data) {
            return false;
        }
        if !self.map_ops_from_blocks(data) {
            return false;
        }
        if !self.check_signedness() {
            return false;
        }
        if !self.normalize_hi(data) {
            return false;
        }
        if !self.normalize_mid(data) {
            return false;
        }
        if !self.normalize_lo(data) {
            return false;
        }
        if !self.check_op_form(data) {
            return false;
        }
        if !self.check_block_form(data) {
            return false;
        }
        true
    }

    fn test_replace(&mut self, data: &Funcdata) -> Result<bool> {
        self.set_op_code();
        let size = self.input.get_size();
        if self.hiconstform {
            let lo_size = data.vn(present(self.input.get_lo())).get_size();
            let value = self.hival.wrapping_shl((8 * lo_size) as u32) | self.loval;
            self.in2.init_partial_constant(size, value);
            if !self.set_bool_op(data)? {
                return Ok(false);
            }
        } else {
            self.in2.init_partial(size, present(self.lo2), self.hi2, data);
            if !self.set_bool_op(data)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        lo_op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if workishi {
            return Ok(false);
        }
        if split_in.get_lo().is_none() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.map_from_low(lo_op, data) {
            return Ok(false);
        }
        let res = self.test_replace(data)?;
        if res {
            if self.in2.exceeds_const_precision() {
                return Ok(false);
            }
            let hilessbool = present(self.hilessbool);
            if self.hislot == 0 {
                SplitVarnode::create_bool_op(data, glb, hilessbool, &mut self.input, &mut self.in2, self.finalopc)?;
            } else {
                SplitVarnode::create_bool_op(data, glb, hilessbool, &mut self.in2, &mut self.input, self.finalopc)?;
            }
            let constvn = data.new_constant(1, if self.equalflip { 1 } else { 0 }, glb);
            data.op_set_input(present(self.hieqbool), constvn, 1)?;
        }
        Ok(res)
    }
}

#[derive(Clone, Debug)]
pub struct LessConstForm {
    pub(crate) input: SplitVarnode,
    pub(crate) vn: Option<VarnodeId>,
    pub(crate) cvn: Option<VarnodeId>,
    pub(crate) inslot: i32,
    pub(crate) signcompare: bool,
    pub(crate) hilessequalform: bool,
    pub(crate) constin: SplitVarnode,
}

impl Default for LessConstForm {
    fn default() -> LessConstForm {
        LessConstForm::new()
    }
}

impl LessConstForm {
    pub fn new() -> LessConstForm {
        LessConstForm {
            input: SplitVarnode::new(),
            vn: None,
            cvn: None,
            inslot: 0,
            signcompare: false,
            hilessequalform: false,
            constin: SplitVarnode::new(),
        }
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if split_in.get_hi().is_none() {
            return Ok(false);
        }
        self.input = split_in.clone();
        let vn = present(self.input.get_hi());
        self.vn = Some(vn);
        self.inslot = data.op(op).get_slot(vn);
        let cvn = op_input(data, op, 1 - self.inslot);
        self.cvn = Some(cvn);
        let losize = self.input.get_size() - data.vn(vn).get_size();

        if !data.vn(cvn).is_constant() {
            return Ok(false);
        }

        let opc = data.op(op).code();
        self.signcompare = opc == OpCode::IntSlessequal || opc == OpCode::IntSless;
        self.hilessequalform = opc == OpCode::IntSlessequal || opc == OpCode::IntLessequal;

        let mut val = data.vn(cvn).get_offset().wrapping_shl((8 * losize) as u32);
        if self.hilessequalform != (self.inslot == 1) {
            val |= calc_mask(losize);
        }

        let Some(desc) = data.vn(op_out(data, op)).lone_descend() else {
            return Ok(false);
        };
        if data.op(desc).code() != OpCode::Cbranch {
            return Ok(false);
        }

        self.constin.init_partial_constant(self.input.get_size(), val);
        if self.constin.exceeds_const_precision() {
            return Ok(false);
        }

        if self.inslot == 0 {
            if SplitVarnode::prepare_bool_op(&mut self.input, &mut self.constin, op, data)? {
                SplitVarnode::replace_bool_op(data, glb, op, &mut self.input, &mut self.constin, opc)?;
                return Ok(true);
            }
        } else if SplitVarnode::prepare_bool_op(&mut self.constin, &mut self.input, op, data)? {
            SplitVarnode::replace_bool_op(data, glb, op, &mut self.constin, &mut self.input, opc)?;
            return Ok(true);
        }
        Ok(false)
    }
}

#[derive(Clone, Debug)]
pub struct ShiftForm {
    pub(crate) input: SplitVarnode,
    pub(crate) opc: OpCode,
    pub(crate) loshift: Option<OpId>,
    pub(crate) midshift: Option<OpId>,
    pub(crate) hishift: Option<OpId>,
    pub(crate) orop: Option<OpId>,
    pub(crate) lo: Option<VarnodeId>,
    pub(crate) hi: Option<VarnodeId>,
    pub(crate) midlo: Option<VarnodeId>,
    pub(crate) midhi: Option<VarnodeId>,
    pub(crate) salo: Option<VarnodeId>,
    pub(crate) sahi: Option<VarnodeId>,
    pub(crate) samid: Option<VarnodeId>,
    pub(crate) reslo: Option<VarnodeId>,
    pub(crate) reshi: Option<VarnodeId>,
    pub(crate) out: SplitVarnode,
    pub(crate) existop: Option<OpId>,
}

impl Default for ShiftForm {
    fn default() -> ShiftForm {
        ShiftForm::new()
    }
}

impl ShiftForm {
    pub fn new() -> ShiftForm {
        ShiftForm {
            input: SplitVarnode::new(),
            opc: OpCode::Blank,
            loshift: None,
            midshift: None,
            hishift: None,
            orop: None,
            lo: None,
            hi: None,
            midlo: None,
            midhi: None,
            salo: None,
            sahi: None,
            samid: None,
            reslo: None,
            reshi: None,
            out: SplitVarnode::new(),
            existop: None,
        }
    }

    fn verify_shift_amount(&mut self, data: &Funcdata) -> bool {
        let salo = present(self.salo);
        let samid = present(self.samid);
        let sahi = present(self.sahi);
        if !data.vn(salo).is_constant() {
            return false;
        }
        if !data.vn(samid).is_constant() {
            return false;
        }
        if !data.vn(sahi).is_constant() {
            return false;
        }
        let mut val = data.vn(salo).get_offset();
        if val != data.vn(sahi).get_offset() {
            return false;
        }
        let lo_bits = (8 * data.vn(present(self.lo)).get_size()) as i64 as u64;
        if val >= lo_bits {
            return false;
        }
        val = lo_bits.wrapping_sub(val);
        if data.vn(samid).get_offset() != val {
            return false;
        }
        true
    }

    fn map_left(&mut self, data: &Funcdata) -> bool {
        let reslo = present(self.reslo);
        let reshi = present(self.reshi);
        if !data.vn(reslo).is_written() {
            return false;
        }
        if !data.vn(reshi).is_written() {
            return false;
        }
        let loshift = def_op(data, reslo);
        self.loshift = Some(loshift);
        self.opc = data.op(loshift).code();
        if self.opc != OpCode::IntLeft {
            return false;
        }
        let orop = def_op(data, reshi);
        self.orop = Some(orop);
        let orcode = data.op(orop).code();
        if orcode != OpCode::IntOr && orcode != OpCode::IntXor && orcode != OpCode::IntAdd {
            return false;
        }
        self.midlo = Some(op_input(data, orop, 0));
        self.midhi = Some(op_input(data, orop, 1));
        if !data.vn(present(self.midlo)).is_written() {
            return false;
        }
        if !data.vn(present(self.midhi)).is_written() {
            return false;
        }
        if data.op(def_op(data, present(self.midhi))).code() != OpCode::IntLeft {
            std::mem::swap(&mut self.midhi, &mut self.midlo);
        }
        let midshift = def_op(data, present(self.midlo));
        self.midshift = Some(midshift);
        if data.op(midshift).code() != OpCode::IntRight {
            return false;
        }
        let hishift = def_op(data, present(self.midhi));
        self.hishift = Some(hishift);
        if data.op(hishift).code() != OpCode::IntLeft {
            return false;
        }

        if self.lo != Some(op_input(data, loshift, 0)) {
            return false;
        }
        if self.hi != Some(op_input(data, hishift, 0)) {
            return false;
        }
        if self.lo != Some(op_input(data, midshift, 0)) {
            return false;
        }
        self.salo = Some(op_input(data, loshift, 1));
        self.sahi = Some(op_input(data, hishift, 1));
        self.samid = Some(op_input(data, midshift, 1));
        true
    }

    fn map_right(&mut self, data: &Funcdata) -> bool {
        let reslo = present(self.reslo);
        let reshi = present(self.reshi);
        if !data.vn(reslo).is_written() {
            return false;
        }
        if !data.vn(reshi).is_written() {
            return false;
        }
        let hishift = def_op(data, reshi);
        self.hishift = Some(hishift);
        self.opc = data.op(hishift).code();
        if self.opc != OpCode::IntRight && self.opc != OpCode::IntSright {
            return false;
        }
        let orop = def_op(data, reslo);
        self.orop = Some(orop);
        let orcode = data.op(orop).code();
        if orcode != OpCode::IntOr && orcode != OpCode::IntXor && orcode != OpCode::IntAdd {
            return false;
        }
        self.midlo = Some(op_input(data, orop, 0));
        self.midhi = Some(op_input(data, orop, 1));
        if !data.vn(present(self.midlo)).is_written() {
            return false;
        }
        if !data.vn(present(self.midhi)).is_written() {
            return false;
        }
        if data.op(def_op(data, present(self.midlo))).code() != OpCode::IntRight {
            std::mem::swap(&mut self.midhi, &mut self.midlo);
        }
        let midshift = def_op(data, present(self.midhi));
        self.midshift = Some(midshift);
        if data.op(midshift).code() != OpCode::IntLeft {
            return false;
        }
        let loshift = def_op(data, present(self.midlo));
        self.loshift = Some(loshift);
        if data.op(loshift).code() != OpCode::IntRight {
            return false;
        }

        if self.lo != Some(op_input(data, loshift, 0)) {
            return false;
        }
        if self.hi != Some(op_input(data, hishift, 0)) {
            return false;
        }
        if self.hi != Some(op_input(data, midshift, 0)) {
            return false;
        }
        self.salo = Some(op_input(data, loshift, 1));
        self.sahi = Some(op_input(data, hishift, 1));
        self.samid = Some(op_input(data, midshift, 1));
        true
    }

    pub fn verify_left(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, lo_op: OpId, data: &Funcdata) -> bool {
        self.hi = Some(hi_vn);
        self.lo = Some(lo_vn);

        self.loshift = Some(lo_op);
        self.reslo = data.op(lo_op).get_out();

        for &hishift in data.vn(hi_vn).descend() {
            self.hishift = Some(hishift);
            if data.op(hishift).code() != OpCode::IntLeft {
                continue;
            }
            let outvn = op_out(data, hishift);
            for &midshift in data.vn(outvn).descend() {
                self.midshift = Some(midshift);
                let Some(tmpvn) = data.op(midshift).get_out() else {
                    continue;
                };
                self.reshi = Some(tmpvn);
                if !self.map_left(data) {
                    continue;
                }
                if !self.verify_shift_amount(data) {
                    continue;
                }
                return true;
            }
        }
        false
    }

    pub fn verify_right(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, hiop: OpId, data: &Funcdata) -> bool {
        self.hi = Some(hi_vn);
        self.lo = Some(lo_vn);
        self.hishift = Some(hiop);
        self.reshi = data.op(hiop).get_out();

        for &loshift in data.vn(lo_vn).descend() {
            self.loshift = Some(loshift);
            if data.op(loshift).code() != OpCode::IntRight {
                continue;
            }
            let outvn = op_out(data, loshift);
            for &midshift in data.vn(outvn).descend() {
                self.midshift = Some(midshift);
                let Some(tmpvn) = data.op(midshift).get_out() else {
                    continue;
                };
                self.reslo = Some(tmpvn);
                if !self.map_right(data) {
                    continue;
                }
                if !self.verify_shift_amount(data) {
                    continue;
                }
                return true;
            }
        }
        false
    }

    pub fn apply_rule_left(
        &mut self,
        split_in: &mut SplitVarnode,
        lo_op: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify_left(present(self.input.get_hi()), present(self.input.get_lo()), lo_op, data) {
            return Ok(false);
        }
        self.apply_shift(data, glb)
    }

    pub fn apply_rule_right(
        &mut self,
        split_in: &mut SplitVarnode,
        hiop: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify_right(present(self.input.get_hi()), present(self.input.get_lo()), hiop, data) {
            return Ok(false);
        }
        self.apply_shift(data, glb)
    }

    fn apply_shift(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let size = self.input.get_size();
        self.out.init_partial(size, present(self.reslo), self.reshi, data);
        self.existop = SplitVarnode::prepare_shift_op(&mut self.out, &mut self.input, data)?;
        let Some(existop) = self.existop else {
            return Ok(false);
        };
        SplitVarnode::create_shift_op(
            data,
            glb,
            &mut self.out,
            &mut self.input,
            present(self.salo),
            existop,
            self.opc,
        )?;
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct MultForm {
    pub(crate) input: SplitVarnode,
    pub(crate) add1: Option<OpId>,
    pub(crate) add2: Option<OpId>,
    pub(crate) subhi: Option<OpId>,
    pub(crate) multlo: Option<OpId>,
    pub(crate) multhi1: Option<OpId>,
    pub(crate) multhi2: Option<OpId>,
    pub(crate) midtmp: Option<VarnodeId>,
    pub(crate) lo1zext: Option<VarnodeId>,
    pub(crate) lo2zext: Option<VarnodeId>,
    pub(crate) hi1: Option<VarnodeId>,
    pub(crate) lo1: Option<VarnodeId>,
    pub(crate) hi2: Option<VarnodeId>,
    pub(crate) lo2: Option<VarnodeId>,
    pub(crate) reslo: Option<VarnodeId>,
    pub(crate) reshi: Option<VarnodeId>,
    pub(crate) outdoub: SplitVarnode,
    pub(crate) in2: SplitVarnode,
    pub(crate) existop: Option<OpId>,
}

impl Default for MultForm {
    fn default() -> MultForm {
        MultForm::new()
    }
}

impl MultForm {
    pub fn new() -> MultForm {
        MultForm {
            input: SplitVarnode::new(),
            add1: None,
            add2: None,
            subhi: None,
            multlo: None,
            multhi1: None,
            multhi2: None,
            midtmp: None,
            lo1zext: None,
            lo2zext: None,
            hi1: None,
            lo1: None,
            hi2: None,
            lo2: None,
            reslo: None,
            reshi: None,
            outdoub: SplitVarnode::new(),
            in2: SplitVarnode::new(),
            existop: None,
        }
    }

    fn zext_of(&mut self, big: VarnodeId, small: VarnodeId, data: &Funcdata) -> bool {
        if data.vn(small).is_constant() {
            if !data.vn(big).is_constant() {
                return false;
            }
            if data.vn(big).get_offset() == data.vn(small).get_offset() {
                return true;
            }
            return false;
        }
        if !data.vn(big).is_written() {
            return false;
        }
        let op = def_op(data, big);
        if data.op(op).code() == OpCode::IntZext {
            return op_input(data, op, 0) == small;
        }
        if data.op(op).code() == OpCode::IntAnd {
            if !data.vn(op_input(data, op, 1)).is_constant() {
                return false;
            }
            if input_offset(data, op, 1) != calc_mask(data.vn(small).get_size()) {
                return false;
            }
            let whole = op_input(data, op, 0);
            if !data.vn(small).is_written() {
                return false;
            }
            let sub = def_op(data, small);
            if data.op(sub).code() != OpCode::Subpiece {
                return false;
            }
            return op_input(data, sub, 0) == whole;
        }
        false
    }

    fn map_res_hi(&mut self, rhi: VarnodeId, data: &Funcdata) -> bool {
        self.reshi = Some(rhi);
        if !data.vn(rhi).is_written() {
            return false;
        }
        let add1 = def_op(data, rhi);
        self.add1 = Some(add1);
        if data.op(add1).code() != OpCode::IntAdd {
            return false;
        }
        let mut ad1 = op_input(data, add1, 0);
        let mut ad2 = op_input(data, add1, 1);
        let ad3;
        if !data.vn(ad1).is_written() {
            return false;
        }
        if !data.vn(ad2).is_written() {
            return false;
        }
        let mut add2 = def_op(data, ad1);
        self.add2 = Some(add2);
        if data.op(add2).code() == OpCode::IntAdd {
            ad1 = op_input(data, add2, 0);
            ad3 = op_input(data, add2, 1);
        } else {
            add2 = def_op(data, ad2);
            self.add2 = Some(add2);
            if data.op(add2).code() != OpCode::IntAdd {
                return false;
            }
            ad2 = op_input(data, add2, 0);
            ad3 = op_input(data, add2, 1);
        }
        if !data.vn(ad1).is_written() {
            return false;
        }
        if !data.vn(ad2).is_written() {
            return false;
        }
        if !data.vn(ad3).is_written() {
            return false;
        }
        let mut subhi = def_op(data, ad1);
        if data.op(subhi).code() == OpCode::Subpiece {
            self.multhi1 = Some(def_op(data, ad2));
            self.multhi2 = Some(def_op(data, ad3));
        } else {
            subhi = def_op(data, ad2);
            if data.op(subhi).code() == OpCode::Subpiece {
                self.multhi1 = Some(def_op(data, ad1));
                self.multhi2 = Some(def_op(data, ad3));
            } else {
                subhi = def_op(data, ad3);
                if data.op(subhi).code() == OpCode::Subpiece {
                    self.multhi1 = Some(def_op(data, ad1));
                    self.multhi2 = Some(def_op(data, ad2));
                } else {
                    self.subhi = Some(subhi);
                    return false;
                }
            }
        }
        self.subhi = Some(subhi);
        if data.op(present(self.multhi1)).code() != OpCode::IntMult {
            return false;
        }
        if data.op(present(self.multhi2)).code() != OpCode::IntMult {
            return false;
        }

        let midtmp = op_input(data, subhi, 0);
        self.midtmp = Some(midtmp);
        if !data.vn(midtmp).is_written() {
            return false;
        }
        let multlo = def_op(data, midtmp);
        self.multlo = Some(multlo);
        if data.op(multlo).code() != OpCode::IntMult {
            return false;
        }
        self.lo1zext = Some(op_input(data, multlo, 0));
        self.lo2zext = Some(op_input(data, multlo, 1));
        true
    }

    fn map_res_hi_small_const(&mut self, rhi: VarnodeId, data: &Funcdata) -> bool {
        self.reshi = Some(rhi);
        if !data.vn(rhi).is_written() {
            return false;
        }
        let add1 = def_op(data, rhi);
        self.add1 = Some(add1);
        if data.op(add1).code() != OpCode::IntAdd {
            return false;
        }
        let ad1 = op_input(data, add1, 0);
        let ad2 = op_input(data, add1, 1);
        if !data.vn(ad1).is_written() {
            return false;
        }
        if !data.vn(ad2).is_written() {
            return false;
        }
        let mut multhi1 = def_op(data, ad1);
        let subhi;
        if data.op(multhi1).code() != OpCode::IntMult {
            subhi = multhi1;
            multhi1 = def_op(data, ad2);
        } else {
            subhi = def_op(data, ad2);
        }
        self.multhi1 = Some(multhi1);
        self.subhi = Some(subhi);
        if data.op(multhi1).code() != OpCode::IntMult {
            return false;
        }
        if data.op(subhi).code() != OpCode::Subpiece {
            return false;
        }
        let midtmp = op_input(data, subhi, 0);
        self.midtmp = Some(midtmp);
        if !data.vn(midtmp).is_written() {
            return false;
        }
        let multlo = def_op(data, midtmp);
        self.multlo = Some(multlo);
        if data.op(multlo).code() != OpCode::IntMult {
            return false;
        }
        self.lo1zext = Some(op_input(data, multlo, 0));
        self.lo2zext = Some(op_input(data, multlo, 1));
        true
    }

    fn find_lo_from_in(&mut self, data: &Funcdata) -> bool {
        let lo1 = present(self.lo1);
        let hi1 = present(self.hi1);
        let mut vn1 = op_input(data, present(self.multhi1), 0);
        let mut vn2 = op_input(data, present(self.multhi1), 1);
        if vn1 != lo1 && vn2 != lo1 {
            std::mem::swap(&mut self.multhi1, &mut self.multhi2);
            vn1 = op_input(data, present(self.multhi1), 0);
            vn2 = op_input(data, present(self.multhi1), 1);
        }
        if vn1 == lo1 {
            self.hi2 = Some(vn2);
        } else if vn2 == lo1 {
            self.hi2 = Some(vn1);
        } else {
            return false;
        }
        vn1 = op_input(data, present(self.multhi2), 0);
        vn2 = op_input(data, present(self.multhi2), 1);
        if vn1 == hi1 {
            self.lo2 = Some(vn2);
        } else if vn2 == hi1 {
            self.lo2 = Some(vn1);
        } else {
            return false;
        }
        true
    }

    fn find_lo_from_in_small_const(&mut self, data: &Funcdata) -> bool {
        let hi1 = present(self.hi1);
        let multhi1 = present(self.multhi1);
        let vn1 = op_input(data, multhi1, 0);
        let vn2 = op_input(data, multhi1, 1);
        if vn1 == hi1 {
            self.lo2 = Some(vn2);
        } else if vn2 == hi1 {
            self.lo2 = Some(vn1);
        } else {
            return false;
        }
        if !data.vn(present(self.lo2)).is_constant() {
            return false;
        }
        self.hi2 = None;
        true
    }

    fn verify_lo(&mut self, data: &Funcdata) -> bool {
        let lo1 = present(self.lo1);
        let lo2 = present(self.lo2);
        let lo1zext = present(self.lo1zext);
        let lo2zext = present(self.lo2zext);
        if input_offset(data, present(self.subhi), 1) != data.vn(lo1).get_size() as i64 as u64 {
            return false;
        }
        if self.zext_of(lo1zext, lo1, data) {
            if self.zext_of(lo2zext, lo2, data) {
                return true;
            }
        } else if self.zext_of(lo1zext, lo2, data) && self.zext_of(lo2zext, lo1, data) {
            return true;
        }
        false
    }

    fn find_res_lo(&mut self, data: &Funcdata) -> bool {
        let lo1 = present(self.lo1);
        let lo2 = present(self.lo2);
        for &op in data.vn(present(self.midtmp)).descend() {
            if data.op(op).code() != OpCode::Subpiece {
                continue;
            }
            if input_offset(data, op, 1) != 0 {
                continue;
            }
            let reslo = op_out(data, op);
            self.reslo = Some(reslo);
            if data.vn(reslo).get_size() != data.vn(lo1).get_size() {
                continue;
            }
            return true;
        }
        for &op in data.vn(lo1).descend() {
            if data.op(op).code() != OpCode::IntMult {
                continue;
            }
            let vn1 = op_input(data, op, 0);
            let vn2 = op_input(data, op, 1);
            if data.vn(lo2).is_constant() {
                let lo2_offset = data.vn(lo2).get_offset();
                if (!data.vn(vn1).is_constant() || data.vn(vn1).get_offset() != lo2_offset)
                    && (!data.vn(vn2).is_constant() || data.vn(vn2).get_offset() != lo2_offset)
                {
                    continue;
                }
            } else if vn1 != lo2 && vn2 != lo2 {
                continue;
            }
            self.reslo = data.op(op).get_out();
            return true;
        }
        false
    }

    fn map_from_in(&mut self, rhi: VarnodeId, data: &Funcdata) -> bool {
        if !self.map_res_hi(rhi, data) {
            return false;
        }
        if !self.find_lo_from_in(data) {
            return false;
        }
        if !self.verify_lo(data) {
            return false;
        }
        if !self.find_res_lo(data) {
            return false;
        }
        true
    }

    fn map_from_in_small_const(&mut self, rhi: VarnodeId, data: &Funcdata) -> bool {
        if !self.map_res_hi_small_const(rhi, data) {
            return false;
        }
        if !self.find_lo_from_in_small_const(data) {
            return false;
        }
        if !self.verify_lo(data) {
            return false;
        }
        if !self.find_res_lo(data) {
            return false;
        }
        true
    }

    fn replace(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let size = self.input.get_size();
        self.outdoub.init_partial(size, present(self.reslo), self.reshi, data);
        self.in2.init_partial(size, present(self.lo2), self.hi2, data);
        if self.in2.exceeds_const_precision() {
            return Ok(false);
        }
        self.existop = SplitVarnode::prepare_binary_op(&mut self.outdoub, &mut self.input, &mut self.in2, data)?;
        let Some(existop) = self.existop else {
            return Ok(false);
        };
        SplitVarnode::create_binary_op(
            data,
            glb,
            &mut self.outdoub,
            &mut self.input,
            &mut self.in2,
            existop,
            OpCode::IntMult,
        )?;
        Ok(true)
    }

    pub fn verify(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, hop: OpId, data: &Funcdata) -> bool {
        self.hi1 = Some(hi_vn);
        self.lo1 = Some(lo_vn);
        for &add1 in data.vn(op_out(data, hop)).descend() {
            self.add1 = Some(add1);
            if data.op(add1).code() != OpCode::IntAdd {
                continue;
            }
            for &add2 in data.vn(op_out(data, add1)).descend() {
                self.add2 = Some(add2);
                if data.op(add2).code() != OpCode::IntAdd {
                    continue;
                }
                if self.map_from_in(op_out(data, add2), data) {
                    return true;
                }
            }
            if self.map_from_in(op_out(data, present(self.add1)), data) {
                return true;
            }
            if self.map_from_in_small_const(op_out(data, present(self.add1)), data) {
                return true;
            }
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        hop: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(present(self.input.get_hi()), present(self.input.get_lo()), hop, data) {
            return Ok(false);
        }
        if self.replace(data, glb)? {
            return Ok(true);
        }
        Ok(false)
    }
}

#[derive(Clone, Debug)]
pub struct PhiForm {
    pub(crate) input: SplitVarnode,
    pub(crate) outvn: SplitVarnode,
    pub(crate) inslot: i32,
    pub(crate) hibase: Option<VarnodeId>,
    pub(crate) lobase: Option<VarnodeId>,
    pub(crate) blbase: Option<BlockId>,
    pub(crate) lophi: Option<OpId>,
    pub(crate) hiphi: Option<OpId>,
    pub(crate) existop: Option<OpId>,
}

impl Default for PhiForm {
    fn default() -> PhiForm {
        PhiForm::new()
    }
}

impl PhiForm {
    pub fn new() -> PhiForm {
        PhiForm {
            input: SplitVarnode::new(),
            outvn: SplitVarnode::new(),
            inslot: 0,
            hibase: None,
            lobase: None,
            blbase: None,
            lophi: None,
            hiphi: None,
            existop: None,
        }
    }

    pub fn verify(&mut self, hi_vn: VarnodeId, lo_vn: VarnodeId, hphi: OpId, data: &Funcdata) -> bool {
        self.hibase = Some(hi_vn);
        self.lobase = Some(lo_vn);
        self.hiphi = Some(hphi);

        self.inslot = data.op(hphi).get_slot(hi_vn);

        if data.vn(op_out(data, hphi)).has_no_descend() {
            return false;
        }
        let blbase = op_block(data, hphi);
        self.blbase = Some(blbase);

        for &lophi in data.vn(lo_vn).descend() {
            self.lophi = Some(lophi);
            if data.op(lophi).code() != OpCode::Multiequal {
                continue;
            }
            if data.op(lophi).get_parent() != Some(blbase) {
                continue;
            }
            if op_input(data, lophi, self.inslot) != lo_vn {
                continue;
            }
            return true;
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        hphi: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(present(self.input.get_hi()), present(self.input.get_lo()), hphi, data) {
            return Ok(false);
        }
        let hiphi = present(self.hiphi);
        let lophi = present(self.lophi);
        let numin = data.op(hiphi).num_input();
        let mut inlist: Vec<SplitVarnode> = Vec::new();
        for slot in 0..numin {
            let vhi = op_input(data, hiphi, slot);
            let vlo = op_input(data, lophi, slot);
            inlist.push(SplitVarnode::new_pieces(vlo, vhi, data));
        }
        let size = self.input.get_size();
        self.outvn
            .init_partial(size, op_out(data, lophi), data.op(hiphi).get_out(), data);
        self.existop = SplitVarnode::prepare_phi_op(&mut self.outvn, &mut inlist, data)?;
        if let Some(existop) = self.existop {
            SplitVarnode::create_phi_op(data, glb, &mut self.outvn, &mut inlist, existop)?;
            return Ok(true);
        }
        Ok(false)
    }
}

#[derive(Clone, Debug)]
pub struct IndirectForm {
    pub(crate) input: SplitVarnode,
    pub(crate) outvn: SplitVarnode,
    pub(crate) lo: Option<VarnodeId>,
    pub(crate) hi: Option<VarnodeId>,
    pub(crate) reslo: Option<VarnodeId>,
    pub(crate) reshi: Option<VarnodeId>,
    pub(crate) affector: Option<OpId>,
    pub(crate) indhi: Option<OpId>,
    pub(crate) indlo: Option<OpId>,
}

impl Default for IndirectForm {
    fn default() -> IndirectForm {
        IndirectForm::new()
    }
}

impl IndirectForm {
    pub fn new() -> IndirectForm {
        IndirectForm {
            input: SplitVarnode::new(),
            outvn: SplitVarnode::new(),
            lo: None,
            hi: None,
            reslo: None,
            reshi: None,
            affector: None,
            indhi: None,
            indlo: None,
        }
    }

    pub fn verify(
        &mut self,
        hi_vn: VarnodeId,
        lo_vn: VarnodeId,
        ihi: OpId,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        self.hi = Some(hi_vn);
        self.lo = Some(lo_vn);
        self.indhi = Some(ihi);
        if space_type_of(data, op_input(data, ihi, 1)) != Some(SpaceType::Iop) {
            return false;
        }
        let affector = PcodeOp::get_op_from_const(data.vn(op_input(data, ihi, 1)).get_addr());
        self.affector = Some(affector);
        if data.op(affector).is_dead() {
            return false;
        }
        let reshi = op_out(data, ihi);
        self.reshi = Some(reshi);
        if space_type_of(data, reshi) == Some(SpaceType::Internal) {
            return false;
        }

        for &indlo in data.vn(lo_vn).descend() {
            self.indlo = Some(indlo);
            if data.op(indlo).code() != OpCode::Indirect {
                continue;
            }
            let iopvn = op_input(data, indlo, 1);
            if space_type_of(data, iopvn) != Some(SpaceType::Iop) {
                continue;
            }
            if affector != PcodeOp::get_op_from_const(data.vn(iopvn).get_addr()) {
                continue;
            }
            let reslo = op_out(data, indlo);
            self.reslo = Some(reslo);
            if space_type_of(data, reslo) == Some(SpaceType::Internal) {
                return false;
            }
            if data.vn(reslo).is_addr_tied() || data.vn(reshi).is_addr_tied() {
                let mut addr = Address::invalid();
                if !SplitVarnode::is_addr_tied_contiguous(reslo, reshi, &mut addr, data, glb) {
                    return false;
                }
            }
            return true;
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        ind: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(
            present(self.input.get_hi()),
            present(self.input.get_lo()),
            ind,
            data,
            glb,
        ) {
            return Ok(false);
        }
        let size = self.input.get_size();
        self.outvn.init_partial(size, present(self.reslo), self.reshi, data);
        let affector = present(self.affector);
        if !SplitVarnode::prepare_indirect_op(&mut self.input, affector, data)? {
            return Ok(false);
        }
        SplitVarnode::replace_indirect_op(data, glb, &mut self.outvn, &mut self.input, affector)?;
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct CopyForceForm {
    pub(crate) input: SplitVarnode,
    pub(crate) reslo: Option<VarnodeId>,
    pub(crate) reshi: Option<VarnodeId>,
    pub(crate) copylo: Option<OpId>,
    pub(crate) copyhi: Option<OpId>,
    pub(crate) addr_out: Address,
}

impl Default for CopyForceForm {
    fn default() -> CopyForceForm {
        CopyForceForm::new()
    }
}

impl CopyForceForm {
    pub fn new() -> CopyForceForm {
        CopyForceForm {
            input: SplitVarnode::new(),
            reslo: None,
            reshi: None,
            copylo: None,
            copyhi: None,
            addr_out: Address::invalid(),
        }
    }

    pub fn verify(
        &mut self,
        hi_vn: VarnodeId,
        lo_vn: VarnodeId,
        whole_vn: Option<VarnodeId>,
        cpy: OpId,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let Some(whole_vn) = whole_vn else {
            return false;
        };
        self.copyhi = Some(cpy);
        if op_input(data, cpy, 0) != hi_vn {
            return false;
        }
        let reshi = op_out(data, cpy);
        self.reshi = Some(reshi);
        if !data.vn(reshi).is_addr_force() || !data.vn(reshi).has_no_descend() {
            return false;
        }
        for &copylo in data.vn(lo_vn).descend() {
            self.copylo = Some(copylo);
            if data.op(copylo).code() != OpCode::Copy || data.op(copylo).get_parent() != data.op(cpy).get_parent() {
                continue;
            }
            let reslo = op_out(data, copylo);
            self.reslo = Some(reslo);
            if !data.vn(reslo).is_addr_force() || !data.vn(reslo).has_no_descend() {
                continue;
            }
            if !SplitVarnode::is_addr_tied_contiguous(reslo, reshi, &mut self.addr_out, data, glb) {
                continue;
            }
            if data.op(cpy).is_return_copy() {
                if data.vn(hi_vn).lone_descend().is_none() {
                    continue;
                }
                if data.vn(lo_vn).lone_descend().is_none() {
                    continue;
                }
                if *data.vn(whole_vn).get_addr() != self.addr_out {
                    if !data.vn(hi_vn).is_written() || !data.vn(lo_vn).is_written() {
                        continue;
                    }
                    let other_lo = def_op(data, lo_vn);
                    let other_hi = def_op(data, hi_vn);
                    if data.op(other_lo).code() != OpCode::Copy || data.op(other_hi).code() != OpCode::Copy {
                        continue;
                    }
                    if data.op(other_lo).get_parent() != data.op(other_hi).get_parent() {
                        continue;
                    }
                }
            }
            return true;
        }
        false
    }

    pub fn apply_rule(
        &mut self,
        split_in: &mut SplitVarnode,
        cpy: OpId,
        workishi: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !workishi {
            return Ok(false);
        }
        if !split_in.has_both_pieces() {
            return Ok(false);
        }
        self.input = split_in.clone();
        if !self.verify(
            present(self.input.get_hi()),
            present(self.input.get_lo()),
            self.input.get_whole(),
            cpy,
            data,
            glb,
        ) {
            return Ok(false);
        }
        let addr_out = self.addr_out.clone();
        SplitVarnode::replace_copy_force(
            data,
            glb,
            &addr_out,
            &mut self.input,
            present(self.copylo),
            present(self.copyhi),
        )?;
        Ok(true)
    }
}

pub struct RuleDoubleIn {
    base: RuleBase,
}

impl RuleDoubleIn {
    pub fn new(group: &str) -> RuleDoubleIn {
        RuleDoubleIn {
            base: RuleBase::new(group, 0, "doublein"),
        }
    }

    fn attempt_marking(&mut self, vn: VarnodeId, subpiece_op: OpId, data: &mut Funcdata, glb: &Architecture) -> i32 {
        let whole = op_input(data, subpiece_op, 0);
        if data.vn(whole).is_type_lock() {
            let types = glb.types.as_deref().expect("architecture has no type factory");
            if !types.get(data.vn(whole).get_type()).is_primitive_whole(types) {
                return 0;
            }
        }
        let offset = input_offset(data, subpiece_op, 1) as i32;
        if offset != data.vn(vn).get_size() {
            return 0;
        }
        if offset.wrapping_mul(2) != data.vn(whole).get_size() {
            return 0;
        }
        if data.vn(whole).is_input() {
            if !data.vn(whole).is_type_lock() {
                return 0;
            }
        } else if !data.vn(whole).is_written() {
            return 0;
        } else {
            let typeop = data.op(def_op(data, whole)).get_opcode(glb);
            if !typeop.is_arithmetic_op() && !typeop.is_floating_point_op() {
                return 0;
            }
        }
        let mut vn_lo: Option<VarnodeId> = None;
        for &op in data.vn(whole).descend() {
            if data.op(op).code() != OpCode::Subpiece {
                continue;
            }
            if input_offset(data, op, 1) != 0 {
                continue;
            }
            let outvn = op_out(data, op);
            if data.vn(outvn).get_size() == data.vn(vn).get_size() {
                vn_lo = Some(outvn);
                break;
            }
        }
        let Some(vn_lo) = vn_lo else {
            return 0;
        };
        set_precis_lo(data, vn_lo);
        set_precis_hi(data, vn);
        1
    }
}

impl Rule for RuleDoubleIn {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleDoubleIn::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = op_out(data, op);
        if !data.vn(outvn).is_precis_lo() {
            if data.vn(outvn).is_precis_hi() {
                return Ok(0);
            }
            return Ok(self.attempt_marking(outvn, op, data, glb));
        }
        if data.has_unreachable_blocks() {
            return Ok(0);
        }

        let mut splitvec: Vec<SplitVarnode> = Vec::new();
        SplitVarnode::whole_list(op_input(data, op, 0), &mut splitvec, data);
        if splitvec.is_empty() {
            return Ok(0);
        }
        for input in splitvec.iter_mut() {
            let res = SplitVarnode::apply_rule_in(input, data, glb)?;
            if res != 0 {
                return Ok(res);
            }
        }
        Ok(0)
    }

    fn reset(&mut self, data: &mut Funcdata, _glb: &mut Architecture) {
        data.set_double_precis_recovery(true);
    }
}

pub struct RuleDoubleOut {
    base: RuleBase,
}

impl RuleDoubleOut {
    pub fn new(group: &str) -> RuleDoubleOut {
        RuleDoubleOut {
            base: RuleBase::new(group, 0, "doubleout"),
        }
    }

    fn attempt_marking(
        &mut self,
        vnhi: VarnodeId,
        vnlo: VarnodeId,
        piece_op: OpId,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> i32 {
        let whole = op_out(data, piece_op);
        if data.vn(whole).is_type_lock() {
            let types = glb.types.as_deref().expect("architecture has no type factory");
            if !types.get(data.vn(whole).get_type()).is_primitive_whole(types) {
                return 0;
            }
        }
        if data.vn(vnhi).get_size() != data.vn(vnlo).get_size() {
            return 0;
        }

        let entryhi = data.vn(vnhi).get_symbol_entry();
        let entrylo = data.vn(vnlo).get_symbol_entry();
        if entryhi.is_some() || entrylo.is_some() {
            let (Some(entryhi), Some(entrylo)) = (entryhi, entrylo) else {
                return 0;
            };
            let symboltab = glb.symboltab.as_deref().expect("architecture has no symbol table");
            if symboltab.entry(entryhi).get_symbol() != symboltab.entry(entrylo).get_symbol() {
                return 0;
            }
        }

        let mut is_whole = false;
        for &readop in data.vn(whole).descend() {
            let typeop = data.op(readop).get_opcode(glb);
            if typeop.is_arithmetic_op() || typeop.is_floating_point_op() {
                is_whole = true;
                break;
            }
        }
        if !is_whole {
            return 0;
        }
        set_precis_hi(data, vnhi);
        set_precis_lo(data, vnlo);
        1
    }
}

impl Rule for RuleDoubleOut {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleDoubleOut::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vnhi = op_input(data, op, 0);
        let vnlo = op_input(data, op, 1);

        if !data.vn(vnhi).is_input() || !data.vn(vnlo).is_input() {
            return Ok(0);
        }
        if !data.vn(vnhi).is_persist() || !data.vn(vnlo).is_persist() {
            return Ok(0);
        }

        if !data.vn(vnhi).is_precis_hi() || !data.vn(vnlo).is_precis_lo() {
            return Ok(self.attempt_marking(vnhi, vnlo, op, data, glb));
        }
        if data.has_unreachable_blocks() {
            return Ok(0);
        }

        let mut addr = Address::invalid();
        if !SplitVarnode::is_addr_tied_contiguous(vnlo, vnhi, &mut addr, data, glb) {
            return Ok(0);
        }
        data.combine_input_varnodes(vnhi, vnlo, glb)?;
        Ok(1)
    }
}

pub struct RuleDoubleLoad {
    base: RuleBase,
}

impl RuleDoubleLoad {
    pub fn new(group: &str) -> RuleDoubleLoad {
        RuleDoubleLoad {
            base: RuleBase::new(group, 0, "doubleload"),
        }
    }

    pub fn no_write_conflict(
        op1: OpId,
        op2: OpId,
        spc: &SpaceRef,
        mut indirects: Option<&mut Vec<OpId>>,
        data: &Funcdata,
        glb: &Architecture,
    ) -> Option<OpId> {
        let bb = data.op(op1).get_parent();
        if bb != data.op(op2).get_parent() {
            return None;
        }
        let (first, last) = if op_order(data, op2) < op_order(data, op1) {
            (op2, op1)
        } else {
            (op1, op2)
        };
        let mut startop = first;
        if data.op(first).code() == OpCode::Store {
            let mut tmp_op = data.op_previous_op(startop);
            while let Some(candidate) = tmp_op {
                if data.op(candidate).code() != OpCode::Indirect {
                    break;
                }
                startop = candidate;
                tmp_op = data.op_previous_op(candidate);
            }
        }
        let mut iter = Some(startop);
        while iter != Some(last) {
            let Some(curop) = iter else {
                break;
            };
            iter = next_basic_op(data, curop);
            if curop == first {
                continue;
            }
            match data.op(curop).code() {
                OpCode::Store => {
                    let store_space = data.vn(op_input(data, curop, 0)).get_space_from_const(&glb.manager);
                    if space_matches(store_space.as_ref(), spc) {
                        return None;
                    }
                }
                OpCode::Indirect => {
                    let affector = PcodeOp::get_op_from_const(data.vn(op_input(data, curop, 1)).get_addr());
                    if affector == first || affector == last {
                        if let Some(list) = indirects.as_deref_mut() {
                            list.push(curop);
                        }
                    } else if space_matches(data.vn(op_out(data, curop)).get_space(), spc) {
                        return None;
                    }
                }
                OpCode::Call
                | OpCode::Callind
                | OpCode::Callother
                | OpCode::Return
                | OpCode::Branch
                | OpCode::Cbranch
                | OpCode::Branchind => {
                    return None;
                }
                _ => {
                    if let Some(outvn) = data.op(curop).get_out()
                        && space_matches(data.vn(outvn).get_space(), spc)
                    {
                        return None;
                    }
                }
            }
        }
        Some(last)
    }
}

impl Rule for RuleDoubleLoad {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleDoubleLoad::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let piece0 = op_input(data, op, 0);
        let piece1 = op_input(data, op, 1);
        if !data.vn(piece0).is_written() {
            return Ok(0);
        }
        if !data.vn(piece1).is_written() {
            return Ok(0);
        }
        let load1 = def_op(data, piece1);
        if data.op(load1).code() != OpCode::Load {
            return Ok(0);
        }
        let mut load0 = def_op(data, piece0);
        let mut opc = data.op(load0).code();
        let mut offset: i32 = 0;
        if opc == OpCode::Subpiece {
            if input_offset(data, load0, 1) != 0 {
                return Ok(0);
            }
            let vn0 = op_input(data, load0, 0);
            if !data.vn(vn0).is_written() {
                return Ok(0);
            }
            offset = data.vn(vn0).get_size() - data.vn(piece0).get_size();
            load0 = def_op(data, vn0);
            opc = data.op(load0).code();
        }
        if opc != OpCode::Load {
            return Ok(0);
        }
        let mut loadlo: Option<OpId> = None;
        let mut loadhi: Option<OpId> = None;
        let mut spc: Option<SpaceRef> = None;
        if !SplitVarnode::test_contiguous_pointers(load0, load1, &mut loadlo, &mut loadhi, &mut spc, data, glb) {
            return Ok(0);
        }
        let loadlo = present(loadlo);
        let loadhi = present(loadhi);
        let spc = present(spc);

        let size = data.vn(piece0).get_size() + data.vn(piece1).get_size();
        let Some(mut latest) = RuleDoubleLoad::no_write_conflict(loadlo, loadhi, &spc, None, data, glb) else {
            return Ok(0);
        };

        let latest_addr = data.op(latest).get_addr().clone();
        let newload = data.new_op(2, &latest_addr);
        let vnout = data.new_unique_out(size, newload, glb)?;
        let spcvn = data.new_varnode_space(&spc, glb);
        data.op_set_opcode(newload, OpCode::Load, glb);
        data.op_set_input(newload, spcvn, 0)?;
        let mut addrvn = op_input(data, loadlo, 1);
        if spc.is_big_endian() && offset != 0 {
            let newadd = data.new_op(2, &latest_addr);
            let addrsize = data.vn(addrvn).get_size();
            let addout = data.new_unique_out(addrsize, newadd, glb)?;
            data.op_set_opcode(newadd, OpCode::IntAdd, glb);
            data.op_set_input(newadd, addrvn, 0)?;
            let constvn = data.new_constant(addrsize, offset as i64 as u64, glb);
            data.op_set_input(newadd, constvn, 1)?;
            data.op_insert_after(newadd, latest);
            addrvn = addout;
            latest = newadd;
        }
        data.op_set_input(newload, addrvn, 1)?;
        data.op_insert_after(newload, latest);

        data.op_remove_input(op, 1);
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_set_input(op, vnout, 0)?;

        Ok(1)
    }
}

pub struct RuleDoubleStore {
    base: RuleBase,
}

impl RuleDoubleStore {
    pub fn new(group: &str) -> RuleDoubleStore {
        RuleDoubleStore {
            base: RuleBase::new(group, 0, "doublestore"),
        }
    }

    pub fn test_indirect_use(op1: OpId, op2: OpId, indirects: &[OpId], data: &Funcdata) -> bool {
        let (first, last) = if op_order(data, op2) < op_order(data, op1) {
            (op2, op1)
        } else {
            (op1, op2)
        };
        for &indirect in indirects {
            let outvn = op_out(data, indirect);
            let mut usecount = 0;
            let mut usebyop2 = 0;
            for &op in data.vn(outvn).descend() {
                usecount += 1;
                if data.op(op).get_parent() != data.op(first).get_parent() {
                    continue;
                }
                if op_order(data, op) < op_order(data, first) {
                    continue;
                }
                if op_order(data, op) > op_order(data, last) {
                    continue;
                }
                if data.op(op).code() == OpCode::Indirect
                    && last == PcodeOp::get_op_from_const(data.vn(op_input(data, op, 1)).get_addr())
                {
                    usebyop2 += 1;
                    continue;
                }
                return false;
            }
            if usebyop2 > 0 && usecount != usebyop2 {
                return false;
            }
            if usebyop2 > 1 {
                return false;
            }
        }
        true
    }

    pub fn reassign_indirects(
        data: &mut Funcdata,
        glb: &mut Architecture,
        new_store: OpId,
        indirects: &[OpId],
    ) -> Result<()> {
        for &op in indirects {
            data.op_mut(op).set_mark();
            let vn = op_input(data, op, 0);
            if !data.vn(vn).is_written() {
                continue;
            }
            let earlyop = def_op(data, vn);
            if data.op(earlyop).is_mark() {
                let earlyin = op_input(data, earlyop, 0);
                data.op_set_input(op, earlyin, 0)?;
                data.op_destroy(earlyop)?;
            }
        }
        for &op in indirects {
            data.op_mut(op).clear_mark();
            if data.op(op).is_dead() {
                continue;
            }
            data.op_uninsert(op);
            data.op_insert_before(op, new_store);
            let iopvn = data.new_varnode_iop(new_store, glb);
            data.op_set_input(op, iopvn, 1)?;
        }
        Ok(())
    }
}

impl Rule for RuleDoubleStore {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleDoubleStore::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Store);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vnlo = op_input(data, op, 2);
        if !data.vn(vnlo).is_precis_lo() {
            return Ok(0);
        }
        if !data.vn(vnlo).is_written() {
            return Ok(0);
        }
        let subpiece_op_lo = def_op(data, vnlo);
        if data.op(subpiece_op_lo).code() != OpCode::Subpiece {
            return Ok(0);
        }
        if input_offset(data, subpiece_op_lo, 1) != 0 {
            return Ok(0);
        }
        let whole = op_input(data, subpiece_op_lo, 0);
        if data.vn(whole).is_free() {
            return Ok(0);
        }
        let whole_descend = data.vn(whole).descend().to_vec();
        for subpiece_op_hi in whole_descend {
            if data.op(subpiece_op_hi).code() != OpCode::Subpiece {
                continue;
            }
            if subpiece_op_hi == subpiece_op_lo {
                continue;
            }
            let offset = input_offset(data, subpiece_op_hi, 1) as i32;
            if offset != data.vn(vnlo).get_size() {
                continue;
            }
            let vnhi = op_out(data, subpiece_op_hi);
            if !data.vn(vnhi).is_precis_hi() {
                continue;
            }
            if data.vn(vnhi).get_size() != data.vn(whole).get_size() - offset {
                continue;
            }
            let hi_descend = data.vn(vnhi).descend().to_vec();
            for store_op2 in hi_descend {
                if data.op(store_op2).code() != OpCode::Store {
                    continue;
                }
                if op_input(data, store_op2, 2) != vnhi {
                    continue;
                }
                let mut storelo: Option<OpId> = None;
                let mut storehi: Option<OpId> = None;
                let mut spc: Option<SpaceRef> = None;
                if SplitVarnode::test_contiguous_pointers(
                    store_op2,
                    op,
                    &mut storelo,
                    &mut storehi,
                    &mut spc,
                    data,
                    glb,
                ) {
                    let storelo = present(storelo);
                    let storehi = present(storehi);
                    let spc = present(spc);
                    let mut indirects: Vec<OpId> = Vec::new();
                    let Some(latest) =
                        RuleDoubleLoad::no_write_conflict(storelo, storehi, &spc, Some(&mut indirects), data, glb)
                    else {
                        continue;
                    };
                    if !RuleDoubleStore::test_indirect_use(storelo, storehi, &indirects, data) {
                        continue;
                    }
                    let latest_addr = data.op(latest).get_addr().clone();
                    let newstore = data.new_op(3, &latest_addr);
                    let spcvn = data.new_varnode_space(&spc, glb);
                    data.op_set_opcode(newstore, OpCode::Store, glb);
                    data.op_set_input(newstore, spcvn, 0)?;
                    let mut addrvn = op_input(data, storelo, 1);
                    if data.vn(addrvn).is_constant() {
                        let addrsize = data.vn(addrvn).get_size();
                        let addroffset = data.vn(addrvn).get_offset();
                        addrvn = data.new_constant(addrsize, addroffset, glb);
                    }
                    data.op_set_input(newstore, addrvn, 1)?;
                    data.op_set_input(newstore, whole, 2)?;
                    data.op_insert_after(newstore, latest);
                    data.op_destroy(op)?;
                    data.op_destroy(store_op2)?;
                    RuleDoubleStore::reassign_indirects(data, glb, newstore, &indirects)?;
                    return Ok(1);
                }
            }
        }
        Ok(0)
    }
}
