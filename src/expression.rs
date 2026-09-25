use crate::address::{BitRange, calc_mask, signbit_negative};
use crate::architecture::Architecture;
use crate::database::SymbolId;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::{OpCode, get_booleanflip};
use crate::stdsort::std_sort;
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::varnode::VarnodeId;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub struct PcodeOpNode {
    pub op: Option<OpId>,
    pub slot: i32,
}

impl PcodeOpNode {
    pub fn new(op: OpId, slot: i32) -> PcodeOpNode {
        PcodeOpNode { op: Some(op), slot }
    }

    pub fn less_than(&self, op2: &PcodeOpNode, data: &Funcdata) -> bool {
        if self.op != op2.op {
            let first = self.op.expect("edge without op");
            let second = op2.op.expect("edge without op");
            return data.op(first).get_seq_num().get_time() < data.op(second).get_seq_num().get_time();
        }
        if self.slot != op2.slot {
            return self.slot < op2.slot;
        }
        false
    }

    pub fn compare_by_high(first_node: &PcodeOpNode, second_node: &PcodeOpNode, data: &Funcdata) -> bool {
        let first = data.op(first_node.op.expect("edge without op")).get_in(first_node.slot);
        let second = data
            .op(second_node.op.expect("edge without op"))
            .get_in(second_node.slot);
        data.vn(first).get_high_option() < data.vn(second).get_high_option()
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TraverseNode {
    pub vn: VarnodeId,
    pub flags: u32,
}

impl TraverseNode {
    pub const ACTIONALT: u32 = 1;
    pub const INDIRECT: u32 = 2;
    pub const INDIRECTALT: u32 = 4;
    pub const LSB_TRUNCATED: u32 = 8;
    pub const CONCAT_HIGH: u32 = 0x10;

    pub fn new(vn: VarnodeId, flags: u32) -> TraverseNode {
        TraverseNode { vn, flags }
    }

    pub fn is_alternate_path_valid(vn: VarnodeId, flags: u32, data: &Funcdata) -> bool {
        if (flags & (TraverseNode::INDIRECT | TraverseNode::INDIRECTALT)) == TraverseNode::INDIRECT {
            return true;
        }
        if (flags & (TraverseNode::INDIRECT | TraverseNode::INDIRECTALT)) == TraverseNode::INDIRECTALT {
            return false;
        }
        if (flags & TraverseNode::ACTIONALT) != 0 {
            return true;
        }
        if data.vn(vn).lone_descend().is_none() {
            return false;
        }
        let Some(mut op) = data.vn(vn).get_def() else {
            return true;
        };
        while data.op(op).is_incidental_copy() && data.op(op).code() == OpCode::Copy {
            let cur = data.op(op).get_in(0);
            if data.vn(cur).lone_descend().is_none() {
                return false;
            }
            match data.vn(cur).get_def() {
                None => return true,
                Some(def) => op = def,
            }
        }
        !data.op(op).is_marker()
    }
}

pub struct BooleanMatch {}

impl BooleanMatch {
    pub const SAME: i32 = 1;
    pub const COMPLEMENTARY: i32 = 2;
    pub const UNCORRELATED: i32 = 3;

    fn same_op_complement(bin1op: OpId, bin2op: OpId, data: &Funcdata) -> bool {
        let first = data.op(bin1op);
        let second = data.op(bin2op);
        let opcode = first.code();
        if opcode == OpCode::IntSless || opcode == OpCode::IntLess {
            let mut constslot = 0;
            if data.vn(first.get_in(1)).is_constant() {
                constslot = 1;
            }
            if !data.vn(first.get_in(constslot)).is_constant() {
                return false;
            }
            if !data.vn(second.get_in(1 - constslot)).is_constant() {
                return false;
            }
            if !BooleanMatch::varnode_same(first.get_in(1 - constslot), second.get_in(constslot), data) {
                return false;
            }
            let mut val1 = data.vn(first.get_in(constslot)).get_offset();
            let mut val2 = data.vn(second.get_in(1 - constslot)).get_offset();
            if constslot != 0 {
                std::mem::swap(&mut val1, &mut val2);
            }
            if val1.wrapping_add(1) != val2 {
                return false;
            }
            if val2 == 0 && opcode == OpCode::IntLess {
                return false;
            }
            if opcode == OpCode::IntSless {
                let size = data.vn(first.get_in(constslot)).get_size();
                if signbit_negative(val2, size) && !signbit_negative(val1, size) {
                    return false;
                }
            }
            return true;
        }
        false
    }

    fn varnode_same(first: VarnodeId, second: VarnodeId, data: &Funcdata) -> bool {
        if first == second {
            return true;
        }
        let first_vn = data.vn(first);
        let second_vn = data.vn(second);
        if first_vn.is_constant() && second_vn.is_constant() {
            return first_vn.get_offset() == second_vn.get_offset();
        }
        false
    }

    fn flip_result(res: i32) -> i32 {
        if res == BooleanMatch::SAME {
            BooleanMatch::COMPLEMENTARY
        } else if res == BooleanMatch::COMPLEMENTARY {
            BooleanMatch::SAME
        } else {
            res
        }
    }

    pub fn evaluate(vn1: VarnodeId, vn2: VarnodeId, depth: i32, data: &Funcdata) -> i32 {
        if vn1 == vn2 {
            return BooleanMatch::SAME;
        }
        let mut op1 = None;
        let mut opc1 = OpCode::Max;
        if data.vn(vn1).is_written() {
            let def = data.vn(vn1).get_def().expect("written varnode without defining op");
            opc1 = data.op(def).code();
            if opc1 == OpCode::BoolNegate {
                let res = BooleanMatch::evaluate(data.op(def).get_in(0), vn2, depth, data);
                return BooleanMatch::flip_result(res);
            }
            op1 = Some(def);
        }
        if !data.vn(vn2).is_written() {
            return BooleanMatch::UNCORRELATED;
        }
        let op2 = data.vn(vn2).get_def().expect("written varnode without defining op");
        let opc2 = data.op(op2).code();
        if opc2 == OpCode::BoolNegate {
            let res = BooleanMatch::evaluate(vn1, data.op(op2).get_in(0), depth, data);
            return BooleanMatch::flip_result(res);
        }
        let Some(op1) = op1 else {
            return BooleanMatch::UNCORRELATED;
        };
        let first = data.op(op1);
        let second = data.op(op2);
        if !first.is_bool_output() || !second.is_bool_output() {
            return BooleanMatch::UNCORRELATED;
        }
        let is_logical = |opc: OpCode| opc == OpCode::BoolAnd || opc == OpCode::BoolOr || opc == OpCode::BoolXor;
        if depth != 0 && is_logical(opc1) {
            if is_logical(opc2)
                && (opc1 == opc2
                    || (opc1 == OpCode::BoolAnd && opc2 == OpCode::BoolOr)
                    || (opc1 == OpCode::BoolOr && opc2 == OpCode::BoolAnd))
            {
                let mut pair1 = BooleanMatch::evaluate(first.get_in(0), second.get_in(0), depth - 1, data);
                let pair2;
                if pair1 == BooleanMatch::UNCORRELATED {
                    pair1 = BooleanMatch::evaluate(first.get_in(0), second.get_in(1), depth - 1, data);
                    if pair1 == BooleanMatch::UNCORRELATED {
                        return BooleanMatch::UNCORRELATED;
                    }
                    pair2 = BooleanMatch::evaluate(first.get_in(1), second.get_in(0), depth - 1, data);
                } else {
                    pair2 = BooleanMatch::evaluate(first.get_in(1), second.get_in(1), depth - 1, data);
                }
                if pair2 == BooleanMatch::UNCORRELATED {
                    return BooleanMatch::UNCORRELATED;
                }
                if opc1 == opc2 {
                    if pair1 == BooleanMatch::SAME && pair2 == BooleanMatch::SAME {
                        return BooleanMatch::SAME;
                    } else if opc1 == OpCode::BoolXor {
                        if pair1 == BooleanMatch::COMPLEMENTARY && pair2 == BooleanMatch::COMPLEMENTARY {
                            return BooleanMatch::SAME;
                        }
                        return BooleanMatch::COMPLEMENTARY;
                    }
                } else if pair1 == BooleanMatch::COMPLEMENTARY && pair2 == BooleanMatch::COMPLEMENTARY {
                    return BooleanMatch::COMPLEMENTARY;
                }
            }
        } else {
            if opc1 == opc2 {
                let mut same_op = true;
                let num_inputs = first.num_input();
                for index in 0..num_inputs {
                    if !BooleanMatch::varnode_same(first.get_in(index), second.get_in(index), data) {
                        same_op = false;
                        break;
                    }
                }
                if same_op {
                    return BooleanMatch::SAME;
                }
                if BooleanMatch::same_op_complement(op1, op2, data) {
                    return BooleanMatch::COMPLEMENTARY;
                }
                return BooleanMatch::UNCORRELATED;
            }
            let slot1 = 0;
            let mut slot2 = 0;
            let Some((flipped, reorder)) = get_booleanflip(opc2) else {
                return BooleanMatch::UNCORRELATED;
            };
            if opc1 != flipped {
                return BooleanMatch::UNCORRELATED;
            }
            if reorder {
                slot2 = 1;
            }
            if !BooleanMatch::varnode_same(first.get_in(slot1), second.get_in(slot2), data) {
                return BooleanMatch::UNCORRELATED;
            }
            if !BooleanMatch::varnode_same(first.get_in(1 - slot1), second.get_in(1 - slot2), data) {
                return BooleanMatch::UNCORRELATED;
            }
            return BooleanMatch::COMPLEMENTARY;
        }
        BooleanMatch::UNCORRELATED
    }
}

#[derive(Clone, Debug, Default)]
pub struct BooleanExpressionMatch {
    matchflip: bool,
}

impl BooleanExpressionMatch {
    pub const MAX_DEPTH: i32 = 1;

    pub fn new() -> BooleanExpressionMatch {
        BooleanExpressionMatch { matchflip: false }
    }

    pub fn verify_condition(&mut self, op: OpId, iop: OpId, data: &Funcdata) -> bool {
        let res = BooleanMatch::evaluate(
            data.op(op).get_in(1),
            data.op(iop).get_in(1),
            BooleanExpressionMatch::MAX_DEPTH,
            data,
        );
        if res == BooleanMatch::UNCORRELATED {
            return false;
        }
        self.matchflip = res == BooleanMatch::COMPLEMENTARY;
        if data.op(op).is_boolean_flip() {
            self.matchflip = !self.matchflip;
        }
        if data.op(iop).is_boolean_flip() {
            self.matchflip = !self.matchflip;
        }
        true
    }

    pub fn get_multi_slot(&self) -> i32 {
        -1
    }

    pub fn get_flip(&self) -> bool {
        self.matchflip
    }
}

#[derive(Copy, Clone, Debug)]
pub struct AdditiveEdge {
    op: OpId,
    slot: i32,
    vn: VarnodeId,
    mult: Option<OpId>,
}

impl AdditiveEdge {
    pub fn new(op: OpId, slot: i32, mult: Option<OpId>, data: &Funcdata) -> AdditiveEdge {
        AdditiveEdge {
            op,
            slot,
            vn: data.op(op).get_in(slot),
            mult,
        }
    }

    pub fn get_multiplier(&self) -> Option<OpId> {
        self.mult
    }

    pub fn get_op(&self) -> OpId {
        self.op
    }

    pub fn get_slot(&self) -> i32 {
        self.slot
    }

    pub fn get_varnode(&self) -> VarnodeId {
        self.vn
    }
}

pub struct TermOrder {
    root: OpId,
    terms: Vec<AdditiveEdge>,
    sorter: Vec<usize>,
}

impl TermOrder {
    pub fn new(root: OpId) -> TermOrder {
        TermOrder {
            root,
            terms: Vec::new(),
            sorter: Vec::new(),
        }
    }

    fn additive_compare(op1: &AdditiveEdge, op2: &AdditiveEdge, data: &Funcdata) -> bool {
        -1 == data.vn_term_order(op1.get_varnode(), op2.get_varnode())
    }

    pub fn get_size(&self) -> i32 {
        self.terms.len() as i32
    }

    pub fn collect(&mut self, data: &Funcdata) {
        let mut opstack: Vec<OpId> = vec![self.root];
        let mut multstack: Vec<Option<OpId>> = vec![None];

        while let Some(curop) = opstack.pop() {
            let multop = multstack.pop().expect("multiplier stack out of sync");
            let pcode_op = data.op(curop);
            for index in 0..pcode_op.num_input() {
                let curvn = pcode_op.get_in(index);
                let varnode = data.vn(curvn);
                if !varnode.is_written() {
                    self.terms.push(AdditiveEdge::new(curop, index, multop, data));
                    continue;
                }
                if varnode.lone_descend().is_none() {
                    self.terms.push(AdditiveEdge::new(curop, index, multop, data));
                    continue;
                }
                let subop = varnode.get_def().expect("written varnode without defining op");
                let sub = data.op(subop);
                if sub.code() != OpCode::IntAdd {
                    if sub.code() == OpCode::IntMult
                        && data.vn(sub.get_in(1)).is_constant()
                        && let Some(addop) = data.vn(sub.get_in(0)).get_def()
                    {
                        let add = data.op(addop);
                        if add.code() == OpCode::IntAdd {
                            let out = add.get_out().expect("INT_ADD without output");
                            if data.vn(out).lone_descend().is_some() {
                                opstack.push(addop);
                                multstack.push(Some(subop));
                                continue;
                            }
                        }
                    }
                    self.terms.push(AdditiveEdge::new(curop, index, multop, data));
                    continue;
                }
                opstack.push(subop);
                multstack.push(multop);
            }
        }
    }

    pub fn sort_terms(&mut self, data: &Funcdata) {
        self.sorter.reserve(self.terms.len());
        for index in 0..self.terms.len() {
            self.sorter.push(index);
        }
        let terms = &self.terms;
        std_sort(&mut self.sorter, |first, second| {
            TermOrder::additive_compare(&terms[*first], &terms[*second], data)
        });
    }

    pub fn get_sort(&self) -> Vec<&AdditiveEdge> {
        self.sorter.iter().map(|index| &self.terms[*index]).collect()
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct AddExpressionTerm {
    vn: Option<VarnodeId>,
    coeff: u64,
}

impl AddExpressionTerm {
    pub fn new(vn: VarnodeId, coeff: u64) -> AddExpressionTerm {
        AddExpressionTerm { vn: Some(vn), coeff }
    }

    pub fn is_equivalent(&self, op2: &AddExpressionTerm, data: &Funcdata) -> bool {
        if self.coeff != op2.coeff {
            return false;
        }
        functional_equality(
            self.vn.expect("expression term without varnode"),
            op2.vn.expect("expression term without varnode"),
            data,
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct AddExpression {
    constval: u64,
    num_terms: i32,
    terms: [AddExpressionTerm; 2],
}

impl AddExpression {
    pub fn new() -> AddExpression {
        AddExpression {
            constval: 0,
            num_terms: 0,
            terms: [AddExpressionTerm::default(); 2],
        }
    }

    fn add(&mut self, vn: VarnodeId, coeff: u64) {
        if self.num_terms < 2 {
            self.terms[self.num_terms as usize] = AddExpressionTerm::new(vn, coeff);
            self.num_terms += 1;
        }
    }

    fn gather(&mut self, vn: VarnodeId, coeff: u64, depth: i32, data: &Funcdata) {
        let varnode = data.vn(vn);
        if varnode.is_constant() {
            self.constval = self.constval.wrapping_add(coeff.wrapping_mul(varnode.get_offset()));
            self.constval &= calc_mask(varnode.get_size());
            return;
        }
        let mut depth = depth;
        let mut coeff = coeff;
        if varnode.is_written() {
            let op = data.op(varnode.get_def().expect("written varnode without defining op"));
            if op.code() == OpCode::IntAdd {
                if !data.vn(op.get_in(1)).is_constant() {
                    depth -= 1;
                }
                if depth >= 0 {
                    self.gather(op.get_in(0), coeff, depth, data);
                    self.gather(op.get_in(1), coeff, depth, data);
                    return;
                }
            } else if op.code() == OpCode::IntMult && data.vn(op.get_in(1)).is_constant() {
                coeff = coeff.wrapping_mul(data.vn(op.get_in(1)).get_offset());
                coeff &= calc_mask(varnode.get_size());
                self.gather(op.get_in(0), coeff, depth, data);
                return;
            }
        }
        self.add(vn, coeff);
    }

    pub fn gather_two_terms_subtract(&mut self, first: VarnodeId, second: VarnodeId, data: &Funcdata) {
        let depth = if data.vn(first).is_constant() || data.vn(second).is_constant() {
            1
        } else {
            0
        };
        self.gather(first, 1, depth, data);
        self.gather(second, calc_mask(data.vn(second).get_size()), depth, data);
    }

    pub fn gather_two_terms_add(&mut self, first: VarnodeId, second: VarnodeId, data: &Funcdata) {
        let depth = if data.vn(first).is_constant() || data.vn(second).is_constant() {
            1
        } else {
            0
        };
        self.gather(first, 1, depth, data);
        self.gather(second, 1, depth, data);
    }

    pub fn gather_two_terms_root(&mut self, root: VarnodeId, data: &Funcdata) {
        self.gather(root, 1, 1, data);
    }

    pub fn is_equivalent(&self, op2: &AddExpression, data: &Funcdata) -> bool {
        if self.constval != op2.constval {
            return false;
        }
        if self.num_terms != op2.num_terms {
            return false;
        }
        if self.num_terms == 1 {
            if self.terms[0].is_equivalent(&op2.terms[0], data) {
                return true;
            }
        } else if self.num_terms == 2 {
            if self.terms[0].is_equivalent(&op2.terms[0], data) && self.terms[1].is_equivalent(&op2.terms[1], data) {
                return true;
            }
            if self.terms[0].is_equivalent(&op2.terms[1], data) && self.terms[1].is_equivalent(&op2.terms[0], data) {
                return true;
            }
        }
        false
    }
}

#[derive(Clone, Debug, Default)]
pub struct BitFieldExpression {
    pub the_struct: Option<TypeId>,
    pub bitfield: Option<usize>,
    pub byte_range_offset: i32,
    pub offset_to_bit_struct: i32,
}

impl BitFieldExpression {
    fn type_factory(glb: &Architecture) -> &TypeFactory {
        glb.types.as_deref().expect("type factory is not initialized")
    }

    fn find_bitfield_index(struct_type: TypeId, range: &BitRange, glb: &Architecture) -> Option<usize> {
        let dt = BitFieldExpression::type_factory(glb).get(struct_type);
        let found = dt.find_matching_bit_field(range)?;
        (0..dt.num_bit_fields())
            .find(|index| std::ptr::eq(dt.get_bit_field(*index), found))
            .map(|index| index as usize)
    }

    pub fn get_structures(
        &mut self,
        dt: TypeId,
        init_byte_off: i32,
        least_bit_off: i32,
        is_big_endian: bool,
        glb: &Architecture,
    ) {
        let types = BitFieldExpression::type_factory(glb);
        let datatype = types.get(dt);
        let encompass_struct;
        self.the_struct = None;
        self.byte_range_offset = if init_byte_off < 0 { 0 } else { init_byte_off };
        if datatype.get_metatype() == TypeMetatype::PartialStruct {
            let struct_tmp = datatype.get_parent();
            if types.get(struct_tmp).get_metatype() != TypeMetatype::Struct {
                return;
            }
            self.byte_range_offset += datatype.get_offset();
            encompass_struct = struct_tmp;
        } else if datatype.get_metatype() == TypeMetatype::Struct {
            encompass_struct = dt;
        } else {
            return;
        }
        let mut offset = self.byte_range_offset as i64;
        let least_byte_off = least_bit_off / 8;
        if is_big_endian {
            offset += (datatype.get_size() - least_byte_off - 1) as i64;
        } else {
            offset += least_byte_off as i64;
        }
        self.the_struct = Some(encompass_struct);
        self.offset_to_bit_struct = 0;
        loop {
            let mut newoff: i64 = 0;
            let current = self.the_struct.expect("structure lost during descent");
            let Some(tmp_dt) = types.get(current).get_sub_type(offset, &mut newoff, glb) else {
                break;
            };
            if types.get(tmp_dt).get_metatype() != TypeMetatype::Struct {
                break;
            }
            self.the_struct = Some(tmp_dt);
            self.offset_to_bit_struct += (offset - newoff) as i32;
            offset = newoff;
        }
    }

    pub fn recover_structure_pointer(
        &mut self,
        vn: VarnodeId,
        offset: i32,
        data: &Funcdata,
        glb: &Architecture,
    ) -> Option<VarnodeId> {
        let struct_size = BitFieldExpression::type_factory(glb)
            .get(self.the_struct.expect("bitfield expression without structure"))
            .get_size();
        let varnode = data.vn(vn);
        if offset == 0 && struct_size == varnode.get_size() {
            return Some(vn);
        } else if varnode.is_written() {
            let ptr_sub = data.op(varnode.get_def().expect("written varnode without defining op"));
            if ptr_sub.code() == OpCode::Ptrsub && data.vn(ptr_sub.get_in(1)).get_offset() as i32 == offset {
                return Some(ptr_sub.get_in(0));
            }
        }

        if offset != 0 {
            return None;
        }
        Some(vn)
    }

    pub fn is_valid(&self) -> bool {
        self.bitfield.is_some()
    }

    pub fn get_pull_field(pull: OpId, data: &Funcdata, glb: &Architecture) -> Option<(TypeId, usize)> {
        let mut expr = BitFieldExpression::default();
        let pull_op = data.op(pull);
        let in_vn = pull_op.get_in(0);
        let least_bit_off = data.vn(pull_op.get_in(1)).get_offset() as i32;
        let bit_size = data.vn(pull_op.get_in(2)).get_offset() as i32;
        let is_big = data
            .vn(in_vn)
            .get_space()
            .expect("varnode without space")
            .is_big_endian();
        let dt = data.vn_get_type_read_facing(in_vn, pull, glb);
        expr.get_structures(dt, 0, least_bit_off, is_big, glb);
        let the_struct = expr.the_struct?;
        let range = BitRange::new(
            expr.byte_range_offset - expr.offset_to_bit_struct,
            data.vn(in_vn).get_size(),
            least_bit_off,
            bit_size,
            is_big,
        );
        BitFieldExpression::find_bitfield_index(the_struct, &range, glb).map(|index| (the_struct, index))
    }
}

pub struct InsertExpression {
    pub expr: BitFieldExpression,
    pub insert_op: OpId,
    pub symbol: Option<SymbolId>,
}

impl InsertExpression {
    pub fn new(insert: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<InsertExpression> {
        let mut res = InsertExpression {
            expr: BitFieldExpression::default(),
            insert_op: insert,
            symbol: None,
        };
        let value = data.op(insert).get_out().expect("INSERT without output");
        let high = data.vn(value).get_high()?;
        res.symbol = data.high_get_symbol(high, glb);
        let Some(symbol) = res.symbol else {
            return Ok(res);
        };
        let is_big = data
            .vn(value)
            .get_space()
            .expect("varnode without space")
            .is_big_endian();
        let least_bit_off = data.vn(data.op(insert).get_in(2)).get_offset() as i32;
        let bit_size = data.vn(data.op(insert).get_in(3)).get_offset() as i32;
        let symbol_type = glb
            .symboltab
            .as_deref()
            .expect("symbol table is not initialized")
            .symbol(symbol)
            .get_type()
            .expect("symbol without data-type");
        let symbol_offset = data.high(high).get_symbol_offset();
        res.expr
            .get_structures(symbol_type, symbol_offset, least_bit_off, is_big, glb);
        let Some(the_struct) = res.expr.the_struct else {
            return Ok(res);
        };
        let range = BitRange::new(
            res.expr.byte_range_offset - res.expr.offset_to_bit_struct,
            data.vn(value).get_size(),
            least_bit_off,
            bit_size,
            is_big,
        );
        res.expr.bitfield = BitFieldExpression::find_bitfield_index(the_struct, &range, glb);
        Ok(res)
    }

    pub fn get_range_mask(insert: OpId, data: &Funcdata) -> u64 {
        let least_bit_off = data.vn(data.op(insert).get_in(2)).get_offset() as i32;
        let bit_size = data.vn(data.op(insert).get_in(3)).get_offset() as i32;
        let mut res: u64 = !0;
        if bit_size < 64 {
            res = !res.wrapping_shl(bit_size as u32);
        }
        res.wrapping_shl(least_bit_off as u32)
    }

    pub fn get_lsb_mask(insert: OpId, data: &Funcdata) -> u64 {
        let bit_size = data.vn(data.op(insert).get_in(3)).get_offset() as i32;
        let mut res: u64 = !0;
        if bit_size < 64 {
            res = !res.wrapping_shl(bit_size as u32);
        }
        res
    }
}

pub struct InsertStoreExpression {
    pub expr: BitFieldExpression,
    pub insert_op: Option<OpId>,
    pub load_op: Option<OpId>,
    pub struct_ptr: Option<VarnodeId>,
}

impl InsertStoreExpression {
    pub fn new(store: OpId, data: &Funcdata, glb: &Architecture) -> InsertStoreExpression {
        let mut res = InsertStoreExpression {
            expr: BitFieldExpression::default(),
            insert_op: None,
            load_op: None,
            struct_ptr: None,
        };
        let value = data.op(store).get_in(2);
        if !data.vn(value).is_written() {
            return res;
        }
        let insert_op = data.vn(value).get_def().expect("written varnode without defining op");
        res.insert_op = Some(insert_op);
        if data.op(insert_op).code() != OpCode::Insert {
            return res;
        }
        let dest = data.op(insert_op).get_in(0);
        if data.vn(dest).is_written() {
            let load_op = data.vn(dest).get_def().expect("written varnode without defining op");
            res.load_op = Some(load_op);
            if data.op(load_op).code() != OpCode::Load {
                return res;
            }
        } else if !data.vn(dest).is_constant() {
            return res;
        }
        let is_big = data
            .vn(data.op(store).get_in(0))
            .get_space_from_const(&glb.manager)
            .expect("STORE without address space")
            .is_big_endian();
        let least_bit_off = data.vn(data.op(insert_op).get_in(2)).get_offset() as i32;
        let bit_size = data.vn(data.op(insert_op).get_in(3)).get_offset() as i32;
        let value_type = data.vn_get_type_def_facing(value, glb);
        res.expr.get_structures(value_type, 0, least_bit_off, is_big, glb);
        let Some(the_struct) = res.expr.the_struct else {
            return res;
        };
        let byte_range_offset = res.expr.byte_range_offset;
        res.struct_ptr = res
            .expr
            .recover_structure_pointer(data.op(store).get_in(1), byte_range_offset, data, glb);
        if res.struct_ptr.is_none() {
            return res;
        }
        let range = BitRange::new(
            res.expr.byte_range_offset - res.expr.offset_to_bit_struct,
            data.vn(value).get_size(),
            least_bit_off,
            bit_size,
            is_big,
        );
        res.expr.bitfield = BitFieldExpression::find_bitfield_index(the_struct, &range, glb);
        res
    }
}

pub struct PullExpression {
    pub expr: BitFieldExpression,
    pub pull_op: OpId,
    pub symbol: Option<SymbolId>,
    pub load_op: Option<OpId>,
    pub struct_ptr: Option<VarnodeId>,
}

impl PullExpression {
    pub fn new(pull: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<PullExpression> {
        let mut res = PullExpression {
            expr: BitFieldExpression::default(),
            pull_op: pull,
            symbol: None,
            load_op: None,
            struct_ptr: None,
        };
        let in_vn = data.op(pull).get_in(0);
        let load_def = data
            .vn(in_vn)
            .get_def()
            .filter(|def| data.op(*def).code() == OpCode::Load);
        let is_big;
        let dt;
        let offset;
        if let Some(load_op) = load_def {
            res.load_op = Some(load_op);
            is_big = data
                .vn(data.op(load_op).get_in(0))
                .get_space_from_const(&glb.manager)
                .expect("LOAD without address space")
                .is_big_endian();
            dt = data.vn_get_type_read_facing(in_vn, pull, glb);
            offset = 0;
        } else {
            let high = data.vn(in_vn).get_high()?;
            res.symbol = data.high_get_symbol(high, glb);
            let Some(symbol) = res.symbol else {
                return Ok(res);
            };
            is_big = data
                .vn(in_vn)
                .get_space()
                .expect("varnode without space")
                .is_big_endian();
            dt = glb
                .symboltab
                .as_deref()
                .expect("symbol table is not initialized")
                .symbol(symbol)
                .get_type()
                .expect("symbol without data-type");
            offset = data.high(high).get_symbol_offset();
        }
        let least_bit_off = data.vn(data.op(pull).get_in(1)).get_offset() as i32;
        let bit_size = data.vn(data.op(pull).get_in(2)).get_offset() as i32;
        res.expr.get_structures(dt, offset, least_bit_off, is_big, glb);
        let Some(the_struct) = res.expr.the_struct else {
            return Ok(res);
        };
        if let Some(load_op) = res.load_op {
            let byte_range_offset = res.expr.byte_range_offset;
            res.struct_ptr =
                res.expr
                    .recover_structure_pointer(data.op(load_op).get_in(1), byte_range_offset, data, glb);
            if res.struct_ptr.is_none() {
                return Ok(res);
            }
        }
        let range = BitRange::new(
            res.expr.byte_range_offset - res.expr.offset_to_bit_struct,
            data.vn(in_vn).get_size(),
            least_bit_off,
            bit_size,
            is_big,
        );
        res.expr.bitfield = BitFieldExpression::find_bitfield_index(the_struct, &range, glb);
        Ok(res)
    }
}

fn functional_equality_level0(vn1: VarnodeId, vn2: VarnodeId, data: &Funcdata) -> i32 {
    if vn1 == vn2 {
        return 0;
    }
    let first = data.vn(vn1);
    let second = data.vn(vn2);
    if first.get_size() != second.get_size() {
        return -1;
    }
    if first.is_constant() {
        if second.is_constant() {
            return if first.get_offset() == second.get_offset() {
                0
            } else {
                -1
            };
        }
        return -1;
    }
    if first.is_free() || second.is_free() {
        return -1;
    }
    1
}

pub fn functional_equality_level(
    vn1: VarnodeId,
    vn2: VarnodeId,
    res1: &mut [Option<VarnodeId>; 2],
    res2: &mut [Option<VarnodeId>; 2],
    data: &Funcdata,
) -> i32 {
    let mut testval = functional_equality_level0(vn1, vn2, data);
    if testval != 1 {
        return testval;
    }
    if !data.vn(vn1).is_written() || !data.vn(vn2).is_written() {
        return -1;
    }
    let op1 = data.op(data.vn(vn1).get_def().expect("written varnode without defining op"));
    let op2 = data.op(data.vn(vn2).get_def().expect("written varnode without defining op"));
    let opc = op1.code();

    if opc != op2.code() {
        return -1;
    }

    let mut num = op1.num_input();
    if num != op2.num_input() {
        return -1;
    }
    if op1.is_marker() {
        return -1;
    }
    if op2.is_call() {
        return -1;
    }
    if opc == OpCode::Load && op1.get_addr() != op2.get_addr() {
        return -1;
    }
    if num >= 3 {
        if opc != OpCode::Ptradd {
            return -1;
        }
        if data.vn(op1.get_in(2)).get_offset() != data.vn(op2.get_in(2)).get_offset() {
            return -1;
        }
        num = 2;
    }
    for index in 0..num {
        res1[index as usize] = Some(op1.get_in(index));
        res2[index as usize] = Some(op2.get_in(index));
    }
    let slot_vn = |res: &[Option<VarnodeId>; 2], index: usize| res[index].expect("missing comparison varnode");

    testval = functional_equality_level0(slot_vn(res1, 0), slot_vn(res2, 0), data);
    if testval == 0 {
        if num == 1 {
            return 0;
        }
        testval = functional_equality_level0(slot_vn(res1, 1), slot_vn(res2, 1), data);
        if testval == 0 {
            return 0;
        }
        if testval < 0 {
            return -1;
        }
        res1[0] = res1[1];
        res2[0] = res2[1];
        return 1;
    }
    if num == 1 {
        return testval;
    }
    let testval2 = functional_equality_level0(slot_vn(res1, 1), slot_vn(res2, 1), data);
    if testval2 == 0 {
        return testval;
    }
    let unmatchsize = if testval == 1 && testval2 == 1 { 2 } else { -1 };

    if !op1.is_commutative() {
        return unmatchsize;
    }
    let comm1 = functional_equality_level0(slot_vn(res1, 0), slot_vn(res2, 1), data);
    let comm2 = functional_equality_level0(slot_vn(res1, 1), slot_vn(res2, 0), data);
    if comm1 == 0 && comm2 == 0 {
        return 0;
    }
    if comm1 < 0 || comm2 < 0 {
        return unmatchsize;
    }
    if comm1 == 0 {
        res1[0] = res1[1];
        return 1;
    }
    if comm2 == 0 {
        res2[0] = res2[1];
        return 1;
    }
    if unmatchsize == 2 {
        return 2;
    }
    res2.swap(0, 1);
    2
}

pub fn functional_equality(vn1: VarnodeId, vn2: VarnodeId, data: &Funcdata) -> bool {
    let mut buf1: [Option<VarnodeId>; 2] = [None; 2];
    let mut buf2: [Option<VarnodeId>; 2] = [None; 2];
    functional_equality_level(vn1, vn2, &mut buf1, &mut buf2, data) == 0
}

pub fn functional_difference(vn1: VarnodeId, vn2: VarnodeId, depth: i32, data: &Funcdata) -> bool {
    if vn1 == vn2 {
        return false;
    }
    let first = data.vn(vn1);
    let second = data.vn(vn2);
    if !first.is_written() || !second.is_written() {
        if first.is_constant() && second.is_constant() {
            return first.get_addr() != second.get_addr();
        }
        if first.is_input() && second.is_input() {
            return false;
        }
        if first.is_free() || second.is_free() {
            return false;
        }
        return true;
    }
    let op1 = data.op(first.get_def().expect("written varnode without defining op"));
    let op2 = data.op(second.get_def().expect("written varnode without defining op"));
    if op1.code() != op2.code() {
        return true;
    }
    let num = op1.num_input();
    if num != op2.num_input() {
        return true;
    }
    if depth == 0 {
        return true;
    }
    let depth = depth - 1;
    for index in 0..num {
        if functional_difference(op1.get_in(index), op2.get_in(index), depth, data) {
            return true;
        }
    }
    false
}

pub fn root_pointer(vn: VarnodeId, offset: &mut u64, data: &Funcdata) -> VarnodeId {
    *offset = 0;
    let mut vn = vn;
    loop {
        let varnode = data.vn(vn);
        if !varnode.is_written() {
            break;
        }
        let op = data.op(varnode.get_def().expect("written varnode without defining op"));
        match op.code() {
            OpCode::Ptrsub => {
                *offset = offset.wrapping_add(data.vn(op.get_in(1)).get_offset());
                vn = op.get_in(0);
            }
            OpCode::IntAdd => {
                let cvn = op.get_in(1);
                if !data.vn(cvn).is_constant() {
                    break;
                }
                *offset = offset.wrapping_add(data.vn(cvn).get_offset());
                vn = op.get_in(0);
            }
            OpCode::Copy => {
                vn = op.get_in(0);
            }
            _ => break,
        }
    }
    vn
}

pub fn pointer_equality(vn1: VarnodeId, vn2: VarnodeId, data: &Funcdata) -> bool {
    if vn1 == vn2 {
        return true;
    }
    let mut off1: u64 = 0;
    let mut off2: u64 = 0;
    let root1 = root_pointer(vn1, &mut off1, data);
    let root2 = root_pointer(vn2, &mut off2, data);
    if off1 != off2 {
        return false;
    }
    root1 == root2
}
