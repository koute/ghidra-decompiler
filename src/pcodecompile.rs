use crate::error::{Error, Result};
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::semantics::{ConstTpl, ConstType, ConstructTpl, LABELBUILD, OpTpl, VarnodeTpl};
use crate::slghsymbol::{SleighSymbol, SymbolBody};
use crate::space::{AddrSpace, SpaceRef};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Location {
    filename: String,
    lineno: i32,
}

impl Location {
    pub fn new(fname: &str, line: i32) -> Location {
        Location {
            filename: fname.to_string(),
            lineno: line,
        }
    }

    pub fn get_filename(&self) -> &str {
        &self.filename
    }

    pub fn get_lineno(&self) -> i32 {
        self.lineno
    }

    pub fn format(&self) -> String {
        format!("{}:{}", self.filename, self.lineno)
    }
}

#[derive(Clone, Debug, Default)]
pub struct StarQuality {
    pub id: ConstTpl,
    pub size: u32,
}

#[derive(Clone, Debug, Default)]
pub struct ExprTree {
    ops: Vec<OpTpl>,
    outvn: Option<VarnodeTpl>,
}

impl ExprTree {
    pub fn new() -> ExprTree {
        ExprTree::default()
    }

    pub fn from_varnode(vn: VarnodeTpl) -> ExprTree {
        ExprTree {
            ops: Vec::new(),
            outvn: Some(vn),
        }
    }

    pub fn get_out(&self) -> Option<&VarnodeTpl> {
        self.outvn.as_ref()
    }

    pub fn get_ops(&self) -> &[OpTpl] {
        &self.ops
    }

    pub fn get_size(&self) -> ConstTpl {
        self.outvn.as_ref().map(|vn| vn.get_size().clone()).unwrap_or_default()
    }

    pub fn set_output(&mut self, newout: VarnodeTpl) -> Result<()> {
        let Some(outvn) = self.outvn.take() else {
            return Err(Error::Sleigh("Expression has no output".to_string()));
        };
        if outvn.is_unnamed() {
            if let Some(op) = self.ops.last_mut() {
                op.clear_output();
                op.set_output(Some(newout.clone()));
            }
        } else {
            let mut op = OpTpl::new(OpCode::Copy);
            op.add_input(outvn);
            op.set_output(Some(newout.clone()));
            self.ops.push(op);
        }
        self.outvn = Some(newout);
        Ok(())
    }

    pub fn append_params(mut op: OpTpl, param: Vec<ExprTree>) -> Vec<OpTpl> {
        let mut res = Vec::new();
        for mut expr in param {
            res.append(&mut expr.ops);
            op.add_input(expr.outvn.take().unwrap_or_default());
        }
        res.push(op);
        res
    }

    pub fn to_vector(expr: ExprTree) -> Vec<OpTpl> {
        expr.ops
    }
}

#[derive(Clone, Debug, Default)]
pub struct PcodeCompileState {
    pub defaultspace: Option<SpaceRef>,
    pub constantspace: Option<SpaceRef>,
    pub uniqspace: Option<SpaceRef>,
    pub local_labelcount: u32,
    pub enforce_local_key: bool,
}

pub type SymbolHandle = usize;

fn space_const(space: &Option<SpaceRef>) -> ConstTpl {
    match space {
        Some(spc) => ConstTpl::new_space(spc.clone()),
        None => ConstTpl::new_type(ConstType::Spaceid),
    }
}

fn real(val: u64) -> ConstTpl {
    ConstTpl::new_value(ConstType::Real, val)
}

fn is_real_zero(size: &ConstTpl) -> bool {
    size.get_type() == ConstType::Real && size.get_real() == 0
}

fn check_mismatch(vn: &VarnodeTpl, size: &ConstTpl) -> Result<()> {
    if size.get_type() == ConstType::Real
        && vn.get_size().get_type() == ConstType::Real
        && vn.get_size().get_real() != 0
        && vn.get_size().get_real() != size.get_real()
    {
        return Err(Error::Sleigh("Localtemp size mismatch".to_string()));
    }
    Ok(())
}

fn propagate_local(ops: &mut [OpTpl], offset: &ConstTpl, size: &ConstTpl) -> Result<()> {
    for op in ops.iter_mut() {
        if let Some(vn) = op.get_out_mut()
            && vn.is_local_temp()
            && vn.get_offset() == offset
        {
            check_mismatch(vn, size)?;
            vn.set_size(size.clone());
        }
        for slot in 0..op.num_input() {
            let vn = op.get_in_mut(slot);
            if vn.is_local_temp() && vn.get_offset() == offset {
                check_mismatch(vn, size)?;
                vn.set_size(size.clone());
            }
        }
    }
    Ok(())
}

pub fn force_size(vt: &mut VarnodeTpl, size: &ConstTpl, ops: &mut [OpTpl]) -> Result<()> {
    if !is_real_zero(vt.get_size()) {
        return Ok(());
    }
    vt.set_size(size.clone());
    if !vt.is_local_temp() {
        return Ok(());
    }
    let offset = vt.get_offset().clone();
    propagate_local(ops, &offset, size)
}

fn slot_varnode(op: &mut OpTpl, slot: i32) -> Option<&mut VarnodeTpl> {
    if slot == -1 {
        op.get_out_mut()
    } else if slot >= 0 && slot < op.num_input() {
        Some(op.get_in_mut(slot))
    } else {
        None
    }
}

pub fn force_size_at(ops: &mut [OpTpl], index: usize, slot: i32, size: &ConstTpl) -> Result<()> {
    let Some(vt) = slot_varnode(&mut ops[index], slot) else {
        return Ok(());
    };
    if !is_real_zero(vt.get_size()) {
        return Ok(());
    }
    vt.set_size(size.clone());
    if !vt.is_local_temp() {
        return Ok(());
    }
    let offset = vt.get_offset().clone();
    propagate_local(ops, &offset, size)
}

pub fn match_size(slot: i32, index: usize, inputonly: bool, ops: &mut [OpTpl]) -> Result<()> {
    let op = &ops[index];
    let mut matched: Option<ConstTpl> = None;
    if !inputonly
        && let Some(out) = op.get_out()
        && !out.is_zero_size()
    {
        matched = Some(out.get_size().clone());
    }
    for input in op.get_inputs() {
        if matched.is_some() {
            break;
        }
        if input.is_zero_size() {
            continue;
        }
        matched = Some(input.get_size().clone());
    }
    if let Some(size) = matched {
        force_size_at(ops, index, slot, &size)?;
    }
    Ok(())
}

fn out_zero(op: &OpTpl) -> bool {
    op.get_out().is_some_and(|out| out.is_zero_size())
}

fn in_zero(op: &OpTpl, slot: i32) -> bool {
    slot < op.num_input() && op.get_in(slot).is_zero_size()
}

pub fn fillin_zero(index: usize, ops: &mut [OpTpl]) -> Result<()> {
    let opc = ops[index].get_opcode();
    match opc {
        OpCode::Copy
        | OpCode::IntAdd
        | OpCode::IntSub
        | OpCode::Int2comp
        | OpCode::IntNegate
        | OpCode::IntXor
        | OpCode::IntAnd
        | OpCode::IntOr
        | OpCode::IntMult
        | OpCode::IntDiv
        | OpCode::IntSdiv
        | OpCode::IntRem
        | OpCode::IntSrem
        | OpCode::FloatAdd
        | OpCode::FloatDiv
        | OpCode::FloatMult
        | OpCode::FloatSub
        | OpCode::FloatNeg
        | OpCode::FloatAbs
        | OpCode::FloatSqrt
        | OpCode::FloatCeil
        | OpCode::FloatFloor
        | OpCode::FloatRound => {
            if out_zero(&ops[index]) {
                match_size(-1, index, false, ops)?;
            }
            let inputsize = ops[index].num_input();
            for slot in 0..inputsize {
                if in_zero(&ops[index], slot) {
                    match_size(slot, index, false, ops)?;
                }
            }
        }
        OpCode::IntEqual
        | OpCode::IntNotequal
        | OpCode::IntSless
        | OpCode::IntSlessequal
        | OpCode::IntLess
        | OpCode::IntLessequal
        | OpCode::IntCarry
        | OpCode::IntScarry
        | OpCode::IntSborrow
        | OpCode::FloatEqual
        | OpCode::FloatNotequal
        | OpCode::FloatLess
        | OpCode::FloatLessequal
        | OpCode::FloatNan
        | OpCode::BoolNegate
        | OpCode::BoolXor
        | OpCode::BoolAnd
        | OpCode::BoolOr => {
            if out_zero(&ops[index]) {
                force_size_at(ops, index, -1, &real(1))?;
            }
            let inputsize = ops[index].num_input();
            for slot in 0..inputsize {
                if in_zero(&ops[index], slot) {
                    match_size(slot, index, true, ops)?;
                }
            }
        }
        OpCode::IntLeft | OpCode::IntRight | OpCode::IntSright | OpCode::Subpiece => {
            if opc != OpCode::Subpiece {
                if out_zero(&ops[index]) {
                    if ops[index].num_input() > 0 && !in_zero(&ops[index], 0) {
                        let size = ops[index].get_in(0).get_size().clone();
                        force_size_at(ops, index, -1, &size)?;
                    }
                } else if in_zero(&ops[index], 0)
                    && let Some(out) = ops[index].get_out()
                {
                    let size = out.get_size().clone();
                    force_size_at(ops, index, 0, &size)?;
                }
            }
            if in_zero(&ops[index], 1) {
                force_size_at(ops, index, 1, &real(4))?;
            }
        }
        OpCode::Cpoolref => {
            if out_zero(&ops[index]) && ops[index].num_input() > 0 && !in_zero(&ops[index], 0) {
                let size = ops[index].get_in(0).get_size().clone();
                force_size_at(ops, index, -1, &size)?;
            }
            if in_zero(&ops[index], 0)
                && let Some(out) = ops[index].get_out()
                && !out.is_zero_size()
            {
                let size = out.get_size().clone();
                force_size_at(ops, index, 0, &size)?;
            }
            for slot in 1..ops[index].num_input() {
                if in_zero(&ops[index], slot) {
                    force_size_at(ops, index, slot, &real(8))?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

pub fn propagate_size(ct: &mut ConstructTpl) -> Result<bool> {
    let ops = ct.get_opvec_mut();
    let mut zerovec = Vec::new();
    for index in 0..ops.len() {
        if ops[index].is_zero_size() {
            fillin_zero(index, ops)?;
            if ops[index].is_zero_size() {
                zerovec.push(index);
            }
        }
    }
    let mut lastsize = zerovec.len() + 1;
    while zerovec.len() < lastsize {
        lastsize = zerovec.len();
        let mut zerovec2 = Vec::new();
        for index in zerovec.iter() {
            fillin_zero(*index, ops)?;
            if ops[*index].is_zero_size() {
                zerovec2.push(*index);
            }
        }
        zerovec = zerovec2;
    }
    Ok(lastsize == 0)
}

pub trait PcodeCompile {
    fn compile_state(&self) -> &PcodeCompileState;

    fn compile_state_mut(&mut self) -> &mut PcodeCompileState;

    fn allocate_temp(&mut self) -> u32;

    fn add_symbol(&mut self, sym: SleighSymbol) -> SymbolHandle;

    fn symbol_mut(&mut self, handle: SymbolHandle) -> &mut SleighSymbol;

    fn get_location(&self, handle: SymbolHandle) -> Option<Location>;

    fn report_error(&mut self, loc: Option<&Location>, msg: &str);

    fn report_warning(&mut self, loc: Option<&Location>, msg: &str);

    fn reset_label_count(&mut self) {
        self.compile_state_mut().local_labelcount = 0;
    }

    fn set_default_space(&mut self, spc: Option<SpaceRef>) {
        self.compile_state_mut().defaultspace = spc;
    }

    fn set_constant_space(&mut self, spc: Option<SpaceRef>) {
        self.compile_state_mut().constantspace = spc;
    }

    fn set_unique_space(&mut self, spc: Option<SpaceRef>) {
        self.compile_state_mut().uniqspace = spc;
    }

    fn set_enforce_local_key(&mut self, val: bool) {
        self.compile_state_mut().enforce_local_key = val;
    }

    fn get_default_space(&self) -> Option<SpaceRef> {
        self.compile_state().defaultspace.clone()
    }

    fn get_constant_space(&self) -> Option<SpaceRef> {
        self.compile_state().constantspace.clone()
    }

    fn build_temporary(&mut self) -> VarnodeTpl {
        let space = space_const(&self.compile_state().uniqspace);
        let offset = self.allocate_temp();
        let mut res = VarnodeTpl::new(space, real(offset as u64), real(0));
        res.set_unnamed(true);
        res
    }

    fn define_label(&mut self, name: &str) -> SymbolHandle {
        let index = self.compile_state().local_labelcount;
        self.compile_state_mut().local_labelcount += 1;
        self.add_symbol(SleighSymbol::new(
            name,
            SymbolBody::Label {
                index,
                isplaced: false,
                refcount: 0,
            },
        ))
    }

    fn place_label(&mut self, labsym: SymbolHandle) -> Vec<OpTpl> {
        let (placed, name, index) = match &self.symbol_mut(labsym).body {
            SymbolBody::Label { index, isplaced, .. } => (*isplaced, true, *index),
            _ => (false, false, 0),
        };
        let label_name = self.symbol_mut(labsym).get_name().to_string();
        if name && placed {
            let loc = self.get_location(labsym);
            self.report_error(loc.as_ref(), &format!("Label '{label_name}' is placed more than once"));
        }
        if let SymbolBody::Label { isplaced, .. } = &mut self.symbol_mut(labsym).body {
            *isplaced = true;
        }
        let mut op = OpTpl::new(LABELBUILD);
        let idvn = VarnodeTpl::new(
            space_const(&self.compile_state().constantspace),
            real(index as u64),
            real(4),
        );
        op.add_input(idvn);
        vec![op]
    }

    fn new_output(&mut self, uses_local_key: bool, mut rhs: ExprTree, varname: &str, size: u32) -> Result<Vec<OpTpl>> {
        let mut tmpvn = self.build_temporary();
        let rhs_size = rhs.get_size();
        if size != 0 {
            tmpvn.set_size(real(size as u64));
        } else if rhs_size.get_type() == ConstType::Real && rhs_size.get_real() != 0 {
            tmpvn.set_size(rhs_size);
        }
        rhs.set_output(tmpvn.clone())?;
        let fix = VarnodeData {
            space: tmpvn.get_space().get_space().cloned(),
            offset: tmpvn.get_offset().get_real(),
            size: tmpvn.get_size().get_real() as i32 as u32,
        };
        let handle = self.add_symbol(SleighSymbol::new(
            varname,
            SymbolBody::Varnode {
                fix,
                context_bits: false,
            },
        ));
        if !uses_local_key && self.compile_state().enforce_local_key {
            let loc = self.get_location(handle);
            self.report_error(
                loc.as_ref(),
                &format!("Must use 'local' keyword to define symbol '{varname}'"),
            );
        }
        Ok(ExprTree::to_vector(rhs))
    }

    fn new_local_definition(&mut self, varname: &str, size: u32) {
        let space = self.compile_state().uniqspace.clone();
        let offset = self.allocate_temp();
        self.add_symbol(SleighSymbol::new(
            varname,
            SymbolBody::Varnode {
                fix: VarnodeData {
                    space,
                    offset: offset as u64,
                    size,
                },
                context_bits: false,
            },
        ));
    }

    fn create_op_unary(&mut self, opc: OpCode, mut vn: ExprTree) -> ExprTree {
        let outvn = self.build_temporary();
        let mut op = OpTpl::new(opc);
        op.add_input(vn.outvn.take().unwrap_or_default());
        op.set_output(Some(outvn.clone()));
        vn.ops.push(op);
        vn.outvn = Some(outvn);
        vn
    }

    fn create_op(&mut self, opc: OpCode, mut vn1: ExprTree, mut vn2: ExprTree) -> ExprTree {
        let outvn = self.build_temporary();
        vn1.ops.append(&mut vn2.ops);
        let mut op = OpTpl::new(opc);
        op.add_input(vn1.outvn.take().unwrap_or_default());
        op.add_input(vn2.outvn.take().unwrap_or_default());
        op.set_output(Some(outvn.clone()));
        vn1.ops.push(op);
        vn1.outvn = Some(outvn);
        vn1
    }

    fn create_op_out(&mut self, outvn: VarnodeTpl, opc: OpCode, mut vn1: ExprTree, mut vn2: ExprTree) -> ExprTree {
        vn1.ops.append(&mut vn2.ops);
        let mut op = OpTpl::new(opc);
        op.add_input(vn1.outvn.take().unwrap_or_default());
        op.add_input(vn2.outvn.take().unwrap_or_default());
        op.set_output(Some(outvn.clone()));
        vn1.ops.push(op);
        vn1.outvn = Some(outvn);
        vn1
    }

    fn create_op_out_unary(&mut self, outvn: VarnodeTpl, opc: OpCode, mut vn: ExprTree) -> ExprTree {
        let mut op = OpTpl::new(opc);
        op.add_input(vn.outvn.take().unwrap_or_default());
        op.set_output(Some(outvn.clone()));
        vn.ops.push(op);
        vn.outvn = Some(outvn);
        vn
    }

    fn create_op_no_out(&mut self, opc: OpCode, mut vn: ExprTree) -> Vec<OpTpl> {
        let mut op = OpTpl::new(opc);
        op.add_input(vn.outvn.take().unwrap_or_default());
        let mut res = vn.ops;
        res.push(op);
        res
    }

    fn create_op_no_out2(&mut self, opc: OpCode, mut vn1: ExprTree, mut vn2: ExprTree) -> Vec<OpTpl> {
        let mut res = std::mem::take(&mut vn1.ops);
        res.append(&mut vn2.ops);
        let mut op = OpTpl::new(opc);
        op.add_input(vn1.outvn.take().unwrap_or_default());
        op.add_input(vn2.outvn.take().unwrap_or_default());
        res.push(op);
        res
    }

    fn create_op_const(&mut self, opc: OpCode, val: u64) -> Vec<OpTpl> {
        let vn = VarnodeTpl::new(space_const(&self.compile_state().constantspace), real(val), real(4));
        let mut op = OpTpl::new(opc);
        op.add_input(vn);
        vec![op]
    }

    fn create_load(&mut self, qual: StarQuality, mut ptr: ExprTree) -> Result<ExprTree> {
        let outvn = self.build_temporary();
        let mut op = OpTpl::new(OpCode::Load);
        let spcvn = VarnodeTpl::new(
            space_const(&self.compile_state().constantspace),
            qual.id.clone(),
            real(8),
        );
        op.add_input(spcvn);
        op.add_input(ptr.outvn.take().unwrap_or_default());
        op.set_output(Some(outvn));
        ptr.ops.push(op);
        let last = ptr.ops.len() - 1;
        if qual.size > 0 {
            force_size_at(&mut ptr.ops, last, -1, &real(qual.size as u64))?;
        }
        ptr.outvn = ptr.ops[last].get_out().cloned();
        Ok(ptr)
    }

    fn create_store(&mut self, qual: StarQuality, mut ptr: ExprTree, mut val: ExprTree) -> Result<Vec<OpTpl>> {
        let mut res = std::mem::take(&mut ptr.ops);
        res.append(&mut val.ops);
        let mut op = OpTpl::new(OpCode::Store);
        let spcvn = VarnodeTpl::new(
            space_const(&self.compile_state().constantspace),
            qual.id.clone(),
            real(8),
        );
        op.add_input(spcvn);
        op.add_input(ptr.outvn.take().unwrap_or_default());
        op.add_input(val.outvn.take().unwrap_or_default());
        res.push(op);
        let last = res.len() - 1;
        force_size_at(&mut res, last, 2, &real(qual.size as u64))?;
        Ok(res)
    }

    fn create_user_op(&mut self, index: u32, param: Vec<ExprTree>) -> ExprTree {
        let outvn = self.build_temporary();
        let mut ops = self.create_user_op_no_out(index, param);
        if let Some(last) = ops.last_mut() {
            last.set_output(Some(outvn.clone()));
        }
        ExprTree {
            ops,
            outvn: Some(outvn),
        }
    }

    fn create_user_op_no_out(&mut self, index: u32, param: Vec<ExprTree>) -> Vec<OpTpl> {
        let mut op = OpTpl::new(OpCode::Callother);
        let vn = VarnodeTpl::new(
            space_const(&self.compile_state().constantspace),
            real(index as u64),
            real(4),
        );
        op.add_input(vn);
        ExprTree::append_params(op, param)
    }

    fn create_variadic(&mut self, opc: OpCode, param: Vec<ExprTree>) -> ExprTree {
        let outvn = self.build_temporary();
        let op = OpTpl::new(opc);
        let mut ops = ExprTree::append_params(op, param);
        if let Some(last) = ops.last_mut() {
            last.set_output(Some(outvn.clone()));
        }
        ExprTree {
            ops,
            outvn: Some(outvn),
        }
    }

    fn append_op(&mut self, opc: OpCode, res: &mut ExprTree, constval: u64, constsz: i32) {
        let mut op = OpTpl::new(opc);
        let constvn = VarnodeTpl::new(
            space_const(&self.compile_state().constantspace),
            real(constval),
            real(constsz as i64 as u64),
        );
        let outvn = self.build_temporary();
        op.add_input(res.outvn.take().unwrap_or_default());
        op.add_input(constvn);
        op.set_output(Some(outvn.clone()));
        res.ops.push(op);
        res.outvn = Some(outvn);
    }

    fn build_truncated_varnode(
        &mut self,
        basevn: &VarnodeTpl,
        bitoffset: u32,
        numbits: u32,
    ) -> Result<Option<VarnodeTpl>> {
        let byteoffset = bitoffset / 8;
        let numbytes = numbits / 8;
        let mut fullsz: u64 = 0;
        if basevn.get_size().get_type() == ConstType::Real {
            fullsz = basevn.get_size().get_real();
            if fullsz == 0 {
                return Ok(None);
            }
            if (byteoffset.wrapping_add(numbytes) as u64) > fullsz {
                return Err(Error::Sleigh("Requested bit range out of bounds".to_string()));
            }
        }
        if !bitoffset.is_multiple_of(8) {
            return Ok(None);
        }
        if !numbits.is_multiple_of(8) {
            return Ok(None);
        }
        let offset_type = basevn.get_offset().get_type();
        if offset_type != ConstType::Real && offset_type != ConstType::Handle {
            return Ok(None);
        }
        let specialoff = if offset_type == ConstType::Handle {
            ConstTpl::new_handle_plus(
                basevn.get_offset().get_handle_index(),
                crate::semantics::VField::VOffsetPlus,
                byteoffset as u64,
            )
        } else {
            if basevn.get_size().get_type() != ConstType::Real {
                return Err(Error::Sleigh("Could not construct requested bit range".to_string()));
            }
            let big_endian = self
                .compile_state()
                .defaultspace
                .as_ref()
                .is_some_and(|spc| spc.is_big_endian());
            let plus = if big_endian {
                fullsz.wrapping_sub(byteoffset.wrapping_add(numbytes) as u64)
            } else {
                byteoffset as u64
            };
            real(basevn.get_offset().get_real().wrapping_add(plus))
        };
        Ok(Some(VarnodeTpl::new(
            basevn.get_space().clone(),
            specialoff,
            real(numbytes as u64),
        )))
    }

    fn assign_bit_range(
        &mut self,
        vn: VarnodeTpl,
        bitoffset: u32,
        numbits: u32,
        mut rhs: ExprTree,
    ) -> Result<Vec<OpTpl>> {
        let mut errmsg = String::new();
        if numbits == 0 {
            errmsg = "Size of bitrange is zero".to_string();
        }
        let smallsize = numbits.wrapping_add(7) / 8;
        let shiftneeded = bitoffset != 0;
        let mut zextneeded = true;
        let mut mask: u64 = 2;
        mask = !(mask
            .wrapping_shl(numbits.wrapping_sub(1))
            .wrapping_sub(1)
            .wrapping_shl(bitoffset));
        if vn.get_size().get_type() == ConstType::Real {
            let mut symsize = vn.get_size().get_real() as u32;
            if symsize > 0 {
                zextneeded = symsize > smallsize;
            }
            symsize = symsize.wrapping_mul(8);
            if bitoffset >= symsize || bitoffset.wrapping_add(numbits) > symsize {
                errmsg = "Assigned bitrange is bad".to_string();
            } else if bitoffset == 0 && numbits == symsize {
                errmsg = "Assigning to bitrange is superfluous".to_string();
            }
        }
        if !errmsg.is_empty() {
            self.report_error(None, &errmsg);
            return Ok(ExprTree::to_vector(rhs));
        }
        if let Some(outvn) = rhs.outvn.as_mut() {
            force_size(outvn, &real(smallsize as u64), &mut rhs.ops)?;
        }
        let res = match self.build_truncated_varnode(&vn, bitoffset, numbits)? {
            Some(finalout) => self.create_op_out_unary(finalout, OpCode::Copy, rhs),
            None => {
                if bitoffset.wrapping_add(numbits) > 64 {
                    errmsg = "Assigned bitrange extends past first 64 bits".to_string();
                }
                let finalout = vn.clone();
                let mut res = ExprTree::from_varnode(vn);
                self.append_op(OpCode::IntAnd, &mut res, mask, 0);
                if zextneeded {
                    rhs = self.create_op_unary(OpCode::IntZext, rhs);
                }
                if shiftneeded {
                    self.append_op(OpCode::IntLeft, &mut rhs, bitoffset as u64, 4);
                }
                self.create_op_out(finalout, OpCode::IntOr, res, rhs)
            }
        };
        if !errmsg.is_empty() {
            self.report_error(None, &errmsg);
        }
        Ok(ExprTree::to_vector(res))
    }

    fn create_bit_range(
        &mut self,
        mut vn: VarnodeTpl,
        sym_name: &str,
        loc: Option<Location>,
        bitoffset: u32,
        numbits: u32,
    ) -> Result<ExprTree> {
        let mut bitoffset = bitoffset;
        let mut errmsg = String::new();
        if numbits == 0 {
            errmsg = "Size of bitrange is zero".to_string();
        }
        let finalsize = numbits.wrapping_add(7) / 8;
        let mut truncshift = 0u32;
        let mut maskneeded = !numbits.is_multiple_of(8);
        let mut truncneeded = true;
        if errmsg.is_empty()
            && bitoffset == 0
            && !maskneeded
            && vn.get_space().get_type() == ConstType::Handle
            && vn.is_zero_size()
        {
            vn.set_size(real(finalsize as u64));
            return Ok(ExprTree::from_varnode(vn));
        }
        if errmsg.is_empty()
            && let Some(truncvn) = self.build_truncated_varnode(&vn, bitoffset, numbits)?
        {
            return Ok(ExprTree::from_varnode(truncvn));
        }
        if vn.get_size().get_type() == ConstType::Real {
            let mut insize = vn.get_size().get_real() as u32;
            if insize > 0 {
                truncneeded = finalsize < insize;
                insize = insize.wrapping_mul(8);
                if bitoffset >= insize || bitoffset.wrapping_add(numbits) > insize {
                    errmsg = "Bitrange is bad".to_string();
                }
                if maskneeded && bitoffset.wrapping_add(numbits) == insize {
                    maskneeded = false;
                }
            }
        }
        let mut mask: u64 = 2;
        mask = mask.wrapping_shl(numbits.wrapping_sub(1)).wrapping_sub(1);
        if truncneeded && bitoffset.is_multiple_of(8) {
            truncshift = bitoffset / 8;
            bitoffset = 0;
        }
        if bitoffset == 0 && !truncneeded && !maskneeded {
            errmsg = "Superfluous bitrange".to_string();
        }
        if maskneeded && finalsize > 8 {
            errmsg = format!("Illegal masked bitrange producing varnode larger than 64 bits: {sym_name}");
        }
        let mut res = ExprTree::from_varnode(vn);
        if !errmsg.is_empty() {
            self.report_error(loc.as_ref(), &errmsg);
            return Ok(res);
        }
        if bitoffset != 0 {
            self.append_op(OpCode::IntRight, &mut res, bitoffset as u64, 4);
        }
        if truncneeded {
            self.append_op(OpCode::Subpiece, &mut res, truncshift as u64, 4);
        }
        if maskneeded {
            self.append_op(OpCode::IntAnd, &mut res, mask, finalsize as i32);
        }
        if let Some(outvn) = res.outvn.as_mut() {
            force_size(outvn, &real(finalsize as u64), &mut res.ops)?;
        }
        Ok(res)
    }

    fn address_of(&mut self, var: VarnodeTpl, size: u32) -> VarnodeTpl {
        let mut size = size;
        if size == 0
            && var.get_space().get_type() == ConstType::Spaceid
            && let Some(spc) = var.get_space().get_space()
        {
            size = spc.get_addr_size();
        }
        let constspace = space_const(&self.compile_state().constantspace);
        if var.get_offset().get_type() == ConstType::Real && var.get_space().get_type() == ConstType::Spaceid {
            let wordsize = var.get_space().get_space().map(|spc| spc.get_word_size()).unwrap_or(1);
            let off = AddrSpace::byte_to_address(var.get_offset().get_real(), wordsize);
            VarnodeTpl::new(constspace, real(off), real(size as u64))
        } else {
            VarnodeTpl::new(constspace, var.get_offset().clone(), real(size as u64))
        }
    }
}
