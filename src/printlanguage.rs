use crate::address::{Address, mostsigbit_set};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::cast::CastStrategy;
use crate::comment::Comment;
use crate::database::{Database, ScopeId, SymbolId};
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::prettyprint::{Emit, EmitPrettyPrint, FuncMark, OpMark, SyntaxHighlight, TypeMark, VarnodeMark};
use crate::printc::{PRINT_C_CAPABILITY, default_token_table};
use crate::printjava::PRINT_JAVA_CAPABILITY;
use crate::stringmanage::StringManagerBase;
use crate::translate::Translate;
use crate::types::{TypeFactory, TypeId};
use crate::varnode::VarnodeId;

pub const OPEN_PAREN: &str = "(";
pub const CLOSE_PAREN: &str = ")";

pub const FORCE_HEX: u32 = 1;
pub const FORCE_DEC: u32 = 2;
pub const BESTFIT: u32 = 4;
pub const FORCE_SCINOTE: u32 = 8;
pub const FORCE_POINTER: u32 = 0x10;
pub const PRINT_LOAD_VALUE: u32 = 0x20;
pub const PRINT_STORE_VALUE: u32 = 0x40;
pub const NO_BRANCH: u32 = 0x80;
pub const ONLY_BRANCH: u32 = 0x100;
pub const COMMA_SEPARATE: u32 = 0x200;
pub const FLAT: u32 = 0x400;
pub const FALSEBRANCH: u32 = 0x800;
pub const NOFALLTHRU: u32 = 0x1000;
pub const NEGATETOKEN: u32 = 0x2000;
pub const HIDE_THISPARAM: u32 = 0x4000;
pub const PENDING_BRACE: u32 = 0x8000;

pub struct PrintContext<'a> {
    pub glb: &'a mut Architecture,
    pub data: Option<&'a mut Funcdata>,
}

impl<'a> PrintContext<'a> {
    pub fn new(glb: &'a mut Architecture, data: Option<&'a mut Funcdata>) -> PrintContext<'a> {
        PrintContext { glb, data }
    }

    pub fn data(&mut self) -> &mut Funcdata {
        self.data.as_deref_mut().expect("printing context has no function")
    }

    pub fn data_ref(&self) -> &Funcdata {
        self.data.as_deref().expect("printing context has no function")
    }

    pub fn parts(&mut self) -> (&mut Architecture, &mut Funcdata) {
        let data = self.data.as_deref_mut().expect("printing context has no function");
        (&mut *self.glb, data)
    }

    pub fn op_mark(&self, op: Option<OpId>) -> Option<OpMark> {
        let op = op?;
        let data = self.data.as_deref()?;
        Some(OpMark {
            id: op,
            time: data.op(op).get_time(),
        })
    }

    pub fn varnode_mark(&self, vn: Option<VarnodeId>) -> Option<VarnodeMark> {
        let vn = vn?;
        let data = self.data.as_deref()?;
        Some(VarnodeMark {
            id: vn,
            create_index: data.vn(vn).get_create_index(),
        })
    }

    pub fn type_mark(&self, ct: TypeId) -> TypeMark {
        let datatype = types(self.glb).get(ct);
        TypeMark {
            id: ct,
            unsized_id: datatype.get_unsized_id(),
            name: datatype.get_name().to_string(),
        }
    }
}

pub(crate) fn types(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

pub(crate) fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("type factory is not initialized")
}

pub(crate) fn symboltab(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("symbol table is not initialized")
}

pub(crate) fn symboltab_mut(glb: &mut Architecture) -> &mut Database {
    glb.symboltab.as_deref_mut().expect("symbol table is not initialized")
}

pub(crate) fn translate(glb: &Architecture) -> &dyn Translate {
    glb.translate.as_deref().expect("translator is not initialized")
}

pub trait PrintLanguageCapability: Sync {
    fn get_name(&self) -> &str;

    fn is_default(&self) -> bool;

    fn initialize(&self) {}

    fn build_language(&self, glb: &mut Architecture) -> Box<dyn PrintLanguage>;
}

static CAPABILITY_LIST: [&dyn PrintLanguageCapability; 2] = [&PRINT_C_CAPABILITY, &PRINT_JAVA_CAPABILITY];

pub fn capability_list() -> &'static [&'static dyn PrintLanguageCapability] {
    &CAPABILITY_LIST
}

pub fn get_default_capability() -> Result<&'static dyn PrintLanguageCapability> {
    match capability_list().first() {
        Some(capability) => Ok(*capability),
        None => Err(Error::Lowlevel("No print languages registered".to_string())),
    }
}

pub fn find_capability(name: &str) -> Option<&'static dyn PrintLanguageCapability> {
    capability_list()
        .iter()
        .copied()
        .find(|capability| capability.get_name() == name)
}

pub fn push_opcode(
    lng: &mut dyn PrintLanguage,
    ctx: &mut PrintContext<'_>,
    op: OpId,
    read_op: Option<OpId>,
) -> Result<()> {
    let opc = ctx.data_ref().op(op).code();
    match opc {
        OpCode::Copy => lng.op_copy(ctx, op),
        OpCode::Load => lng.op_load(ctx, op),
        OpCode::Store => lng.op_store(ctx, op),
        OpCode::Branch => lng.op_branch(ctx, op),
        OpCode::Cbranch => lng.op_cbranch(ctx, op),
        OpCode::Branchind => lng.op_branchind(ctx, op),
        OpCode::Call => lng.op_call(ctx, op),
        OpCode::Callind => lng.op_callind(ctx, op),
        OpCode::Callother => lng.op_callother(ctx, op),
        OpCode::Return => lng.op_return(ctx, op),
        OpCode::IntEqual => lng.op_int_equal(ctx, op),
        OpCode::IntNotequal => lng.op_int_not_equal(ctx, op),
        OpCode::IntSless => lng.op_int_sless(ctx, op),
        OpCode::IntSlessequal => lng.op_int_sless_equal(ctx, op),
        OpCode::IntLess => lng.op_int_less(ctx, op),
        OpCode::IntLessequal => lng.op_int_less_equal(ctx, op),
        OpCode::IntZext => lng.op_int_zext(ctx, op, read_op),
        OpCode::IntSext => lng.op_int_sext(ctx, op, read_op),
        OpCode::IntAdd => lng.op_int_add(ctx, op),
        OpCode::IntSub => lng.op_int_sub(ctx, op),
        OpCode::IntCarry => lng.op_int_carry(ctx, op),
        OpCode::IntScarry => lng.op_int_scarry(ctx, op),
        OpCode::IntSborrow => lng.op_int_sborrow(ctx, op),
        OpCode::Int2comp => lng.op_int_2comp(ctx, op),
        OpCode::IntNegate => lng.op_int_negate(ctx, op),
        OpCode::IntXor => lng.op_int_xor(ctx, op),
        OpCode::IntAnd => lng.op_int_and(ctx, op),
        OpCode::IntOr => lng.op_int_or(ctx, op),
        OpCode::IntLeft => lng.op_int_left(ctx, op),
        OpCode::IntRight => lng.op_int_right(ctx, op),
        OpCode::IntSright => lng.op_int_sright(ctx, op),
        OpCode::IntMult => lng.op_int_mult(ctx, op),
        OpCode::IntDiv => lng.op_int_div(ctx, op),
        OpCode::IntSdiv => lng.op_int_sdiv(ctx, op),
        OpCode::IntRem => lng.op_int_rem(ctx, op),
        OpCode::IntSrem => lng.op_int_srem(ctx, op),
        OpCode::BoolNegate => lng.op_bool_negate(ctx, op),
        OpCode::BoolXor => lng.op_bool_xor(ctx, op),
        OpCode::BoolAnd => lng.op_bool_and(ctx, op),
        OpCode::BoolOr => lng.op_bool_or(ctx, op),
        OpCode::FloatEqual => lng.op_float_equal(ctx, op),
        OpCode::FloatNotequal => lng.op_float_not_equal(ctx, op),
        OpCode::FloatLess => lng.op_float_less(ctx, op),
        OpCode::FloatLessequal => lng.op_float_less_equal(ctx, op),
        OpCode::FloatNan => lng.op_float_nan(ctx, op),
        OpCode::FloatAdd => lng.op_float_add(ctx, op),
        OpCode::FloatDiv => lng.op_float_div(ctx, op),
        OpCode::FloatMult => lng.op_float_mult(ctx, op),
        OpCode::FloatSub => lng.op_float_sub(ctx, op),
        OpCode::FloatNeg => lng.op_float_neg(ctx, op),
        OpCode::FloatAbs => lng.op_float_abs(ctx, op),
        OpCode::FloatSqrt => lng.op_float_sqrt(ctx, op),
        OpCode::FloatInt2float => lng.op_float_int2float(ctx, op),
        OpCode::FloatFloat2float => lng.op_float_float2float(ctx, op),
        OpCode::FloatTrunc => lng.op_float_trunc(ctx, op),
        OpCode::FloatCeil => lng.op_float_ceil(ctx, op),
        OpCode::FloatFloor => lng.op_float_floor(ctx, op),
        OpCode::FloatRound => lng.op_float_round(ctx, op),
        OpCode::Multiequal => lng.op_multiequal(ctx, op),
        OpCode::Indirect => lng.op_indirect(ctx, op),
        OpCode::Piece => lng.op_piece(ctx, op),
        OpCode::Subpiece => lng.op_subpiece(ctx, op),
        OpCode::Cast => lng.op_cast(ctx, op),
        OpCode::Ptradd => lng.op_ptradd(ctx, op),
        OpCode::Ptrsub => lng.op_ptrsub(ctx, op),
        OpCode::Segmentop => lng.op_segment_op(ctx, op),
        OpCode::Cpoolref => lng.op_cpool_ref_op(ctx, op),
        OpCode::New => lng.op_new_op(ctx, op),
        OpCode::Insert => lng.op_insert_op(ctx, op),
        OpCode::Zpull => lng.op_zpull_op(ctx, op),
        OpCode::Popcount => lng.op_popcount_op(ctx, op),
        OpCode::Lzcount => lng.op_lzcount_op(ctx, op),
        OpCode::Spull => lng.op_spull_op(ctx, op),
        OpCode::Blank | OpCode::Unused1 | OpCode::Max => {
            Err(Error::Lowlevel("no TypeOp registered for opcode".to_string()))
        }
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OpTokenType {
    Binary = 0,
    UnaryPrefix = 1,
    Postsurround = 2,
    Presurround = 3,
    Space = 4,
    Hiddenfunction = 5,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OpTokenKey {
    Hidden,
    Scope,
    ObjectMember,
    PointerMember,
    Subscript,
    FunctionCall,
    BitwiseNot,
    BooleanNot,
    UnaryMinus,
    UnaryPlus,
    Addressof,
    Dereference,
    Typecast,
    Multiply,
    Divide,
    Modulo,
    BinaryPlus,
    BinaryMinus,
    ShiftLeft,
    ShiftRight,
    ShiftSright,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Equal,
    NotEqual,
    BitwiseAnd,
    BitwiseXor,
    BitwiseOr,
    BooleanAnd,
    BooleanOr,
    BooleanXor,
    Assignment,
    Comma,
    NewOp,
    Multequal,
    Divequal,
    Remequal,
    Plusequal,
    Minusequal,
    Leftequal,
    Rightequal,
    Andequal,
    Orequal,
    Xorequal,
    TypeExprSpace,
    TypeExprNospace,
    PtrExpr,
    ArrayExpr,
    EnumCat,
    Instanceof,
}

impl OpTokenKey {
    pub const COUNT: usize = 52;

    pub fn index(self) -> usize {
        self as usize
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct OpToken {
    pub print1: &'static str,
    pub print2: &'static str,
    pub stage: i32,
    pub precedence: i32,
    pub associative: bool,
    pub tp: OpTokenType,
    pub spacing: i32,
    pub bump: i32,
    pub negate: Option<OpTokenKey>,
}

impl OpToken {
    pub const fn new(
        print1: &'static str,
        print2: &'static str,
        stage: i32,
        precedence: i32,
        associative: bool,
        tp: OpTokenType,
        spacing: i32,
        bump: i32,
        negate: Option<OpTokenKey>,
    ) -> OpToken {
        OpToken {
            print1,
            print2,
            stage,
            precedence,
            associative,
            tp,
            spacing,
            bump,
            negate,
        }
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrintTagType {
    Syntax = 0,
    Vartoken = 1,
    Functoken = 2,
    Optoken = 3,
    Typetoken = 4,
    Fieldtoken = 5,
    Bitfieldtoken = 6,
    Casetoken = 7,
    Blanktoken = 8,
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NamespaceStrategy {
    MinimalNamespaces = 0,
    NoNamespaces = 1,
    AllNamespaces = 2,
}

#[derive(Copy, Clone, Debug)]
pub struct ReversePolish {
    pub tok: OpTokenKey,
    pub visited: i32,
    pub paren: bool,
    pub op: Option<OpId>,
    pub id: i32,
    pub id2: i32,
}

#[derive(Copy, Clone, Debug)]
pub struct NodePending {
    pub vn: VarnodeId,
    pub op: Option<OpId>,
    pub vnmod: u32,
}

impl NodePending {
    pub fn new(varnode: VarnodeId, op_2: Option<OpId>, mask: u32) -> NodePending {
        NodePending {
            vn: varnode,
            op: op_2,
            vnmod: mask,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub enum AtomRef {
    #[default]
    None,
    Varnode(VarnodeId),
    Func(FuncMark),
    Type(TypeId),
    IntValue(u64),
}

#[derive(Clone, Debug)]
pub struct Atom<'a> {
    pub name: &'a str,
    pub tagtype: PrintTagType,
    pub highlight: SyntaxHighlight,
    pub op: Option<OpId>,
    pub ptr_second: AtomRef,
    pub offset: i32,
}

impl<'a> Atom<'a> {
    pub fn new(nm: &'a str, tag_type: PrintTagType, hl: SyntaxHighlight) -> Atom<'a> {
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: None,
            ptr_second: AtomRef::None,
            offset: 0,
        }
    }

    pub fn with_type(nm: &'a str, tag_type: PrintTagType, hl: SyntaxHighlight, datatype: TypeId) -> Atom<'a> {
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: None,
            ptr_second: AtomRef::Type(datatype),
            offset: 0,
        }
    }

    pub fn with_field(
        nm: &'a str,
        tag_type: PrintTagType,
        hl: SyntaxHighlight,
        datatype: TypeId,
        off: i32,
        op_2: Option<OpId>,
    ) -> Atom<'a> {
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: op_2,
            ptr_second: AtomRef::Type(datatype),
            offset: off,
        }
    }

    pub fn with_op(nm: &'a str, tag_type: PrintTagType, hl: SyntaxHighlight, op_2: Option<OpId>) -> Atom<'a> {
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: op_2,
            ptr_second: AtomRef::None,
            offset: 0,
        }
    }

    pub fn with_varnode(
        nm: &'a str,
        tag_type: PrintTagType,
        hl: SyntaxHighlight,
        op_2: Option<OpId>,
        v: Option<VarnodeId>,
    ) -> Atom<'a> {
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: op_2,
            ptr_second: match v {
                Some(vn) => AtomRef::Varnode(vn),
                None => AtomRef::None,
            },
            offset: 0,
        }
    }

    pub fn with_func(
        nm: &'a str,
        tag_type: PrintTagType,
        hl: SyntaxHighlight,
        op_2: Option<OpId>,
        f: Option<FuncMark>,
    ) -> Atom<'a> {
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: op_2,
            ptr_second: match f {
                Some(mark) => AtomRef::Func(mark),
                None => AtomRef::None,
            },
            offset: 0,
        }
    }

    pub fn with_value(
        nm: &'a str,
        tag_type: PrintTagType,
        hl: SyntaxHighlight,
        op_2: Option<OpId>,
        v: Option<VarnodeId>,
        int_value: u64,
    ) -> Atom<'a> {
        let ptr_second = if tag_type == PrintTagType::Casetoken {
            AtomRef::IntValue(int_value)
        } else {
            match v {
                Some(vn) => AtomRef::Varnode(vn),
                None => AtomRef::None,
            }
        };
        Atom {
            name: nm,
            tagtype: tag_type,
            highlight: hl,
            op: op_2,
            ptr_second,
            offset: 0,
        }
    }
}

pub struct PrintLanguageBase {
    pub name: String,
    pub modstack: Vec<u32>,
    pub scopestack: Vec<Option<ScopeId>>,
    pub revpol: Vec<ReversePolish>,
    pub nodepend: Vec<NodePending>,
    pub pending: i32,
    pub line_commentindent: i32,
    pub commentstart: String,
    pub commentend: String,
    pub tokens: Vec<OpToken>,
    pub curscope: Option<ScopeId>,
    pub cast_strategy: Option<Box<dyn CastStrategy>>,
    pub emit: Box<dyn Emit>,
    pub mods: u32,
    pub instr_comment_type: u32,
    pub head_comment_type: u32,
    pub namespc_strategy: NamespaceStrategy,
}

impl PrintLanguageBase {
    pub fn new(nm: &str) -> PrintLanguageBase {
        let mut base = PrintLanguageBase {
            name: nm.to_string(),
            modstack: Vec::new(),
            scopestack: Vec::new(),
            revpol: Vec::new(),
            nodepend: Vec::new(),
            pending: 0,
            line_commentindent: 0,
            commentstart: String::new(),
            commentend: String::new(),
            tokens: default_token_table(),
            curscope: None,
            cast_strategy: None,
            emit: Box::new(EmitPrettyPrint::new()),
            mods: 0,
            instr_comment_type: 0,
            head_comment_type: 0,
            namespc_strategy: NamespaceStrategy::MinimalNamespaces,
        };
        base.reset_defaults_internal();
        base
    }

    pub fn reset_defaults_internal(&mut self) {
        self.mods = 0;
        self.head_comment_type = Comment::HEADER | Comment::WARNINGHEADER;
        self.line_commentindent = 20;
        self.namespc_strategy = NamespaceStrategy::MinimalNamespaces;
        self.instr_comment_type = Comment::USER2 | Comment::WARNING;
    }
}

pub fn unicode_needs_escape(codepoint: i32) -> bool {
    if codepoint < 0x20 {
        return true;
    }
    if codepoint < 0x7f {
        return matches!(codepoint, 92 | 0x22 | 0x27);
    }
    if codepoint < 0x100 {
        return codepoint <= 0xa0;
    }
    if codepoint >= 0x2fa20 {
        return true;
    }
    if codepoint < 0x2000 {
        if (0x180b..=0x180e).contains(&codepoint) {
            return true;
        }
        if codepoint == 0x61c {
            return true;
        }
        if codepoint == 0x1680 {
            return true;
        }
        return false;
    }
    if codepoint < 0x3000 {
        if codepoint < 0x2010 {
            return true;
        }
        if (0x2028..=0x202f).contains(&codepoint) {
            return true;
        }
        if codepoint == 0x205f || codepoint == 0x2060 {
            return true;
        }
        if (0x2066..=0x206f).contains(&codepoint) {
            return true;
        }
        return false;
    }
    if codepoint < 0xe000 {
        if codepoint == 0x3000 {
            return true;
        }
        if codepoint >= 0xd7fc {
            return true;
        }
        return false;
    }
    if codepoint < 0xf900 {
        return true;
    }
    if (0xfe00..=0xfe0f).contains(&codepoint) {
        return true;
    }
    if codepoint == 0xfeff {
        return true;
    }
    if (0xfff0..=0xffff).contains(&codepoint) {
        if codepoint == 0xfffc || codepoint == 0xfffd {
            return false;
        }
        return true;
    }
    false
}

pub fn most_natural_base(val: u64) -> i32 {
    let mut countdec = 0;
    let mut tmp = val;
    if tmp == 0 {
        return 10;
    }
    let setdig = tmp % 10;
    if setdig == 0 || setdig == 9 {
        countdec += 1;
        tmp /= 10;
        while tmp != 0 {
            let dig = tmp % 10;
            if dig == setdig {
                countdec += 1;
            } else {
                break;
            }
            tmp /= 10;
        }
    }
    match countdec {
        0 => return 16,
        1 => {
            if tmp > 1 || setdig == 9 {
                return 16;
            }
        }
        2 => {
            if tmp > 10 {
                return 16;
            }
        }
        3 | 4 => {
            if tmp > 100 {
                return 16;
            }
        }
        _ => {
            if tmp > 1000 {
                return 16;
            }
        }
    }
    let mut counthex = 0;
    tmp = val;
    let setdig = tmp & 0xf;
    if setdig == 0 || setdig == 0xf {
        counthex += 1;
        tmp >>= 4;
        while tmp != 0 {
            let dig = tmp & 0xf;
            if dig == setdig {
                counthex += 1;
            } else {
                break;
            }
            tmp >>= 4;
        }
    }
    if countdec > counthex { 10 } else { 16 }
}

pub fn format_binary(out: &mut String, val: u64) {
    let mut pos = mostsigbit_set(val);
    if pos < 0 {
        out.push('0');
        return;
    } else if pos <= 7 {
        pos = 7;
    } else if pos <= 15 {
        pos = 15;
    } else if pos <= 31 {
        pos = 31;
    } else {
        pos = 63;
    }
    let mut mask: u64 = 1u64 << pos;
    while mask != 0 {
        if (mask & val) != 0 {
            out.push('1');
        } else {
            out.push('0');
        }
        mask >>= 1;
    }
}

pub trait PrintLanguage: PrintLanguageAny + Send {
    fn base(&self) -> &PrintLanguageBase;

    fn base_mut(&mut self) -> &mut PrintLanguageBase;

    fn as_dyn_language(&mut self) -> &mut dyn PrintLanguage;

    fn get_token(&self, key: OpTokenKey) -> &OpToken {
        &self.base().tokens[key.index()]
    }

    fn is_stack_empty(&self) -> bool {
        self.base().nodepend.is_empty() && self.base().revpol.is_empty()
    }

    fn is_mod_stack_empty(&self) -> bool {
        self.base().modstack.is_empty()
    }

    fn is_set(&self, mask: u32) -> bool {
        (self.base().mods & mask) != 0
    }

    fn push_scope(&mut self, sc: Option<ScopeId>) {
        let base = self.base_mut();
        base.scopestack.push(sc);
        base.curscope = sc;
    }

    fn pop_scope(&mut self) {
        let base = self.base_mut();
        base.scopestack.pop();
        base.curscope = match base.scopestack.last() {
            Some(scope) => *scope,
            None => None,
        };
    }

    fn push_mod(&mut self) {
        let base = self.base_mut();
        base.modstack.push(base.mods);
    }

    fn pop_mod(&mut self) {
        let base = self.base_mut();
        base.mods = base.modstack.pop().expect("print modifier stack is empty");
    }

    fn set_mod(&mut self, mask: u32) {
        self.base_mut().mods |= mask;
    }

    fn unset_mod(&mut self, mask: u32) {
        self.base_mut().mods &= !mask;
    }

    fn emit_top_op(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let mut top = *self.base().revpol.last().expect("reverse polish stack is empty");
        self.emit_op(ctx, &mut top)?;
        *self
            .base_mut()
            .revpol
            .last_mut()
            .expect("reverse polish stack is empty") = top;
        Ok(())
    }

    fn push_op(&mut self, ctx: &mut PrintContext<'_>, tok: OpTokenKey, op: Option<OpId>) -> Result<()> {
        if (self.base().pending as usize) < self.base().nodepend.len() {
            self.recurse(ctx)?;
        }
        let paren;
        let id;
        if self.base().revpol.is_empty() {
            paren = false;
            id = self.base_mut().emit.open_group()?;
        } else {
            self.emit_top_op(ctx)?;
            paren = self.parentheses(tok);
            if paren {
                id = self.base_mut().emit.open_paren(OPEN_PAREN, 0)?;
            } else {
                id = self.base_mut().emit.open_group()?;
            }
        }
        self.base_mut().revpol.push(ReversePolish {
            tok,
            visited: 0,
            paren,
            op,
            id,
            id2: 0,
        });
        Ok(())
    }

    fn push_atom(&mut self, ctx: &mut PrintContext<'_>, atom: &Atom<'_>) -> Result<()> {
        if (self.base().pending as usize) < self.base().nodepend.len() {
            self.recurse(ctx)?;
        }
        if self.base().revpol.is_empty() {
            self.emit_atom(ctx, atom)?;
        } else {
            self.emit_top_op(ctx)?;
            self.emit_atom(ctx, atom)?;
            loop {
                let (visited, stage) = {
                    let base = self.base_mut();
                    let top = base.revpol.last_mut().expect("reverse polish stack is empty");
                    top.visited += 1;
                    (top.visited, base.tokens[top.tok.index()].stage)
                };
                if visited == stage {
                    self.emit_top_op(ctx)?;
                    let top = *self.base().revpol.last().expect("reverse polish stack is empty");
                    if top.paren {
                        self.base_mut().emit.close_paren(CLOSE_PAREN, top.id)?;
                    } else {
                        self.base_mut().emit.close_group(top.id)?;
                    }
                    self.base_mut().revpol.pop();
                } else {
                    break;
                }
                if self.base().revpol.is_empty() {
                    break;
                }
            }
        }
        Ok(())
    }

    fn push_vn(&mut self, _ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>, mask: u32) -> Result<()> {
        self.base_mut().nodepend.push(NodePending::new(vn, op, mask));
        Ok(())
    }

    fn push_vn_explicit(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>) -> Result<()> {
        let (is_annotation, is_constant, offset) = {
            let varnode = ctx.data_ref().vn(vn);
            (varnode.is_annotation(), varnode.is_constant(), varnode.get_offset())
        };
        if is_annotation {
            return self.push_annotation(ctx, vn, op);
        }
        if is_constant {
            let ct = read_facing_type(ctx, vn, op)?;
            let display_format = types(ctx.glb).get(ct).get_display_format();
            return self.push_constant(ctx, offset, ct, PrintTagType::Vartoken, Some(vn), op, display_format);
        }
        self.push_symbol_detail(ctx, vn, op, true)
    }

    fn push_symbol_detail(
        &mut self,
        ctx: &mut PrintContext<'_>,
        vn: VarnodeId,
        op: Option<OpId>,
        is_read: bool,
    ) -> Result<()> {
        let high = ctx.data_ref().vn(vn).get_high()?;
        let sym = {
            let (glb, data) = ctx.parts();
            data.high_get_symbol(high, glb)
        };
        match sym {
            None => {
                let rep = ctx.data().high_get_name_representative(high);
                let addr = ctx.data_ref().vn(rep).get_addr().clone();
                self.push_unnamed_location(ctx, &addr, Some(vn), op)
            }
            Some(sym) => {
                let mut symboloff = ctx.data_ref().high(high).get_symbol_offset();
                let symtype = symboltab(ctx.glb)
                    .symbol(sym)
                    .get_type()
                    .expect("symbol has no data-type");
                let (needs_resolution, type_size) = {
                    let datatype = types(ctx.glb).get(symtype);
                    (datatype.needs_resolution(), datatype.get_size())
                };
                if symboloff == -1 {
                    if !needs_resolution {
                        return self.push_symbol(ctx, sym, Some(vn), op);
                    }
                    symboloff = 0;
                }
                let size = ctx.data_ref().vn(vn).get_size();
                if symboloff + size <= type_size {
                    let inslot = match (is_read, op) {
                        (true, Some(read_op)) => ctx.data_ref().op(read_op).get_slot(vn),
                        _ => -1,
                    };
                    self.push_partial_symbol(ctx, sym, symboloff, size, Some(vn), op, inslot, is_read)
                } else {
                    self.push_mismatch_symbol(ctx, sym, symboloff, size, Some(vn), op)
                }
            }
        }
    }

    fn parentheses(&self, op2: OpTokenKey) -> bool {
        let base = self.base();
        let top = base.revpol.last().expect("reverse polish stack is empty");
        let top_token = &base.tokens[top.tok.index()];
        let second = &base.tokens[op2.index()];
        let stage = top.visited;
        match top_token.tp {
            OpTokenType::Space | OpTokenType::Binary => {
                if top_token.precedence > second.precedence {
                    return true;
                }
                if top_token.precedence < second.precedence {
                    return false;
                }
                if top_token.associative && top.tok == op2 {
                    return false;
                }
                if second.tp == OpTokenType::Postsurround && stage == 0 {
                    return false;
                }
                true
            }
            OpTokenType::UnaryPrefix => {
                if top_token.precedence > second.precedence {
                    return true;
                }
                if top_token.precedence < second.precedence {
                    return false;
                }
                if second.tp == OpTokenType::UnaryPrefix || second.tp == OpTokenType::Presurround {
                    return false;
                }
                true
            }
            OpTokenType::Postsurround => {
                if stage == 1 {
                    return false;
                }
                if top_token.precedence > second.precedence {
                    return true;
                }
                if top_token.precedence < second.precedence {
                    return false;
                }
                if second.tp == OpTokenType::Postsurround || second.tp == OpTokenType::Binary {
                    return false;
                }
                true
            }
            OpTokenType::Presurround => {
                if stage == 0 {
                    return false;
                }
                if top_token.precedence > second.precedence {
                    return true;
                }
                if top_token.precedence < second.precedence {
                    return false;
                }
                if second.tp == OpTokenType::UnaryPrefix || second.tp == OpTokenType::Presurround {
                    return false;
                }
                true
            }
            OpTokenType::Hiddenfunction => {
                if stage == 0 && base.revpol.len() > 1 {
                    let prev_token = &base.tokens[base.revpol[base.revpol.len() - 2].tok.index()];
                    if prev_token.tp != OpTokenType::Binary && prev_token.tp != OpTokenType::UnaryPrefix {
                        return false;
                    }
                    if prev_token.precedence < second.precedence {
                        return false;
                    }
                }
                true
            }
        }
    }

    fn emit_op(&mut self, ctx: &mut PrintContext<'_>, entry: &mut ReversePolish) -> Result<()> {
        let tok = *self.get_token(entry.tok);
        let op_mark = ctx.op_mark(entry.op);
        let emit = &mut self.base_mut().emit;
        match tok.tp {
            OpTokenType::Binary => {
                if entry.visited != 1 {
                    return Ok(());
                }
                emit.spaces(tok.spacing, tok.bump)?;
                emit.tag_op(tok.print1, SyntaxHighlight::NoColor, op_mark)?;
                emit.spaces(tok.spacing, tok.bump)?;
            }
            OpTokenType::UnaryPrefix => {
                if entry.visited != 0 {
                    return Ok(());
                }
                emit.tag_op(tok.print1, SyntaxHighlight::NoColor, op_mark)?;
                emit.spaces(tok.spacing, tok.bump)?;
            }
            OpTokenType::Postsurround => {
                if entry.visited == 0 {
                    return Ok(());
                }
                if entry.visited == 1 {
                    emit.spaces(tok.spacing, tok.bump)?;
                    entry.id2 = emit.open_paren(tok.print1, 0)?;
                    emit.spaces(0, tok.bump)?;
                } else {
                    emit.close_paren(tok.print2, entry.id2)?;
                }
            }
            OpTokenType::Presurround => {
                if entry.visited == 2 {
                    return Ok(());
                }
                if entry.visited == 0 {
                    entry.id2 = emit.open_paren(tok.print1, 0)?;
                } else {
                    emit.close_paren(tok.print2, entry.id2)?;
                    emit.spaces(tok.spacing, tok.bump)?;
                }
            }
            OpTokenType::Space => {
                if entry.visited != 1 {
                    return Ok(());
                }
                emit.spaces(tok.spacing, tok.bump)?;
            }
            OpTokenType::Hiddenfunction => {}
        }
        Ok(())
    }

    fn emit_atom(&mut self, ctx: &mut PrintContext<'_>, atom: &Atom<'_>) -> Result<()> {
        let op_mark = ctx.op_mark(atom.op);
        let type_mark = match &atom.ptr_second {
            AtomRef::Type(ct) => Some(ctx.type_mark(*ct)),
            _ => None,
        };
        let varnode_mark = match &atom.ptr_second {
            AtomRef::Varnode(vn) => ctx.varnode_mark(Some(*vn)),
            _ => None,
        };
        let emit = &mut self.base_mut().emit;
        match atom.tagtype {
            PrintTagType::Syntax => emit.print(atom.name, atom.highlight)?,
            PrintTagType::Vartoken => emit.tag_variable(atom.name, atom.highlight, varnode_mark, op_mark)?,
            PrintTagType::Functoken => {
                let func = match &atom.ptr_second {
                    AtomRef::Func(mark) => Some(mark),
                    _ => None,
                };
                emit.tag_func_name(atom.name, atom.highlight, func, op_mark)?
            }
            PrintTagType::Optoken => emit.tag_op(atom.name, atom.highlight, op_mark)?,
            PrintTagType::Typetoken => emit.tag_type(atom.name, atom.highlight, type_mark.as_ref())?,
            PrintTagType::Fieldtoken => {
                emit.tag_field(atom.name, atom.highlight, type_mark.as_ref(), atom.offset, op_mark)?
            }
            PrintTagType::Bitfieldtoken => {
                emit.tag_bit_field(atom.name, atom.highlight, type_mark.as_ref(), atom.offset, op_mark)?
            }
            PrintTagType::Casetoken => {
                let value = match &atom.ptr_second {
                    AtomRef::IntValue(value) => *value,
                    _ => 0,
                };
                emit.tag_case_label(atom.name, atom.highlight, op_mark, value)?
            }
            PrintTagType::Blanktoken => {}
        }
        Ok(())
    }

    fn escape_character_data(&self, out: &mut String, buf: &[u8], count: i32, charsize: i32, bigend: bool) -> bool {
        let mut index: i32 = 0;
        let mut skip = charsize;
        let mut codepoint = 0;
        while index < count {
            codepoint = StringManagerBase::get_codepoint(&buf[index as usize..], charsize, bigend, &mut skip);
            if codepoint == 0 || codepoint == -1 {
                break;
            }
            self.print_unicode(out, codepoint);
            index += skip;
        }
        codepoint == 0
    }

    fn recurse(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let modsave = self.base().mods;
        let last_pending = self.base().pending;
        self.base_mut().pending = self.base().nodepend.len() as i32;
        while last_pending < self.base().pending {
            let pend = *self.base().nodepend.last().expect("pending varnode stack is empty");
            let vn = pend.vn;
            let op = pend.op;
            {
                let base = self.base_mut();
                base.mods = pend.vnmod;
                base.nodepend.pop();
                base.pending -= 1;
            }
            let (is_implied, has_implied_field, def_op) = {
                let varnode = ctx.data_ref().vn(vn);
                (varnode.is_implied(), varnode.has_implied_field(), varnode.get_def())
            };
            if is_implied {
                if has_implied_field {
                    self.push_implied_field(ctx, vn, op)?;
                } else {
                    let def_op = def_op.expect("implied varnode has no defining op");
                    push_opcode(self.as_dyn_language(), ctx, def_op, op)?;
                }
            } else {
                self.push_vn_explicit(ctx, vn, op)?;
            }
            let base = self.base_mut();
            base.pending = base.nodepend.len() as i32;
        }
        self.base_mut().mods = modsave;
        Ok(())
    }

    fn op_binary(&mut self, ctx: &mut PrintContext<'_>, tok: OpTokenKey, op: OpId) -> Result<()> {
        let mut tok = tok;
        if self.is_set(NEGATETOKEN) {
            let negate = self.get_token(tok).negate;
            self.unset_mod(NEGATETOKEN);
            match negate {
                Some(key) => tok = key,
                None => return Err(Error::Lowlevel("Could not find fliptoken".to_string())),
            }
        }
        self.push_op(ctx, tok, Some(op))?;
        let (in0, in1) = {
            let pcode = ctx.data_ref().op(op);
            (pcode.get_in(0), pcode.get_in(1))
        };
        let mods = self.base().mods;
        self.push_vn(ctx, in1, Some(op), mods)?;
        self.push_vn(ctx, in0, Some(op), mods)
    }

    fn op_unary(&mut self, ctx: &mut PrintContext<'_>, tok: OpTokenKey, op: OpId) -> Result<()> {
        self.push_op(ctx, tok, Some(op))?;
        let in0 = ctx.data_ref().op(op).get_in(0);
        let mods = self.base().mods;
        self.push_vn(ctx, in0, Some(op), mods)
    }

    fn get_pending(&self) -> i32 {
        self.base().pending
    }

    fn reset_defaults_internal(&mut self) {
        self.base_mut().reset_defaults_internal();
    }

    fn print_unicode(&self, out: &mut String, onechar: i32);

    fn push_type(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()>;

    fn push_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        ct: TypeId,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
        display_format: u32,
    ) -> Result<()>;

    fn push_equate(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        sz: i32,
        sym: SymbolId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<bool>;

    fn push_annotation(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>) -> Result<()>;

    fn push_symbol(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()>;

    fn push_unnamed_location(
        &mut self,
        ctx: &mut PrintContext<'_>,
        addr: &Address,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()>;

    fn push_partial_symbol(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        off: i32,
        sz: i32,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
        slot: i32,
        allow_cast: bool,
    ) -> Result<()>;

    fn push_mismatch_symbol(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        off: i32,
        sz: i32,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()>;

    fn push_implied_field(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>) -> Result<()>;

    fn emit_line_comment(&mut self, _ctx: &mut PrintContext<'_>, indent: i32, comm: &Comment) -> Result<()> {
        let text = comm.get_text();
        let bytes = text.as_bytes();
        let spc = comm.get_addr().get_space().cloned();
        let off = comm.get_addr().get_offset();
        let indent = if indent < 0 {
            self.base().line_commentindent
        } else {
            indent
        };
        let commentstart = self.base().commentstart.clone();
        let commentend = self.base().commentend.clone();
        let emit = &mut self.base_mut().emit;
        emit.tag_line_indent(indent)?;
        let id = emit.start_comment()?;
        emit.tag_comment(&commentstart, SyntaxHighlight::CommentColor, spc.as_ref(), off)?;
        let mut pos = 0usize;
        while pos < bytes.len() {
            let mut tok = bytes[pos];
            pos += 1;
            if tok == b' ' || tok == b'\t' {
                let mut count = 1;
                while pos < bytes.len() {
                    tok = bytes[pos];
                    if tok != b' ' && tok != b'\t' {
                        break;
                    }
                    count += 1;
                    pos += 1;
                }
                emit.spaces(count, 0)?;
            } else if tok == b'\n' {
                emit.tag_line()?;
            } else if tok == b'\r' {
            } else if tok == b'{' && pos < bytes.len() && bytes[pos] == b'@' {
                let mut count = 1;
                while pos < bytes.len() {
                    tok = bytes[pos];
                    count += 1;
                    pos += 1;
                    if tok == b'}' {
                        break;
                    }
                }
                let annote = &text[pos - count..pos];
                emit.tag_comment(annote, SyntaxHighlight::CommentColor, spc.as_ref(), off)?;
            } else {
                let mut count = 1;
                while pos < bytes.len() {
                    tok = bytes[pos];
                    if is_c_space(tok) {
                        break;
                    }
                    count += 1;
                    pos += 1;
                }
                let sub = &text[pos - count..pos];
                emit.tag_comment(sub, SyntaxHighlight::CommentColor, spc.as_ref(), off)?;
            }
        }
        if !commentend.is_empty() {
            emit.tag_comment(&commentend, SyntaxHighlight::CommentColor, spc.as_ref(), off)?;
        }
        emit.stop_comment(id)?;
        comm.set_emitted(true);
        Ok(())
    }

    fn emit_var_decl(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()>;

    fn emit_var_decl_statement(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()>;

    fn emit_scope_var_decls(&mut self, ctx: &mut PrintContext<'_>, sym_scope: ScopeId, cat: i32) -> Result<bool>;

    fn emit_expression(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn emit_constructor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn emit_bit_field_store(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn emit_bit_field_expression(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn emit_function_declaration(&mut self, ctx: &mut PrintContext<'_>) -> Result<()>;

    fn check_print_negation(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId) -> bool;

    fn get_name(&self) -> &str {
        &self.base().name
    }

    fn get_cast_strategy(&self) -> Option<&dyn CastStrategy> {
        self.base().cast_strategy.as_deref()
    }

    fn get_output_stream(&mut self) -> &mut Vec<u8> {
        self.base_mut().emit.get_output_stream()
    }

    fn set_output_stream(&mut self, text: Vec<u8>) {
        self.base_mut().emit.set_output_stream(text);
    }

    fn take_output_stream(&mut self) -> Vec<u8> {
        self.base_mut().emit.take_output_stream()
    }

    fn set_max_line_size(&mut self, mls: i32) -> Result<()> {
        self.base_mut().emit.set_max_line_size(mls)
    }

    fn set_indent_increment(&mut self, inc: i32) {
        self.base_mut().emit.set_indent_increment(inc);
    }

    fn set_line_comment_indent(&mut self, val: i32) -> Result<()> {
        if val < 0 || val >= self.base().emit.get_max_line_size() {
            return Err(Error::Lowlevel("Bad comment indent value".to_string()));
        }
        self.base_mut().line_commentindent = val;
        Ok(())
    }

    fn set_comment_delimeter(&mut self, start: &str, stop: &str, usecommentfill: bool) {
        let base = self.base_mut();
        base.commentstart = start.to_string();
        base.commentend = stop.to_string();
        if usecommentfill {
            base.emit.set_comment_fill(start);
        } else {
            let spaces = " ".repeat(start.len());
            base.emit.set_comment_fill(&spaces);
        }
    }

    fn get_instruction_comment(&self) -> u32 {
        self.base().instr_comment_type
    }

    fn set_instruction_comment(&mut self, val: u32) {
        self.base_mut().instr_comment_type = val;
    }

    fn set_namespace_strategy(&mut self, strat: NamespaceStrategy) {
        self.base_mut().namespc_strategy = strat;
    }

    fn get_header_comment(&self) -> u32 {
        self.base().head_comment_type
    }

    fn set_header_comment(&mut self, val: u32) {
        self.base_mut().head_comment_type = val;
    }

    fn emits_markup(&self) -> bool {
        self.base().emit.emits_markup()
    }

    fn set_markup(&mut self, val: bool) {
        self.base_mut().emit.set_markup(val);
    }

    fn set_packed_output(&mut self, val: bool) {
        self.base_mut().emit.set_packed_output(val);
    }

    fn set_flat(&mut self, val: bool) {
        if val {
            self.base_mut().mods |= FLAT;
        } else {
            self.base_mut().mods &= !FLAT;
        }
    }

    fn initialize_from_architecture(&mut self, glb: &mut Architecture) -> Result<()>;

    fn adjust_type_operators(&mut self, glb: &mut Architecture);

    fn reset_defaults(&mut self) {
        self.reset_defaults_language();
    }

    fn reset_defaults_language(&mut self) {
        self.base_mut().emit.reset_defaults();
        self.base_mut().reset_defaults_internal();
    }

    fn clear(&mut self) {
        let base = self.base_mut();
        base.emit.clear();
        if !base.modstack.is_empty() {
            base.mods = base.modstack[0];
            base.modstack.clear();
        }
        base.scopestack.clear();
        base.curscope = None;
        base.revpol.clear();
        base.pending = 0;
        base.nodepend.clear();
    }

    fn set_integer_format(&mut self, nm: &str) -> Result<()> {
        let modifier = if nm.starts_with("hex") {
            FORCE_HEX
        } else if nm.starts_with("dec") {
            FORCE_DEC
        } else if nm.starts_with("best") {
            0
        } else {
            return Err(Error::Lowlevel(format!("Unknown integer format option: {}", nm)));
        };
        let base = self.base_mut();
        base.mods &= !(FORCE_HEX | FORCE_DEC);
        base.mods |= modifier;
        Ok(())
    }

    fn set_comment_style(&mut self, nm: &str) -> Result<()>;

    fn doc_type_definitions(&mut self, ctx: &mut PrintContext<'_>) -> Result<()>;

    fn doc_all_globals(&mut self, ctx: &mut PrintContext<'_>) -> Result<()>;

    fn doc_single_global(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()>;

    fn doc_function(&mut self, ctx: &mut PrintContext<'_>) -> Result<()>;

    fn emit_block_basic(&mut self, ctx: &mut PrintContext<'_>, bb: BlockId) -> Result<()>;

    fn emit_block_graph(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_copy(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_goto(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_ls(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_condition(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_if(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_while_do(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_do_while(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_inf_loop(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn emit_block_switch(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()>;

    fn op_copy(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_load(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_store(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_branch(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_cbranch(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_branchind(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_call(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_callind(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_callother(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_constructor(&mut self, ctx: &mut PrintContext<'_>, op: OpId, with_new: bool) -> Result<()>;

    fn op_return(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_not_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_sless(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_sless_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_less(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_less_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_zext(&mut self, ctx: &mut PrintContext<'_>, op: OpId, read_op: Option<OpId>) -> Result<()>;

    fn op_int_sext(&mut self, ctx: &mut PrintContext<'_>, op: OpId, read_op: Option<OpId>) -> Result<()>;

    fn op_int_add(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_sub(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_carry(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_scarry(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_sborrow(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_2comp(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_negate(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_xor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_and(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_or(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_left(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_right(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_sright(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_mult(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_div(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_sdiv(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_rem(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_int_srem(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_bool_negate(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_bool_xor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_bool_and(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_bool_or(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_not_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_less(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_less_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_nan(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_add(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_div(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_mult(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_sub(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_neg(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_abs(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_sqrt(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_int2float(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_float2float(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_trunc(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_ceil(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_floor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_float_round(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_multiequal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_indirect(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_piece(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_subpiece(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_cast(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_ptradd(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_ptrsub(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_segment_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_cpool_ref_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_new_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_insert_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_zpull_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_popcount_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_lzcount_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn op_spull_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()>;

    fn unnamed_field(&self, off: i32, size: i32) -> String {
        format!("_{}_{}_", off, size)
    }

    fn get_scope_delimiter(&self) -> String;
}

fn is_c_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

pub(crate) fn read_facing_type(ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>) -> Result<TypeId> {
    let (glb, data) = ctx.parts();
    match op {
        Some(read_op) => data.vn_get_high_type_read_facing(vn, read_op, glb),
        None => {
            let high = data.vn(vn).get_high()?;
            Ok(data.high_get_type(high, glb))
        }
    }
}

pub(crate) fn def_facing_type(ctx: &mut PrintContext<'_>, vn: VarnodeId) -> Result<TypeId> {
    let (glb, data) = ctx.parts();
    data.vn_get_high_type_def_facing(vn, glb)
}

pub trait PrintLanguageAny {
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any;
}

impl<T: PrintLanguage + 'static> PrintLanguageAny for T {
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}
