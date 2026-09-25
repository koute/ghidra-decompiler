mod tables;

use std::collections::BTreeMap;

use crate::error::{Error, Result};
use crate::istream::{self, Basefield};
use crate::opcodes::OpCode;
use crate::pcodecompile::{
    ExprTree, Location, PcodeCompile, PcodeCompileState, StarQuality, SymbolHandle, propagate_size,
};
use crate::semantics::{ConstTpl, ConstType, ConstructTpl, OpTpl, VarnodeTpl};
use crate::sleighbase::SleighBase;
use crate::slghsymbol::{OperandSymbol, SleighSymbol, SymbolBody, SymbolId, SymbolType};
use crate::space::SpaceType;
use tables::*;

pub const OP_BOOL_OR: i32 = 258;
pub const OP_BOOL_AND: i32 = 259;
pub const OP_BOOL_XOR: i32 = 260;
pub const OP_EQUAL: i32 = 261;
pub const OP_NOTEQUAL: i32 = 262;
pub const OP_FEQUAL: i32 = 263;
pub const OP_FNOTEQUAL: i32 = 264;
pub const OP_GREATEQUAL: i32 = 265;
pub const OP_LESSEQUAL: i32 = 266;
pub const OP_SLESS: i32 = 267;
pub const OP_SGREATEQUAL: i32 = 268;
pub const OP_SLESSEQUAL: i32 = 269;
pub const OP_SGREAT: i32 = 270;
pub const OP_FLESS: i32 = 271;
pub const OP_FGREAT: i32 = 272;
pub const OP_FLESSEQUAL: i32 = 273;
pub const OP_FGREATEQUAL: i32 = 274;
pub const OP_LEFT: i32 = 275;
pub const OP_RIGHT: i32 = 276;
pub const OP_SRIGHT: i32 = 277;
pub const OP_FADD: i32 = 278;
pub const OP_FSUB: i32 = 279;
pub const OP_SDIV: i32 = 280;
pub const OP_SREM: i32 = 281;
pub const OP_FMULT: i32 = 282;
pub const OP_FDIV: i32 = 283;
pub const OP_ZEXT: i32 = 284;
pub const OP_CARRY: i32 = 285;
pub const OP_BORROW: i32 = 286;
pub const OP_SEXT: i32 = 287;
pub const OP_SCARRY: i32 = 288;
pub const OP_SBORROW: i32 = 289;
pub const OP_NAN: i32 = 290;
pub const OP_ABS: i32 = 291;
pub const OP_SQRT: i32 = 292;
pub const OP_CEIL: i32 = 293;
pub const OP_FLOOR: i32 = 294;
pub const OP_ROUND: i32 = 295;
pub const OP_INT2FLOAT: i32 = 296;
pub const OP_FLOAT2FLOAT: i32 = 297;
pub const OP_TRUNC: i32 = 298;
pub const OP_NEW: i32 = 299;
pub const BADINTEGER: i32 = 300;
pub const GOTO_KEY: i32 = 301;
pub const CALL_KEY: i32 = 302;
pub const RETURN_KEY: i32 = 303;
pub const IF_KEY: i32 = 304;
pub const ENDOFSTREAM: i32 = 305;
pub const LOCAL_KEY: i32 = 306;
pub const INTEGER: i32 = 307;
pub const STRING: i32 = 308;
pub const SPACESYM: i32 = 309;
pub const USEROPSYM: i32 = 310;
pub const VARSYM: i32 = 311;
pub const OPERANDSYM: i32 = 312;
pub const JUMPSYM: i32 = 313;
pub const LABELSYM: i32 = 314;

static IDENTS: [(&str, i32); 46] = [
    ("!=", OP_NOTEQUAL),
    ("&&", OP_BOOL_AND),
    ("<<", OP_LEFT),
    ("<=", OP_LESSEQUAL),
    ("==", OP_EQUAL),
    (">=", OP_GREATEQUAL),
    (">>", OP_RIGHT),
    ("^^", OP_BOOL_XOR),
    ("||", OP_BOOL_OR),
    ("abs", OP_ABS),
    ("borrow", OP_BORROW),
    ("call", CALL_KEY),
    ("carry", OP_CARRY),
    ("ceil", OP_CEIL),
    ("f!=", OP_FNOTEQUAL),
    ("f*", OP_FMULT),
    ("f+", OP_FADD),
    ("f-", OP_FSUB),
    ("f/", OP_FDIV),
    ("f<", OP_FLESS),
    ("f<=", OP_FLESSEQUAL),
    ("f==", OP_FEQUAL),
    ("f>", OP_FGREAT),
    ("f>=", OP_FGREATEQUAL),
    ("float2float", OP_FLOAT2FLOAT),
    ("floor", OP_FLOOR),
    ("goto", GOTO_KEY),
    ("if", IF_KEY),
    ("int2float", OP_INT2FLOAT),
    ("local", LOCAL_KEY),
    ("nan", OP_NAN),
    ("return", RETURN_KEY),
    ("round", OP_ROUND),
    ("s%", OP_SREM),
    ("s/", OP_SDIV),
    ("s<", OP_SLESS),
    ("s<=", OP_SLESSEQUAL),
    ("s>", OP_SGREAT),
    ("s>=", OP_SGREATEQUAL),
    ("s>>", OP_SRIGHT),
    ("sborrow", OP_SBORROW),
    ("scarry", OP_SCARRY),
    ("sext", OP_SEXT),
    ("sqrt", OP_SQRT),
    ("trunc", OP_TRUNC),
    ("zext", OP_ZEXT),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LexState {
    Start,
    Special2,
    Special3,
    Special32,
    Comment,
    Punctuation,
    Identifier,
    Hexstring,
    Decstring,
    Endstream,
    Illegal,
}

fn is_ident(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'.'
}

#[derive(Clone, Debug)]
pub struct PcodeLexer {
    curstate: LexState,
    curchar: u8,
    lookahead1: u8,
    lookahead2: u8,
    curtoken: Vec<u8>,
    endofstream: bool,
    endofstreamsent: bool,
    input: Vec<u8>,
    position: usize,
    curidentifier: String,
    curnum: u64,
}

impl Default for PcodeLexer {
    fn default() -> PcodeLexer {
        PcodeLexer::new()
    }
}

impl PcodeLexer {
    pub fn new() -> PcodeLexer {
        PcodeLexer {
            curstate: LexState::Start,
            curchar: 0,
            lookahead1: 0,
            lookahead2: 0,
            curtoken: Vec::new(),
            endofstream: false,
            endofstreamsent: false,
            input: Vec::new(),
            position: 0,
            curidentifier: String::new(),
            curnum: 0,
        }
    }

    fn read_byte(&mut self) -> Option<u8> {
        let res = self.input.get(self.position).copied();
        if res.is_some() {
            self.position += 1;
        }
        res
    }

    pub fn initialize(&mut self, input: &[u8]) {
        self.input = input.to_vec();
        self.position = 0;
        self.curstate = LexState::Start;
        self.curtoken.clear();
        self.endofstream = false;
        self.endofstreamsent = false;
        self.lookahead1 = 0;
        self.lookahead2 = 0;
        match self.read_byte() {
            Some(byte) => self.lookahead1 = byte,
            None => {
                self.endofstream = true;
                self.lookahead1 = 0;
                return;
            }
        }
        match self.read_byte() {
            Some(byte) => self.lookahead2 = byte,
            None => {
                self.endofstream = true;
                self.lookahead2 = 0;
            }
        }
    }

    pub fn get_identifier(&self) -> &str {
        &self.curidentifier
    }

    pub fn get_number(&self) -> u64 {
        self.curnum
    }

    fn starttoken(&mut self) {
        self.curtoken.clear();
        self.curtoken.push(self.curchar);
    }

    fn advancetoken(&mut self) {
        self.curtoken.push(self.curchar);
    }

    fn find_identifier(text: &str) -> i32 {
        let mut low: i32 = 0;
        let mut high: i32 = IDENTS.len() as i32 - 1;
        loop {
            let targ = (low + high) / 2;
            let comp = text.as_bytes().cmp(IDENTS[targ as usize].0.as_bytes());
            match comp {
                std::cmp::Ordering::Less => high = targ - 1,
                std::cmp::Ordering::Greater => low = targ + 1,
                std::cmp::Ordering::Equal => return targ,
            }
            if low > high {
                return -1;
            }
        }
    }

    fn special_start(&mut self, next: LexState) -> LexState {
        self.starttoken();
        self.curstate = next;
        LexState::Start
    }

    fn identifier_start(&mut self) -> LexState {
        self.starttoken();
        if is_ident(self.lookahead1) {
            self.curstate = LexState::Identifier;
            return LexState::Start;
        }
        self.curstate = LexState::Start;
        LexState::Identifier
    }

    fn move_state(&mut self) -> LexState {
        let curchar = self.curchar;
        let look1 = self.lookahead1;
        let look2 = self.lookahead2;
        match self.curstate {
            LexState::Start => match curchar {
                b'#' => {
                    self.curstate = LexState::Comment;
                    LexState::Start
                }
                b'|' | b'&' | b'^' | b'=' => {
                    if look1 == curchar {
                        return self.special_start(LexState::Special2);
                    }
                    LexState::Punctuation
                }
                b'>' | b'<' => {
                    if look1 == curchar || look1 == b'=' {
                        return self.special_start(LexState::Special2);
                    }
                    LexState::Punctuation
                }
                b'!' => {
                    if look1 == b'=' {
                        return self.special_start(LexState::Special2);
                    }
                    LexState::Punctuation
                }
                b'(' | b')' | b',' | b':' | b'[' | b']' | b';' | b'+' | b'-' | b'*' | b'/' | b'%' | b'~' => {
                    LexState::Punctuation
                }
                b's' | b'f' => {
                    if curchar == b's' {
                        if look1 == b'/' || look1 == b'%' {
                            return self.special_start(LexState::Special2);
                        } else if look1 == b'<' {
                            let next = if look2 == b'=' {
                                LexState::Special3
                            } else {
                                LexState::Special2
                            };
                            return self.special_start(next);
                        } else if look1 == b'>' {
                            let next = if look2 == b'>' || look2 == b'=' {
                                LexState::Special3
                            } else {
                                LexState::Special2
                            };
                            return self.special_start(next);
                        }
                    } else if look1 == b'+' || look1 == b'-' || look1 == b'*' || look1 == b'/' {
                        return self.special_start(LexState::Special2);
                    } else if (look1 == b'=' || look1 == b'!') && look2 == b'=' {
                        return self.special_start(LexState::Special3);
                    } else if look1 == b'<' || look1 == b'>' {
                        let next = if look2 == b'=' {
                            LexState::Special3
                        } else {
                            LexState::Special2
                        };
                        return self.special_start(next);
                    }
                    self.identifier_start()
                }
                b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'.' => self.identifier_start(),
                b'0' => {
                    self.starttoken();
                    if look1 == b'x' {
                        self.curstate = LexState::Hexstring;
                        return LexState::Start;
                    }
                    if look1.is_ascii_digit() {
                        self.curstate = LexState::Decstring;
                        return LexState::Start;
                    }
                    self.curstate = LexState::Start;
                    LexState::Decstring
                }
                b'1'..=b'9' => {
                    self.starttoken();
                    if look1.is_ascii_digit() {
                        self.curstate = LexState::Decstring;
                        return LexState::Start;
                    }
                    self.curstate = LexState::Start;
                    LexState::Decstring
                }
                b'\n' | b' ' | b'\t' | 0x0b | b'\r' => LexState::Start,
                0 => {
                    self.curstate = LexState::Endstream;
                    LexState::Endstream
                }
                _ => {
                    self.curstate = LexState::Illegal;
                    LexState::Illegal
                }
            },
            LexState::Special2 => {
                self.advancetoken();
                self.curstate = LexState::Start;
                LexState::Identifier
            }
            LexState::Special3 => {
                self.advancetoken();
                self.curstate = LexState::Special32;
                LexState::Start
            }
            LexState::Special32 => {
                self.advancetoken();
                self.curstate = LexState::Start;
                LexState::Identifier
            }
            LexState::Comment => {
                if curchar == b'\n' {
                    self.curstate = LexState::Start;
                } else if curchar == 0 {
                    self.curstate = LexState::Endstream;
                    return LexState::Endstream;
                }
                LexState::Start
            }
            LexState::Identifier => {
                self.advancetoken();
                if is_ident(look1) {
                    return LexState::Start;
                }
                self.curstate = LexState::Start;
                LexState::Identifier
            }
            LexState::Hexstring => {
                self.advancetoken();
                if look1.is_ascii_hexdigit() {
                    return LexState::Start;
                }
                self.curstate = LexState::Start;
                LexState::Hexstring
            }
            LexState::Decstring => {
                self.advancetoken();
                if look1.is_ascii_digit() {
                    return LexState::Start;
                }
                self.curstate = LexState::Start;
                LexState::Decstring
            }
            _ => {
                self.curstate = LexState::Endstream;
                LexState::Endstream
            }
        }
    }

    pub fn get_next_token(&mut self) -> i32 {
        let mut tok;
        loop {
            self.curchar = self.lookahead1;
            self.lookahead1 = self.lookahead2;
            if self.endofstream {
                self.lookahead2 = 0;
            } else {
                match self.read_byte() {
                    Some(byte) => self.lookahead2 = byte,
                    None => {
                        self.endofstream = true;
                        self.lookahead2 = 0;
                    }
                }
            }
            tok = self.move_state();
            if tok != LexState::Start {
                break;
            }
        }
        match tok {
            LexState::Identifier => {
                self.curidentifier = String::from_utf8_lossy(&self.curtoken).into_owned();
                let num = PcodeLexer::find_identifier(&self.curidentifier);
                if num < 0 {
                    return STRING;
                }
                IDENTS[num as usize].1
            }
            LexState::Hexstring | LexState::Decstring => {
                let text = String::from_utf8_lossy(&self.curtoken).into_owned();
                match istream::extract_u64(&text, Basefield::Auto) {
                    Some(extraction) if !extraction.failed => {
                        self.curnum = extraction.value;
                        INTEGER
                    }
                    Some(extraction) => {
                        self.curnum = extraction.value;
                        BADINTEGER
                    }
                    None => BADINTEGER,
                }
            }
            LexState::Endstream => {
                if !self.endofstreamsent {
                    self.endofstreamsent = true;
                    return ENDOFSTREAM;
                }
                0
            }
            LexState::Illegal => 0,
            _ => self.curchar as i8 as i32,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SnippetSymbol {
    Local(SymbolHandle),
    Global(SymbolId),
}

#[derive(Debug, Default)]
enum SemValue {
    #[default]
    Empty,
    Integer(u64),
    Text(String),
    Symbol(SnippetSymbol),
    Param(Vec<ExprTree>),
    Star(StarQuality),
    Varnode(VarnodeTpl),
    Tree(ExprTree),
    Stmt(Vec<OpTpl>),
    Sem(ConstructTpl),
}

impl SemValue {
    fn integer(self) -> u64 {
        match self {
            SemValue::Integer(val) => val,
            _ => 0,
        }
    }

    fn text(self) -> String {
        match self {
            SemValue::Text(text) => text,
            _ => String::new(),
        }
    }

    fn symbol(self) -> SnippetSymbol {
        match self {
            SemValue::Symbol(sym) => sym,
            _ => SnippetSymbol::Local(usize::MAX),
        }
    }

    fn param(self) -> Vec<ExprTree> {
        match self {
            SemValue::Param(param) => param,
            _ => Vec::new(),
        }
    }

    fn star(self) -> StarQuality {
        match self {
            SemValue::Star(star) => star,
            _ => StarQuality::default(),
        }
    }

    fn varnode(self) -> VarnodeTpl {
        match self {
            SemValue::Varnode(vn) => vn,
            _ => VarnodeTpl::default(),
        }
    }

    fn tree(self) -> ExprTree {
        match self {
            SemValue::Tree(tree) => tree,
            _ => ExprTree::new(),
        }
    }

    fn stmt(self) -> Vec<OpTpl> {
        match self {
            SemValue::Stmt(stmt) => stmt,
            _ => Vec::new(),
        }
    }

    fn sem(self) -> ConstructTpl {
        match self {
            SemValue::Sem(sem) => sem,
            _ => ConstructTpl::new(),
        }
    }
}

enum ActionFailure {
    Rejected,
    Thrown(Error),
}

impl From<Error> for ActionFailure {
    fn from(err: Error) -> ActionFailure {
        ActionFailure::Thrown(err)
    }
}

type ActionResult = std::result::Result<SemValue, ActionFailure>;

const YYEMPTY: i32 = -2;
const YYEOF: i32 = 0;
const YYTERROR: i32 = 1;
const YYUNDEFTOK: i32 = 2;
const YYMAXDEPTH: usize = 10000;

fn yytranslate(token: i32) -> i32 {
    if (0..=YYMAXUTOK).contains(&token) {
        YYTRANSLATE[token as usize] as i32
    } else {
        YYUNDEFTOK
    }
}

fn binary_opcode(rule: usize) -> Option<(OpCode, bool)> {
    let res = match rule {
        29 => (OpCode::IntAdd, false),
        30 => (OpCode::IntSub, false),
        31 => (OpCode::IntEqual, false),
        32 => (OpCode::IntNotequal, false),
        33 => (OpCode::IntLess, false),
        34 => (OpCode::IntLessequal, true),
        35 => (OpCode::IntLessequal, false),
        36 => (OpCode::IntLess, true),
        37 => (OpCode::IntSless, false),
        38 => (OpCode::IntSlessequal, true),
        39 => (OpCode::IntSlessequal, false),
        40 => (OpCode::IntSless, true),
        43 => (OpCode::IntXor, false),
        44 => (OpCode::IntAnd, false),
        45 => (OpCode::IntOr, false),
        46 => (OpCode::IntLeft, false),
        47 => (OpCode::IntRight, false),
        48 => (OpCode::IntSright, false),
        49 => (OpCode::IntMult, false),
        50 => (OpCode::IntDiv, false),
        51 => (OpCode::IntSdiv, false),
        52 => (OpCode::IntRem, false),
        53 => (OpCode::IntSrem, false),
        55 => (OpCode::BoolXor, false),
        56 => (OpCode::BoolAnd, false),
        57 => (OpCode::BoolOr, false),
        58 => (OpCode::FloatEqual, false),
        59 => (OpCode::FloatNotequal, false),
        60 => (OpCode::FloatLess, false),
        61 => (OpCode::FloatLess, true),
        62 => (OpCode::FloatLessequal, false),
        63 => (OpCode::FloatLessequal, true),
        64 => (OpCode::FloatAdd, false),
        65 => (OpCode::FloatSub, false),
        66 => (OpCode::FloatMult, false),
        67 => (OpCode::FloatDiv, false),
        _ => return None,
    };
    Some(res)
}

fn prefix_unary_opcode(rule: usize) -> Option<OpCode> {
    match rule {
        41 => Some(OpCode::Int2comp),
        42 => Some(OpCode::IntNegate),
        54 => Some(OpCode::BoolNegate),
        68 => Some(OpCode::FloatNeg),
        _ => None,
    }
}

fn function_unary_opcode(rule: usize) -> Option<OpCode> {
    match rule {
        69 => Some(OpCode::FloatAbs),
        70 => Some(OpCode::FloatSqrt),
        71 => Some(OpCode::IntSext),
        72 => Some(OpCode::IntZext),
        76 => Some(OpCode::FloatFloat2float),
        77 => Some(OpCode::FloatInt2float),
        78 => Some(OpCode::FloatNan),
        79 => Some(OpCode::FloatTrunc),
        80 => Some(OpCode::FloatCeil),
        81 => Some(OpCode::FloatFloor),
        82 => Some(OpCode::FloatRound),
        83 => Some(OpCode::New),
        _ => None,
    }
}

fn function_binary_opcode(rule: usize) -> Option<OpCode> {
    match rule {
        73 => Some(OpCode::IntCarry),
        74 => Some(OpCode::IntScarry),
        75 => Some(OpCode::IntSborrow),
        84 => Some(OpCode::New),
        _ => None,
    }
}

fn real(val: u64) -> ConstTpl {
    ConstTpl::new_value(ConstType::Real, val)
}

pub struct PcodeSnippet<'a> {
    lexer: PcodeLexer,
    sleigh: &'a SleighBase,
    locals: Vec<SleighSymbol>,
    tree: BTreeMap<String, SymbolHandle>,
    tempbase: u32,
    errorcount: i32,
    firsterror: String,
    result: Option<ConstructTpl>,
    state: PcodeCompileState,
}

impl<'a> PcodeSnippet<'a> {
    pub fn new(sleigh: &'a SleighBase) -> PcodeSnippet<'a> {
        let manager = &sleigh.translate.manager;
        let mut snippet = PcodeSnippet {
            lexer: PcodeLexer::new(),
            sleigh,
            locals: Vec::new(),
            tree: BTreeMap::new(),
            tempbase: 0,
            errorcount: 0,
            firsterror: String::new(),
            result: None,
            state: PcodeCompileState::default(),
        };
        snippet.set_default_space(manager.get_default_code_space());
        snippet.set_constant_space(manager.get_constant_space());
        snippet.set_unique_space(manager.get_unique_space());
        for index in 0..manager.num_spaces() {
            let Some(spc) = manager.get_space(index) else {
                continue;
            };
            let space_type = spc.get_type();
            if matches!(
                space_type,
                SpaceType::Constant | SpaceType::Processor | SpaceType::Spacebase | SpaceType::Internal
            ) {
                let name = spc.get_name().to_string();
                if !snippet.tree.contains_key(&name) {
                    snippet
                        .locals
                        .push(SleighSymbol::new(&name, SymbolBody::Space { space: spc }));
                    snippet.tree.insert(name, snippet.locals.len() - 1);
                }
            }
        }
        let const_space = manager.get_constant_space();
        snippet.add_symbol(SleighSymbol::new(
            "inst_dest",
            SymbolBody::Flowdest {
                const_space: const_space.clone(),
            },
        ));
        snippet.add_symbol(SleighSymbol::new("inst_ref", SymbolBody::Flowref { const_space }));
        snippet
    }

    pub fn set_result(&mut self, res: ConstructTpl) {
        self.result = Some(res);
    }

    pub fn release_result(&mut self) -> Option<ConstructTpl> {
        self.result.take()
    }

    pub fn has_errors(&self) -> bool {
        self.errorcount != 0
    }

    pub fn get_error_message(&self) -> &str {
        &self.firsterror
    }

    pub fn set_unique_base(&mut self, val: u32) {
        self.tempbase = val;
    }

    pub fn get_unique_base(&self) -> u32 {
        self.tempbase
    }

    pub fn clear(&mut self) {
        let locals = &self.locals;
        self.tree
            .retain(|_, handle| locals[*handle].get_type() == SymbolType::Space);
        self.result = None;
        self.errorcount = 0;
        self.firsterror.clear();
        self.reset_label_count();
    }

    pub fn add_operand(&mut self, name: &str, index: i32) {
        let oper = OperandSymbol {
            hand: index,
            ..OperandSymbol::default()
        };
        self.add_symbol(SleighSymbol::new(name, SymbolBody::Operand(Box::new(oper))));
    }

    fn symbol_ref(&self, sym: SnippetSymbol) -> &SleighSymbol {
        match sym {
            SnippetSymbol::Local(handle) => self
                .locals
                .get(handle)
                .unwrap_or_else(|| self.sleigh.symtab.get(u32::MAX)),
            SnippetSymbol::Global(id) => self.sleigh.symtab.get(id),
        }
    }

    fn symbol_varnode(&self, sym: SnippetSymbol) -> VarnodeTpl {
        self.symbol_ref(sym)
            .get_varnode(&self.sleigh.symtab)
            .unwrap_or_default()
    }

    fn lex(&mut self) -> (i32, SemValue) {
        let tok = self.lexer.get_next_token();
        if tok == STRING {
            let name = self.lexer.get_identifier().to_string();
            let found = match self.tree.get(&name) {
                Some(handle) => Some(SnippetSymbol::Local(*handle)),
                None => self
                    .sleigh
                    .symtab
                    .find_symbol(&name)
                    .map(|sym| SnippetSymbol::Global(sym.get_id())),
            };
            if let Some(sym) = found {
                let token = match self.symbol_ref(sym).get_type() {
                    SymbolType::Space => Some(SPACESYM),
                    SymbolType::Userop => Some(USEROPSYM),
                    SymbolType::Varnode => Some(VARSYM),
                    SymbolType::Operand => Some(OPERANDSYM),
                    SymbolType::Start
                    | SymbolType::End
                    | SymbolType::Next2
                    | SymbolType::Flowdest
                    | SymbolType::Flowref => Some(JUMPSYM),
                    SymbolType::Label => Some(LABELSYM),
                    _ => None,
                };
                if let Some(token) = token {
                    return (token, SemValue::Symbol(sym));
                }
            }
            return (STRING, SemValue::Text(name));
        }
        if tok == INTEGER {
            return (INTEGER, SemValue::Integer(self.lexer.get_number()));
        }
        (tok, SemValue::Empty)
    }

    fn yyerror(&mut self, msg: &str) {
        self.report_error(None, msg);
    }

    fn reject(&mut self, msg: &str) -> ActionResult {
        self.yyerror(msg);
        Err(ActionFailure::Rejected)
    }

    fn reduce(&mut self, rule: usize, mut args: Vec<SemValue>) -> ActionResult {
        let mut take = |index: usize| std::mem::take(&mut args[index - 1]);
        if let Some((opc, swapped)) = binary_opcode(rule) {
            let first = take(1).tree();
            let second = take(3).tree();
            let res = if swapped {
                self.create_op(opc, second, first)
            } else {
                self.create_op(opc, first, second)
            };
            return Ok(SemValue::Tree(res));
        }
        if let Some(opc) = prefix_unary_opcode(rule) {
            let vn = take(2).tree();
            return Ok(SemValue::Tree(self.create_op_unary(opc, vn)));
        }
        if let Some(opc) = function_unary_opcode(rule) {
            let vn = take(3).tree();
            return Ok(SemValue::Tree(self.create_op_unary(opc, vn)));
        }
        if let Some(opc) = function_binary_opcode(rule) {
            let first = take(3).tree();
            let second = take(5).tree();
            return Ok(SemValue::Tree(self.create_op(opc, first, second)));
        }
        let const_space = self.get_constant_space();
        match rule {
            2 => {
                let sem = take(1).sem();
                self.set_result(sem);
                Ok(SemValue::Empty)
            }
            3 => Ok(SemValue::Sem(ConstructTpl::new())),
            4 => {
                let mut sem = take(1).sem();
                let stmt = take(2).stmt();
                if !sem.add_op_list(stmt) {
                    return self.reject("Multiple delayslot declarations");
                }
                Ok(SemValue::Sem(sem))
            }
            5 => {
                let sem = take(1).sem();
                let name = take(3).text();
                self.new_local_definition(&name, 0);
                Ok(SemValue::Sem(sem))
            }
            6 => {
                let sem = take(1).sem();
                let name = take(3).text();
                let size = take(5).integer() as u32;
                self.new_local_definition(&name, size);
                Ok(SemValue::Sem(sem))
            }
            7 => {
                let vn = take(1).varnode();
                let mut tree = take(3).tree();
                tree.set_output(vn)?;
                Ok(SemValue::Stmt(ExprTree::to_vector(tree)))
            }
            8 => {
                let name = take(2).text();
                let tree = take(4).tree();
                Ok(SemValue::Stmt(self.new_output(true, tree, &name, 0)?))
            }
            9 => {
                let name = take(1).text();
                let tree = take(3).tree();
                Ok(SemValue::Stmt(self.new_output(false, tree, &name, 0)?))
            }
            10 => {
                let name = take(2).text();
                let size = take(4).integer() as u32;
                let tree = take(6).tree();
                Ok(SemValue::Stmt(self.new_output(true, tree, &name, size)?))
            }
            11 => {
                let name = take(1).text();
                let size = take(3).integer() as u32;
                let tree = take(5).tree();
                Ok(SemValue::Stmt(self.new_output(true, tree, &name, size)?))
            }
            12 => {
                let sym = take(2).symbol();
                let msg = format!("Redefinition of symbol: {}", self.symbol_ref(sym).get_name());
                self.reject(&msg)
            }
            13 => {
                let qual = take(1).star();
                let ptr = take(2).tree();
                let val = take(4).tree();
                Ok(SemValue::Stmt(self.create_store(qual, ptr, val)?))
            }
            14 => {
                let index = self.userop_index(take(1).symbol());
                let param = take(3).param();
                Ok(SemValue::Stmt(self.create_user_op_no_out(index, param)))
            }
            15 => {
                let vn = take(1).varnode();
                let bitoffset = take(3).integer() as u32;
                let numbits = take(5).integer() as u32;
                let tree = take(8).tree();
                Ok(SemValue::Stmt(self.assign_bit_range(vn, bitoffset, numbits, tree)?))
            }
            16 => self.reject("Illegal truncation on left-hand side of assignment"),
            17 => self.reject("Illegal subpiece on left-hand side of assignment"),
            18 | 21 => {
                let opc = if rule == 18 { OpCode::Branch } else { OpCode::Call };
                let dest = take(2).varnode();
                Ok(SemValue::Stmt(self.create_op_no_out(opc, ExprTree::from_varnode(dest))))
            }
            19 => {
                let cond = take(2).tree();
                let dest = take(4).varnode();
                Ok(SemValue::Stmt(self.create_op_no_out2(
                    OpCode::Cbranch,
                    ExprTree::from_varnode(dest),
                    cond,
                )))
            }
            20 | 22 | 24 => {
                let opc = match rule {
                    20 => OpCode::Branchind,
                    22 => OpCode::Callind,
                    _ => OpCode::Return,
                };
                let tree = take(3).tree();
                Ok(SemValue::Stmt(self.create_op_no_out(opc, tree)))
            }
            23 => self.reject("Must specify an indirect parameter for return"),
            25 => {
                let label = self.local_handle(take(1).symbol());
                Ok(SemValue::Stmt(self.place_label(label)))
            }
            26 => Ok(SemValue::Tree(ExprTree::from_varnode(take(1).varnode()))),
            27 => {
                let qual = take(1).star();
                let ptr = take(2).tree();
                Ok(SemValue::Tree(self.create_load(qual, ptr)?))
            }
            28 => Ok(SemValue::Tree(take(2).tree())),
            85 => {
                let vn = self.symbol_varnode(take(1).symbol());
                let piece = take(3).varnode();
                Ok(SemValue::Tree(self.create_op(
                    OpCode::Subpiece,
                    ExprTree::from_varnode(vn),
                    ExprTree::from_varnode(piece),
                )))
            }
            86 => {
                let sym = take(1).symbol();
                let numbits = take(3).integer().wrapping_mul(8) as u32;
                Ok(SemValue::Tree(self.bit_range(sym, 0, numbits)?))
            }
            87 => {
                let sym = take(1).symbol();
                let bitoffset = take(3).integer() as u32;
                let numbits = take(5).integer() as u32;
                Ok(SemValue::Tree(self.bit_range(sym, bitoffset, numbits)?))
            }
            88 => {
                let index = self.userop_index(take(1).symbol());
                let param = take(3).param();
                Ok(SemValue::Tree(self.create_user_op(index, param)))
            }
            89 | 90 => {
                let spc = self.symbol_ref(take(3).symbol()).get_space().cloned();
                let size = if rule == 89 { take(6).integer() as u32 } else { 0 };
                Ok(SemValue::Star(StarQuality {
                    id: space_const_opt(spc),
                    size,
                }))
            }
            91 | 92 => {
                let size = if rule == 91 { take(3).integer() as u32 } else { 0 };
                Ok(SemValue::Star(StarQuality {
                    id: space_const_opt(self.get_default_space()),
                    size,
                }))
            }
            93 => {
                let sym = self.symbol_varnode(take(1).symbol());
                Ok(SemValue::Varnode(VarnodeTpl::new(
                    ConstTpl::new_type(ConstType::JCurspace),
                    sym.get_offset().clone(),
                    ConstTpl::new_type(ConstType::JCurspaceSize),
                )))
            }
            94 => {
                let val = take(1).integer();
                Ok(SemValue::Varnode(VarnodeTpl::new(
                    ConstTpl::new_type(ConstType::JCurspace),
                    real(val),
                    ConstTpl::new_type(ConstType::JCurspaceSize),
                )))
            }
            95 => {
                let res = VarnodeTpl::new(
                    ConstTpl::new_type(ConstType::JCurspace),
                    real(0),
                    ConstTpl::new_type(ConstType::JCurspaceSize),
                );
                self.yyerror("Parsed integer is too big (overflow)");
                Ok(SemValue::Varnode(res))
            }
            96 => {
                let val = take(1).integer();
                let spc = self.symbol_ref(take(3).symbol()).get_space().cloned();
                let size = spc.as_ref().map(|spc| spc.get_addr_size()).unwrap_or(0);
                Ok(SemValue::Varnode(VarnodeTpl::new(
                    space_const_opt(spc),
                    real(val),
                    real(size as u64),
                )))
            }
            97 => {
                let label = self.local_handle(take(1).symbol());
                let index = match &self.symbol_mut(label).body {
                    SymbolBody::Label { index, .. } => *index,
                    _ => 0,
                };
                let res = VarnodeTpl::new(
                    space_const_opt(const_space),
                    ConstTpl::new_value(ConstType::JRelative, index as u64),
                    real(4),
                );
                if let SymbolBody::Label { refcount, .. } = &mut self.symbol_mut(label).body {
                    *refcount += 1;
                }
                Ok(SemValue::Varnode(res))
            }
            98 => {
                let name = take(1).text();
                self.reject(&format!("Unknown jump destination: {name}"))
            }
            99 | 107 => Ok(SemValue::Varnode(self.symbol_varnode(take(1).symbol()))),
            100 => Ok(SemValue::Varnode(take(1).varnode())),
            101 => {
                let name = take(1).text();
                self.reject(&format!("Unknown varnode parameter: {name}"))
            }
            102 => {
                let val = take(1).integer();
                Ok(SemValue::Varnode(VarnodeTpl::new(
                    space_const_opt(const_space),
                    real(val),
                    real(0),
                )))
            }
            103 => {
                let res = VarnodeTpl::new(space_const_opt(const_space), real(0), real(0));
                self.yyerror("Parsed integer is too big (overflow)");
                Ok(SemValue::Varnode(res))
            }
            104 => {
                let val = take(1).integer();
                let size = take(3).integer();
                Ok(SemValue::Varnode(VarnodeTpl::new(
                    space_const_opt(const_space),
                    real(val),
                    real(size),
                )))
            }
            105 => {
                let vn = take(2).varnode();
                Ok(SemValue::Varnode(self.address_of(vn, 0)))
            }
            106 => {
                let size = take(3).integer() as u32;
                let vn = take(4).varnode();
                Ok(SemValue::Varnode(self.address_of(vn, size)))
            }
            108 => {
                let name = take(1).text();
                self.reject(&format!("Unknown assignment varnode: {name}"))
            }
            109 => Ok(take(2)),
            110 => {
                let name = take(2).text();
                let label = self.define_label(&name);
                Ok(SemValue::Symbol(SnippetSymbol::Local(label)))
            }
            111..=113 => Ok(take(1)),
            114 => Ok(SemValue::Param(Vec::new())),
            115 => Ok(SemValue::Param(vec![take(1).tree()])),
            116 => {
                let mut param = take(1).param();
                param.push(take(3).tree());
                Ok(SemValue::Param(param))
            }
            _ => Ok(SemValue::Empty),
        }
    }

    fn userop_index(&self, sym: SnippetSymbol) -> u32 {
        match &self.symbol_ref(sym).body {
            SymbolBody::Userop { index } => *index,
            _ => 0,
        }
    }

    fn local_handle(&self, sym: SnippetSymbol) -> SymbolHandle {
        match sym {
            SnippetSymbol::Local(handle) => handle,
            SnippetSymbol::Global(_) => usize::MAX,
        }
    }

    fn bit_range(&mut self, sym: SnippetSymbol, bitoffset: u32, numbits: u32) -> Result<ExprTree> {
        let vn = self.symbol_varnode(sym);
        let name = self.symbol_ref(sym).get_name().to_string();
        self.create_bit_range(vn, &name, None, bitoffset, numbits)
    }

    fn yyparse(&mut self) -> Result<i32> {
        let mut states: Vec<i32> = Vec::with_capacity(200);
        let mut values: Vec<SemValue> = Vec::with_capacity(200);
        let mut yystate: i32 = 0;
        let mut yyerrstatus = 0;
        let mut yychar = YYEMPTY;
        let mut yylval = SemValue::Empty;
        states.push(yystate);
        values.push(SemValue::Empty);
        enum Step {
            SetState,
            Backup,
            Default,
            Reduce(i32),
            ErrorLab,
            ErrorLab1,
        }
        let mut step = Step::SetState;
        loop {
            match step {
                Step::SetState => {
                    if states.len() >= YYMAXDEPTH {
                        self.yyerror("memory exhausted");
                        return Ok(2);
                    }
                    if yystate == YYFINAL {
                        return Ok(0);
                    }
                    step = Step::Backup;
                }
                Step::Backup => {
                    let mut yyn = YYPACT[yystate as usize] as i32;
                    if yyn == YYPACT_NINF {
                        step = Step::Default;
                        continue;
                    }
                    if yychar == YYEMPTY {
                        let (token, value) = self.lex();
                        yychar = token;
                        yylval = value;
                    }
                    let yytoken = if yychar <= YYEOF {
                        yychar = YYEOF;
                        YYEOF
                    } else {
                        yytranslate(yychar)
                    };
                    yyn += yytoken;
                    if !(0..=YYLAST).contains(&yyn) || YYCHECK[yyn as usize] as i32 != yytoken {
                        step = Step::Default;
                        continue;
                    }
                    yyn = YYTABLE[yyn as usize] as i32;
                    if yyn <= 0 {
                        if yyn == YYTABLE_NINF {
                            step = Step::ErrorLab;
                            continue;
                        }
                        step = Step::Reduce(-yyn);
                        continue;
                    }
                    if yyerrstatus > 0 {
                        yyerrstatus -= 1;
                    }
                    yystate = yyn;
                    values.push(std::mem::take(&mut yylval));
                    states.push(yystate);
                    yychar = YYEMPTY;
                    step = Step::SetState;
                }
                Step::Default => {
                    let yyn = YYDEFACT[yystate as usize] as i32;
                    if yyn == 0 {
                        step = Step::ErrorLab;
                        continue;
                    }
                    step = Step::Reduce(yyn);
                }
                Step::Reduce(rule) => {
                    let yylen = YYR2[rule as usize] as usize;
                    let args = values.split_off(values.len() - yylen);
                    states.truncate(states.len() - yylen);
                    match self.reduce(rule as usize, args) {
                        Err(ActionFailure::Thrown(err)) => return Err(err),
                        Err(ActionFailure::Rejected) => {
                            yystate = *states.last().unwrap_or(&0);
                            step = Step::ErrorLab1;
                            continue;
                        }
                        Ok(value) => values.push(value),
                    }
                    let top = *states.last().unwrap_or(&0);
                    let yylhs = YYR1[rule as usize] as i32 - YYNTOKENS;
                    let yyi = YYPGOTO[yylhs as usize] as i32 + top;
                    yystate = if (0..=YYLAST).contains(&yyi) && YYCHECK[yyi as usize] as i32 == top {
                        YYTABLE[yyi as usize] as i32
                    } else {
                        YYDEFGOTO[yylhs as usize] as i32
                    };
                    states.push(yystate);
                    step = Step::SetState;
                }
                Step::ErrorLab => {
                    if yyerrstatus == 0 {
                        self.yyerror("syntax error");
                    }
                    if yyerrstatus == 3 {
                        if yychar <= YYEOF {
                            if yychar == YYEOF {
                                return Ok(1);
                            }
                        } else {
                            yychar = YYEMPTY;
                        }
                    }
                    step = Step::ErrorLab1;
                }
                Step::ErrorLab1 => {
                    yyerrstatus = 3;
                    let shift_state = loop {
                        let mut yyn = YYPACT[yystate as usize] as i32;
                        if yyn != YYPACT_NINF {
                            yyn += YYTERROR;
                            if (0..=YYLAST).contains(&yyn) && YYCHECK[yyn as usize] as i32 == YYTERROR {
                                yyn = YYTABLE[yyn as usize] as i32;
                                if 0 < yyn {
                                    break Some(yyn);
                                }
                            }
                        }
                        if states.len() <= 1 {
                            return Ok(1);
                        }
                        states.pop();
                        values.pop();
                        yystate = *states.last().unwrap_or(&0);
                    };
                    if let Some(next) = shift_state {
                        values.push(std::mem::take(&mut yylval));
                        yystate = next;
                        states.push(yystate);
                    }
                    step = Step::SetState;
                }
            }
        }
    }

    pub fn parse_stream(&mut self, input: &[u8]) -> Result<bool> {
        self.lexer.initialize(input);
        let res = self.yyparse()?;
        if res != 0 {
            self.report_error(None, "Syntax error");
            return Ok(false);
        }
        let mut result = self.result.take().unwrap_or_default();
        let resolved = propagate_size(&mut result);
        self.result = Some(result);
        if !resolved? {
            self.report_error(None, "Could not resolve at least 1 variable size");
            return Ok(false);
        }
        Ok(true)
    }
}

fn space_const_opt(spc: Option<crate::space::SpaceRef>) -> ConstTpl {
    match spc {
        Some(spc) => ConstTpl::new_space(spc),
        None => ConstTpl::new_type(ConstType::Spaceid),
    }
}

impl PcodeCompile for PcodeSnippet<'_> {
    fn compile_state(&self) -> &PcodeCompileState {
        &self.state
    }

    fn compile_state_mut(&mut self) -> &mut PcodeCompileState {
        &mut self.state
    }

    fn allocate_temp(&mut self) -> u32 {
        let res = self.tempbase;
        self.tempbase = self.tempbase.wrapping_add(16);
        res
    }

    fn add_symbol(&mut self, sym: SleighSymbol) -> SymbolHandle {
        let name = sym.get_name().to_string();
        self.locals.push(sym);
        let handle = self.locals.len() - 1;
        match self.tree.entry(name) {
            std::collections::btree_map::Entry::Occupied(entry) => {
                let message = format!("Duplicate symbol name: {}", entry.key());
                self.report_error(None, &message);
            }
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(handle);
            }
        }
        handle
    }

    fn symbol_mut(&mut self, handle: SymbolHandle) -> &mut SleighSymbol {
        if handle >= self.locals.len() {
            self.locals.push(SleighSymbol::new("", SymbolBody::Dummy));
            let last = self.locals.len() - 1;
            return &mut self.locals[last];
        }
        &mut self.locals[handle]
    }

    fn get_location(&self, _handle: SymbolHandle) -> Option<Location> {
        None
    }

    fn report_error(&mut self, _loc: Option<&Location>, msg: &str) {
        if self.errorcount == 0 {
            self.firsterror = msg.to_string();
        }
        self.errorcount += 1;
    }

    fn report_warning(&mut self, _loc: Option<&Location>, _msg: &str) {}
}
