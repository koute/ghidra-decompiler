use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::context::{ConstructorRef, FixedHandle, ParserWalker, ParserWalkerChange, Token};
use crate::error::{Error, Result};
use crate::marshal::Decoder;
use crate::pcoderaw::VarnodeData;
use crate::semantics::{ConstTpl, ConstType, ConstructTpl, VarnodeTpl};
use crate::slaformat::*;
use crate::slghpatexpress::{
    CONSTANT_ZERO, END_INSTRUCTION_VALUE, NEXT2_INSTRUCTION_VALUE, PatternExpression, START_INSTRUCTION_VALUE,
};
use crate::slghpattern::DisjointPattern;
use crate::space::{SpaceRef, SpaceType};

pub type SymbolId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SymbolType {
    Space,
    Token,
    Userop,
    Value,
    Valuemap,
    Name,
    Varnode,
    Varnodelist,
    Operand,
    Start,
    End,
    Next2,
    Subtable,
    Macro,
    Section,
    Bitrange,
    Context,
    Epsilon,
    Label,
    Flowdest,
    Flowref,
    Dummy,
}

#[derive(Clone, Debug, Default)]
pub struct OperandSymbol {
    pub reloffset: u32,
    pub offsetbase: i32,
    pub minimumlength: i32,
    pub hand: i32,
    pub localexp: Option<PatternExpression>,
    pub triple: Option<SymbolId>,
    pub defexp: Option<PatternExpression>,
    pub flags: u32,
}

impl OperandSymbol {
    pub const CODE_ADDRESS: u32 = 1;
    pub const OFFSET_IRREL: u32 = 2;
    pub const VARIABLE_LEN: u32 = 4;
    pub const MARKED: u32 = 8;

    pub fn new(index: i32, ct: ConstructorRef) -> OperandSymbol {
        OperandSymbol {
            reloffset: 0,
            offsetbase: 0,
            minimumlength: 0,
            hand: index,
            localexp: Some(PatternExpression::Operand { index, ct }),
            triple: None,
            defexp: None,
            flags: 0,
        }
    }

    pub fn get_relative_offset(&self) -> u32 {
        self.reloffset
    }

    pub fn get_offset_base(&self) -> i32 {
        self.offsetbase
    }

    pub fn get_minimum_length(&self) -> i32 {
        self.minimumlength
    }

    pub fn get_defining_expression(&self) -> Option<&PatternExpression> {
        self.defexp.as_ref()
    }

    pub fn get_defining_symbol(&self) -> Option<SymbolId> {
        self.triple
    }

    pub fn get_index(&self) -> i32 {
        self.hand
    }

    pub fn define_operand_expression(&mut self, pe: PatternExpression) -> Result<()> {
        if self.defexp.is_some() || self.triple.is_some() {
            return Err(Error::Sleigh("Redefining operand".to_string()));
        }
        self.defexp = Some(pe);
        Ok(())
    }

    pub fn define_operand_symbol(&mut self, tri: SymbolId) -> Result<()> {
        if self.defexp.is_some() || self.triple.is_some() {
            return Err(Error::Sleigh("Redefining operand".to_string()));
        }
        self.triple = Some(tri);
        Ok(())
    }

    pub fn set_code_address(&mut self) {
        self.flags |= OperandSymbol::CODE_ADDRESS;
    }

    pub fn is_code_address(&self) -> bool {
        (self.flags & OperandSymbol::CODE_ADDRESS) != 0
    }

    pub fn set_offset_irrelevant(&mut self) {
        self.flags |= OperandSymbol::OFFSET_IRREL;
    }

    pub fn is_offset_irrelevant(&self) -> bool {
        (self.flags & OperandSymbol::OFFSET_IRREL) != 0
    }
}

#[derive(Clone, Debug)]
pub enum ContextChange {
    Op {
        patexp: PatternExpression,
        num: i32,
        mask: u32,
        shift: i32,
    },
    Commit {
        sym: SymbolId,
        num: i32,
        mask: u32,
        flow: bool,
    },
}

pub fn calc_maskword(sbit: i32, ebit: i32) -> Result<(i32, i32, u32)> {
    let num = sbit / 32;
    if num != ebit / 32 {
        return Err(Error::Sleigh(
            "Context field not contained within one machine int".to_string(),
        ));
    }
    let sbit = sbit - num * 32;
    let ebit = ebit - num * 32;
    let shift = 32 - ebit - 1;
    let mut mask = (!0u32).wrapping_shr((sbit + shift) as u32);
    mask = mask.wrapping_shl(shift as u32);
    Ok((num, shift, mask))
}

impl ContextChange {
    pub fn new_op(startbit: i32, endbit: i32, patexp: PatternExpression) -> Result<ContextChange> {
        let (num, shift, mask) = calc_maskword(startbit, endbit)?;
        Ok(ContextChange::Op {
            patexp,
            num,
            mask,
            shift,
        })
    }

    pub fn new_commit(sym: SymbolId, sbit: i32, ebit: i32, flow: bool) -> Result<ContextChange> {
        let (num, _shift, mask) = calc_maskword(sbit, ebit)?;
        Ok(ContextChange::Commit { sym, num, mask, flow })
    }

    pub fn apply(&self, walker: &mut ParserWalkerChange<'_>) -> Result<()> {
        match self {
            ContextChange::Op {
                patexp,
                num,
                mask,
                shift,
            } => {
                let mut val = patexp.get_value(&walker.view())? as u32;
                val = val.wrapping_shl(*shift as u32);
                walker.get_parser_context().set_context_word(*num, val, *mask);
            }
            ContextChange::Commit { sym, num, mask, flow } => {
                let point = walker.get_point();
                walker.get_parser_context().add_commit(*sym, *num, *mask, *flow, point);
            }
        }
        Ok(())
    }

    fn decode(decoder: &mut dyn Decoder, symtab: &SymbolTable) -> Result<ContextChange> {
        let subel = decoder.peek_element()?;
        if subel == ELEM_CONTEXT_OP {
            let el = decoder.open_element_expect(ELEM_CONTEXT_OP)?;
            let num = decoder.read_signed_integer_attr(ATTRIB_I)? as i32;
            let shift = decoder.read_signed_integer_attr(ATTRIB_SHIFT)? as i32;
            let mask = decoder.read_unsigned_integer_attr(ATTRIB_MASK)? as u32;
            let patexp = PatternExpression::decode_expression(decoder, symtab)?;
            decoder.close_element(el)?;
            return Ok(ContextChange::Op {
                patexp,
                num,
                mask,
                shift,
            });
        }
        let el = decoder.open_element_expect(ELEM_COMMIT)?;
        let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)? as u32;
        symtab.find_symbol_by_id(id)?;
        let num = decoder.read_signed_integer_attr(ATTRIB_NUMBER)? as i32;
        let mask = decoder.read_unsigned_integer_attr(ATTRIB_MASK)? as u32;
        let flow = decoder.read_bool_attr(ATTRIB_FLOW)?;
        decoder.close_element(el)?;
        Ok(ContextChange::Commit {
            sym: id,
            num,
            mask,
            flow,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrintPiece {
    Text(String),
    Operand(i32),
}

fn operand_piece_index(index: i32) -> i32 {
    ((65 + index) as u8 as i8 as i32) - 65
}

#[derive(Clone, Debug)]
pub struct Constructor {
    parent: SymbolId,
    operands: Vec<SymbolId>,
    printpiece: Vec<PrintPiece>,
    context: Vec<ContextChange>,
    templ: Option<ConstructTpl>,
    namedtempl: Vec<Option<ConstructTpl>>,
    minimumlength: i32,
    id: u32,
    firstwhitespace: i32,
    flowthruindex: i32,
    lineno: i32,
    src_index: i32,
}

static EMPTY_CONSTRUCTOR: Constructor = Constructor::empty();

impl Default for Constructor {
    fn default() -> Constructor {
        Constructor::empty()
    }
}

impl Constructor {
    pub const fn empty() -> Constructor {
        Constructor {
            parent: 0,
            operands: Vec::new(),
            printpiece: Vec::new(),
            context: Vec::new(),
            templ: None,
            namedtempl: Vec::new(),
            minimumlength: 0,
            id: 0,
            firstwhitespace: -1,
            flowthruindex: -1,
            lineno: 0,
            src_index: 0,
        }
    }

    pub fn empty_static() -> &'static Constructor {
        &EMPTY_CONSTRUCTOR
    }

    pub fn new(parent: SymbolId) -> Constructor {
        let mut res = Constructor::empty();
        res.parent = parent;
        res
    }

    pub fn get_parent(&self) -> SymbolId {
        self.parent
    }

    pub fn get_minimum_length(&self) -> i32 {
        self.minimumlength
    }

    pub fn set_minimum_length(&mut self, len: i32) {
        self.minimumlength = len;
    }

    pub fn get_id(&self) -> u32 {
        self.id
    }

    pub fn set_id(&mut self, id: u32) {
        self.id = id;
    }

    pub fn get_lineno(&self) -> i32 {
        self.lineno
    }

    pub fn get_src_index(&self) -> i32 {
        self.src_index
    }

    pub fn get_num_operands(&self) -> i32 {
        self.operands.len() as i32
    }

    pub fn get_operand(&self, index: i32) -> Option<SymbolId> {
        if index < 0 {
            return None;
        }
        self.operands.get(index as usize).copied()
    }

    pub fn get_operands(&self) -> &[SymbolId] {
        &self.operands
    }

    pub fn get_templ(&self) -> Option<&ConstructTpl> {
        self.templ.as_ref()
    }

    pub fn get_named_templ(&self, secnum: i32) -> Option<&ConstructTpl> {
        if secnum < 0 {
            return None;
        }
        self.namedtempl.get(secnum as usize).and_then(|templ| templ.as_ref())
    }

    pub fn get_num_sections(&self) -> i32 {
        self.namedtempl.len() as i32
    }

    pub fn get_print_pieces(&self) -> &[PrintPiece] {
        &self.printpiece
    }

    pub fn get_context_changes(&self) -> &[ContextChange] {
        &self.context
    }

    pub fn apply_context(&self, walker: &mut ParserWalkerChange<'_>) -> Result<()> {
        for change in self.context.iter() {
            change.apply(walker)?;
        }
        Ok(())
    }

    fn print_piece(&self, piece: &PrintPiece, out: &mut String, walker: &mut ParserWalker<'_>) -> Result<()> {
        match piece {
            PrintPiece::Text(text) => out.push_str(text),
            PrintPiece::Operand(index) => {
                if let Some(symid) = self.get_operand(*index) {
                    walker.symtab().get(symid).print(out, walker)?;
                }
            }
        }
        Ok(())
    }

    pub fn print(&self, out: &mut String, walker: &mut ParserWalker<'_>) -> Result<()> {
        for piece in self.printpiece.iter() {
            self.print_piece(piece, out, walker)?;
        }
        Ok(())
    }

    fn flowthru_subtable(&self, walker: &ParserWalker<'_>) -> bool {
        if self.flowthruindex == -1 {
            return false;
        }
        let Some(symid) = self.get_operand(self.flowthruindex) else {
            return false;
        };
        let Some(oper) = walker.symtab().get(symid).operand() else {
            return false;
        };
        match oper.get_defining_symbol() {
            Some(triple) => walker.symtab().get(triple).get_type() == SymbolType::Subtable,
            None => false,
        }
    }

    pub fn print_mnemonic(&self, out: &mut String, walker: &mut ParserWalker<'_>) -> Result<()> {
        if self.flowthru_subtable(walker) {
            walker.push_operand(self.flowthruindex)?;
            if let Some(ct) = walker.get_constructor() {
                ct.print_mnemonic(out, walker)?;
            }
            walker.pop_operand();
            return Ok(());
        }
        let endind = if self.firstwhitespace == -1 {
            self.printpiece.len()
        } else {
            (self.firstwhitespace.max(0) as usize).min(self.printpiece.len())
        };
        for piece in self.printpiece[..endind].iter() {
            self.print_piece(piece, out, walker)?;
        }
        Ok(())
    }

    pub fn print_body(&self, out: &mut String, walker: &mut ParserWalker<'_>) -> Result<()> {
        if self.flowthru_subtable(walker) {
            walker.push_operand(self.flowthruindex)?;
            if let Some(ct) = walker.get_constructor() {
                ct.print_body(out, walker)?;
            }
            walker.pop_operand();
            return Ok(());
        }
        if self.firstwhitespace == -1 {
            return Ok(());
        }
        let start = (self.firstwhitespace as usize + 1).min(self.printpiece.len());
        for piece in self.printpiece[start..].iter() {
            self.print_piece(piece, out, walker)?;
        }
        Ok(())
    }

    pub fn add_operand(&mut self, sym: SymbolId) {
        let index = self.operands.len() as i32;
        self.operands.push(sym);
        self.printpiece.push(PrintPiece::Operand(operand_piece_index(index)));
    }

    pub fn add_invisible_operand(&mut self, sym: SymbolId) {
        self.operands.push(sym);
    }

    pub fn set_main_section(&mut self, tpl: ConstructTpl) {
        self.templ = Some(tpl);
    }

    pub fn set_named_section(&mut self, tpl: ConstructTpl, id: i32) {
        while self.namedtempl.len() as i32 <= id {
            self.namedtempl.push(None);
        }
        self.namedtempl[id as usize] = Some(tpl);
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, symtab: &SymbolTable) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_CONSTRUCTOR)?;
        let id = decoder.read_unsigned_integer_attr(ATTRIB_PARENT)? as u32;
        symtab.find_symbol_by_id(id)?;
        self.parent = id;
        self.firstwhitespace = decoder.read_signed_integer_attr(ATTRIB_FIRST)? as i32;
        self.minimumlength = decoder.read_signed_integer_attr(ATTRIB_LENGTH)? as i32;
        self.src_index = decoder.read_signed_integer_attr(ATTRIB_SOURCE)? as i32;
        self.lineno = decoder.read_signed_integer_attr(ATTRIB_LINE)? as i32;
        let mut subel = decoder.peek_element()?;
        while subel != 0 {
            if subel == ELEM_OPER {
                decoder.open_element()?;
                let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)? as u32;
                symtab.find_symbol_by_id(id)?;
                self.operands.push(id);
                decoder.close_element(subel)?;
            } else if subel == ELEM_PRINT {
                decoder.open_element()?;
                let piece = decoder.read_string_attr(ATTRIB_PIECE)?;
                let bytes = piece.as_bytes();
                if !bytes.is_empty() && bytes[0] == b'\n' {
                    let second = bytes.get(1).copied().unwrap_or(0) as i8 as i32;
                    self.printpiece.push(PrintPiece::Operand(second - 65));
                } else {
                    self.printpiece.push(PrintPiece::Text(piece));
                }
                decoder.close_element(subel)?;
            } else if subel == ELEM_OPPRINT {
                decoder.open_element()?;
                let index = decoder.read_signed_integer_attr(ATTRIB_ID)? as i32;
                self.printpiece.push(PrintPiece::Operand(operand_piece_index(index)));
                decoder.close_element(subel)?;
            } else if subel == ELEM_CONTEXT_OP || subel == ELEM_COMMIT {
                let change = ContextChange::decode(decoder, symtab)?;
                self.context.push(change);
            } else {
                let mut cur = ConstructTpl::new();
                let sectionid = cur.decode(decoder)?;
                if sectionid < 0 {
                    if self.templ.is_some() {
                        return Err(Error::Lowlevel("Duplicate main section".to_string()));
                    }
                    self.templ = Some(cur);
                } else {
                    while self.namedtempl.len() as i32 <= sectionid {
                        self.namedtempl.push(None);
                    }
                    if self.namedtempl[sectionid as usize].is_some() {
                        return Err(Error::Lowlevel("Duplicate named section".to_string()));
                    }
                    self.namedtempl[sectionid as usize] = Some(cur);
                }
            }
            subel = decoder.peek_element()?;
        }
        if self.printpiece.len() == 1
            && let PrintPiece::Operand(index) = self.printpiece[0]
        {
            self.flowthruindex = index;
        } else {
            self.flowthruindex = -1;
        }
        decoder.close_element(el)
    }
}

#[derive(Clone, Debug, Default)]
pub struct DecisionNode {
    list: Vec<(DisjointPattern, u32)>,
    children: Vec<DecisionNode>,
    num: i32,
    contextdecision: bool,
    startbit: i32,
    bitsize: i32,
}

impl DecisionNode {
    pub fn resolve(&self, walker: &ParserWalker<'_>, table: SymbolId) -> Result<ConstructorRef> {
        let mut node = self;
        loop {
            if node.bitsize == 0 {
                for (pat, ct) in node.list.iter() {
                    if pat.is_match(walker)? {
                        return Ok(ConstructorRef { table, index: *ct });
                    }
                }
                let addr = walker.get_addr();
                let mut message = String::new();
                message.push(addr.get_shortcut());
                addr.print_raw(&mut message);
                message.push_str(": Unable to resolve constructor");
                return Err(Error::BadData(message));
            }
            let val = if node.contextdecision {
                walker.get_context_bits(node.startbit, node.bitsize)
            } else {
                walker.get_instruction_bits(node.startbit, node.bitsize)?
            };
            match node.children.get(val as usize) {
                Some(child) => node = child,
                None => {
                    return Err(Error::Lowlevel(
                        "decision tree has no child for field value".to_string(),
                    ));
                }
            }
        }
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, numct: usize) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_DECISION)?;
        self.num = decoder.read_signed_integer_attr(ATTRIB_NUMBER)? as i32;
        self.contextdecision = decoder.read_bool_attr(ATTRIB_CONTEXT)?;
        self.startbit = decoder.read_signed_integer_attr(ATTRIB_STARTBIT)? as i32;
        self.bitsize = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as i32;
        let mut subel = decoder.peek_element()?;
        while subel != 0 {
            if subel == ELEM_PAIR {
                decoder.open_element()?;
                let id = decoder.read_signed_integer_attr(ATTRIB_ID)? as u32;
                if id as usize >= numct {
                    return Err(Error::Decoder("Invalid constructor id".to_string()));
                }
                let pat = DisjointPattern::decode_disjoint(decoder)?;
                self.list.push((pat, id));
                decoder.close_element(subel)?;
            } else if subel == ELEM_DECISION {
                let mut subnode = DecisionNode::default();
                subnode.decode(decoder, numct)?;
                self.children.push(subnode);
            } else {
                return Err(Error::Decoder("unexpected element in decision node".to_string()));
            }
            subel = decoder.peek_element()?;
        }
        decoder.close_element(el)
    }
}

#[derive(Clone, Debug, Default)]
pub struct SubtableSymbol {
    pub construct: Vec<Constructor>,
    pub decisiontree: Option<DecisionNode>,
    pub beingbuilt: bool,
    pub errors: bool,
}

#[derive(Clone, Debug)]
pub enum SymbolBody {
    Dummy,
    Space {
        space: SpaceRef,
    },
    Token {
        token: Token,
    },
    Userop {
        index: u32,
    },
    Epsilon {
        const_space: Option<SpaceRef>,
    },
    Value {
        patval: Option<PatternExpression>,
    },
    Valuemap {
        patval: Option<PatternExpression>,
        valuetable: Vec<i64>,
        tableisfilled: bool,
    },
    Name {
        patval: Option<PatternExpression>,
        nametable: Vec<String>,
        tableisfilled: bool,
    },
    Varnode {
        fix: VarnodeData,
        context_bits: bool,
    },
    Bitrange {
        varsym: SymbolId,
        bitoffset: u32,
        numbits: u32,
    },
    Context {
        patval: Option<PatternExpression>,
        vn: SymbolId,
        low: u32,
        high: u32,
        flow: bool,
    },
    Varnodelist {
        patval: Option<PatternExpression>,
        varnode_table: Vec<Option<SymbolId>>,
        tableisfilled: bool,
    },
    Operand(Box<OperandSymbol>),
    Start {
        const_space: Option<SpaceRef>,
    },
    End {
        const_space: Option<SpaceRef>,
    },
    Next2 {
        const_space: Option<SpaceRef>,
    },
    Flowdest {
        const_space: Option<SpaceRef>,
    },
    Flowref {
        const_space: Option<SpaceRef>,
    },
    Subtable(Box<SubtableSymbol>),
    Macro {
        index: i32,
        construct: Option<ConstructTpl>,
        operands: Vec<SymbolId>,
    },
    Section {
        templateid: i32,
        define_count: i32,
        ref_count: i32,
    },
    Label {
        index: u32,
        isplaced: bool,
        refcount: u32,
    },
}

#[derive(Clone, Debug)]
pub struct SleighSymbol {
    name: String,
    id: SymbolId,
    scopeid: u32,
    pub body: SymbolBody,
}

static DUMMY_SYMBOL: SleighSymbol = SleighSymbol {
    name: String::new(),
    id: 0,
    scopeid: 0,
    body: SymbolBody::Dummy,
};

fn write_signed_hex(out: &mut String, val: i64) {
    if val >= 0 {
        let _ = write!(out, "0x{val:x}");
    } else {
        let _ = write!(out, "-0x{:x}", val.wrapping_neg() as u64);
    }
}

fn write_address_hex(out: &mut String, val: u64) {
    let _ = write!(out, "0x{val:x}");
}

fn check_table_fill(patval: &Option<PatternExpression>, size: usize) -> bool {
    let Some(patval) = patval else {
        return false;
    };
    let min = patval.min_value().unwrap_or(0);
    let max = patval.max_value().unwrap_or(0);
    min >= 0 && (max as u64) < size as u64
}

impl SleighSymbol {
    pub fn new(name: &str, body: SymbolBody) -> SleighSymbol {
        SleighSymbol {
            name: name.to_string(),
            id: 0,
            scopeid: 0,
            body,
        }
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_id(&self) -> SymbolId {
        self.id
    }

    pub fn get_scope_id(&self) -> u32 {
        self.scopeid
    }

    pub fn get_type(&self) -> SymbolType {
        match &self.body {
            SymbolBody::Dummy => SymbolType::Dummy,
            SymbolBody::Space { .. } => SymbolType::Space,
            SymbolBody::Token { .. } => SymbolType::Token,
            SymbolBody::Userop { .. } => SymbolType::Userop,
            SymbolBody::Epsilon { .. } => SymbolType::Epsilon,
            SymbolBody::Value { .. } => SymbolType::Value,
            SymbolBody::Valuemap { .. } => SymbolType::Valuemap,
            SymbolBody::Name { .. } => SymbolType::Name,
            SymbolBody::Varnode { .. } => SymbolType::Varnode,
            SymbolBody::Bitrange { .. } => SymbolType::Bitrange,
            SymbolBody::Context { .. } => SymbolType::Context,
            SymbolBody::Varnodelist { .. } => SymbolType::Varnodelist,
            SymbolBody::Operand(_) => SymbolType::Operand,
            SymbolBody::Start { .. } => SymbolType::Start,
            SymbolBody::End { .. } => SymbolType::End,
            SymbolBody::Next2 { .. } => SymbolType::Next2,
            SymbolBody::Flowdest { .. } => SymbolType::Flowdest,
            SymbolBody::Flowref { .. } => SymbolType::Flowref,
            SymbolBody::Subtable(_) => SymbolType::Subtable,
            SymbolBody::Macro { .. } => SymbolType::Macro,
            SymbolBody::Section { .. } => SymbolType::Section,
            SymbolBody::Label { .. } => SymbolType::Label,
        }
    }

    pub fn operand(&self) -> Option<&OperandSymbol> {
        match &self.body {
            SymbolBody::Operand(oper) => Some(oper),
            _ => None,
        }
    }

    pub fn operand_mut(&mut self) -> Option<&mut OperandSymbol> {
        match &mut self.body {
            SymbolBody::Operand(oper) => Some(oper),
            _ => None,
        }
    }

    pub fn subtable(&self) -> Option<&SubtableSymbol> {
        match &self.body {
            SymbolBody::Subtable(sub) => Some(sub),
            _ => None,
        }
    }

    pub fn subtable_num_constructors(&self) -> usize {
        match &self.body {
            SymbolBody::Subtable(sub) => sub.construct.len(),
            _ => 0,
        }
    }

    pub fn get_fixed_varnode(&self) -> Option<&VarnodeData> {
        match &self.body {
            SymbolBody::Varnode { fix, .. } => Some(fix),
            _ => None,
        }
    }

    pub fn get_space(&self) -> Option<&SpaceRef> {
        match &self.body {
            SymbolBody::Space { space } => Some(space),
            _ => None,
        }
    }

    pub fn get_pattern_value(&self) -> Option<&PatternExpression> {
        match &self.body {
            SymbolBody::Value { patval }
            | SymbolBody::Valuemap { patval, .. }
            | SymbolBody::Name { patval, .. }
            | SymbolBody::Context { patval, .. }
            | SymbolBody::Varnodelist { patval, .. } => patval.as_ref(),
            _ => None,
        }
    }

    pub fn is_triple(&self) -> bool {
        matches!(
            self.get_type(),
            SymbolType::Epsilon
                | SymbolType::Value
                | SymbolType::Valuemap
                | SymbolType::Name
                | SymbolType::Varnode
                | SymbolType::Context
                | SymbolType::Varnodelist
                | SymbolType::Operand
                | SymbolType::Start
                | SymbolType::End
                | SymbolType::Next2
                | SymbolType::Flowdest
                | SymbolType::Flowref
                | SymbolType::Subtable
        )
    }

    pub fn is_specific(&self) -> bool {
        matches!(
            self.get_type(),
            SymbolType::Epsilon
                | SymbolType::Varnode
                | SymbolType::Operand
                | SymbolType::Start
                | SymbolType::End
                | SymbolType::Next2
                | SymbolType::Flowdest
                | SymbolType::Flowref
        )
    }

    pub fn resolve(&self, walker: &ParserWalker<'_>) -> Result<Option<ConstructorRef>> {
        match &self.body {
            SymbolBody::Valuemap {
                patval,
                valuetable,
                tableisfilled,
            } => {
                if !*tableisfilled {
                    let ind = match patval {
                        Some(patval) => patval.get_value(walker)?,
                        None => 0,
                    };
                    if (ind as u64) >= valuetable.len() as u64 || ind < 0 || valuetable[ind as usize] == 0xBADBEEF {
                        return Err(bad_table_entry(walker, "valuetable"));
                    }
                }
                Ok(None)
            }
            SymbolBody::Name {
                patval,
                nametable,
                tableisfilled,
            } => {
                if !*tableisfilled {
                    let ind = match patval {
                        Some(patval) => patval.get_value(walker)?,
                        None => 0,
                    };
                    if (ind as u64) >= nametable.len() as u64 || ind < 0 || nametable[ind as usize] == "\t" {
                        return Err(bad_table_entry(walker, "nametable"));
                    }
                }
                Ok(None)
            }
            SymbolBody::Varnodelist {
                patval,
                varnode_table,
                tableisfilled,
            } => {
                if !*tableisfilled {
                    let ind = match patval {
                        Some(patval) => patval.get_value(walker)?,
                        None => 0,
                    };
                    if ind < 0 || (ind as u64) >= varnode_table.len() as u64 || varnode_table[ind as usize].is_none() {
                        return Err(bad_table_entry(walker, "varnode list"));
                    }
                }
                Ok(None)
            }
            SymbolBody::Subtable(sub) => match &sub.decisiontree {
                Some(tree) => Ok(Some(tree.resolve(walker, self.id)?)),
                None => Err(Error::Lowlevel(format!("subtable {} has no decision tree", self.name))),
            },
            _ => Ok(None),
        }
    }

    pub fn get_pattern_expression(&self) -> Result<Option<&PatternExpression>> {
        match &self.body {
            SymbolBody::Epsilon { .. } | SymbolBody::Varnode { .. } => Ok(Some(&CONSTANT_ZERO)),
            SymbolBody::Value { patval }
            | SymbolBody::Valuemap { patval, .. }
            | SymbolBody::Name { patval, .. }
            | SymbolBody::Context { patval, .. }
            | SymbolBody::Varnodelist { patval, .. } => Ok(patval.as_ref()),
            SymbolBody::Operand(oper) => Ok(oper.localexp.as_ref()),
            SymbolBody::Start { .. } => Ok(Some(&START_INSTRUCTION_VALUE)),
            SymbolBody::End { .. } => Ok(Some(&END_INSTRUCTION_VALUE)),
            SymbolBody::Next2 { .. } => Ok(Some(&NEXT2_INSTRUCTION_VALUE)),
            SymbolBody::Flowdest { .. } | SymbolBody::Flowref { .. } => {
                Err(Error::Sleigh("Cannot use symbol in pattern".to_string()))
            }
            SymbolBody::Subtable(_) => Err(Error::Sleigh("Cannot use subtable in expression".to_string())),
            _ => Ok(None),
        }
    }

    pub fn get_fixed_handle(&self, hand: &mut FixedHandle, walker: &ParserWalker<'_>) -> Result<()> {
        match &self.body {
            SymbolBody::Epsilon { const_space } => {
                hand.space = const_space.clone();
                hand.offset_space = None;
                hand.offset_offset = 0;
                hand.size = 0;
            }
            SymbolBody::Value { patval } | SymbolBody::Name { patval, .. } | SymbolBody::Context { patval, .. } => {
                hand.space = walker.get_const_space().cloned();
                hand.offset_space = None;
                hand.offset_offset = match patval {
                    Some(patval) => patval.get_value(walker)? as u64,
                    None => 0,
                };
                hand.size = 0;
            }
            SymbolBody::Valuemap { patval, valuetable, .. } => {
                let ind = match patval {
                    Some(patval) => patval.get_value(walker)? as u32,
                    None => 0,
                };
                hand.space = walker.get_const_space().cloned();
                hand.offset_space = None;
                hand.offset_offset = valuetable.get(ind as usize).copied().unwrap_or(0) as u64;
                hand.size = 0;
            }
            SymbolBody::Varnode { fix, .. } => {
                hand.space = fix.space.clone();
                hand.offset_space = None;
                hand.offset_offset = fix.offset;
                hand.size = fix.size;
            }
            SymbolBody::Varnodelist {
                patval, varnode_table, ..
            } => {
                let ind = match patval {
                    Some(patval) => patval.get_value(walker)? as u32,
                    None => 0,
                };
                let entry = varnode_table.get(ind as usize).copied().flatten();
                let fix = entry
                    .and_then(|symid| walker.symtab().get(symid).get_fixed_varnode())
                    .cloned()
                    .unwrap_or_default();
                hand.space = fix.space;
                hand.offset_space = None;
                hand.offset_offset = fix.offset;
                hand.size = fix.size;
            }
            SymbolBody::Operand(oper) => {
                *hand = walker.get_fixed_handle(oper.hand).clone();
            }
            SymbolBody::Start { .. } => {
                let space = walker.get_cur_space().cloned();
                hand.offset_space = None;
                hand.offset_offset = walker.get_addr().get_offset();
                hand.size = space.as_ref().map(|spc| spc.get_addr_size()).unwrap_or(0);
                hand.space = space;
            }
            SymbolBody::End { .. } => {
                let space = walker.get_cur_space().cloned();
                hand.offset_space = None;
                hand.offset_offset = walker.get_naddr().get_offset();
                hand.size = space.as_ref().map(|spc| spc.get_addr_size()).unwrap_or(0);
                hand.space = space;
            }
            SymbolBody::Next2 { .. } => {
                let space = walker.get_cur_space().cloned();
                hand.offset_space = None;
                hand.offset_offset = walker.get_n2addr()?.get_offset();
                hand.size = space.as_ref().map(|spc| spc.get_addr_size()).unwrap_or(0);
                hand.space = space;
            }
            SymbolBody::Flowdest { const_space } => {
                let ref_addr = walker.get_dest_addr();
                hand.space = const_space.clone();
                hand.offset_space = None;
                hand.offset_offset = ref_addr.get_offset();
                hand.size = ref_addr.get_addr_size() as u32;
            }
            SymbolBody::Flowref { const_space } => {
                let ref_addr = walker.get_ref_addr();
                hand.space = const_space.clone();
                hand.offset_space = None;
                hand.offset_offset = ref_addr.get_offset();
                hand.size = ref_addr.get_addr_size() as u32;
            }
            SymbolBody::Subtable(_) => {
                return Err(Error::Sleigh("Cannot use subtable in expression".to_string()));
            }
            _ => {
                return Err(Error::Sleigh(format!(
                    "Symbol {} cannot produce a fixed handle",
                    self.name
                )));
            }
        }
        Ok(())
    }

    pub fn get_size(&self, symtab: &SymbolTable) -> Result<i32> {
        match &self.body {
            SymbolBody::Varnode { fix, .. } => Ok(fix.size as i32),
            SymbolBody::Varnodelist { varnode_table, .. } => {
                for entry in varnode_table.iter().flatten() {
                    if let Some(fix) = symtab.get(*entry).get_fixed_varnode() {
                        return Ok(fix.size as i32);
                    }
                }
                Err(Error::Sleigh(format!("No register attached to: {}", self.name)))
            }
            SymbolBody::Operand(oper) => match oper.triple {
                Some(triple) => symtab.get(triple).get_size(symtab),
                None => Ok(0),
            },
            SymbolBody::Subtable(_) => Ok(-1),
            _ => Ok(0),
        }
    }

    pub fn print(&self, out: &mut String, walker: &mut ParserWalker<'_>) -> Result<()> {
        match &self.body {
            SymbolBody::Epsilon { .. } => out.push('0'),
            SymbolBody::Value { patval } | SymbolBody::Context { patval, .. } => {
                let val = match patval {
                    Some(patval) => patval.get_value(walker)?,
                    None => 0,
                };
                write_signed_hex(out, val);
            }
            SymbolBody::Valuemap { patval, valuetable, .. } => {
                let ind = match patval {
                    Some(patval) => patval.get_value(walker)? as u32,
                    None => 0,
                };
                let val = valuetable.get(ind as usize).copied().unwrap_or(0);
                write_signed_hex(out, val);
            }
            SymbolBody::Name { patval, nametable, .. } => {
                let ind = match patval {
                    Some(patval) => patval.get_value(walker)? as u32,
                    None => 0,
                };
                if let Some(name) = nametable.get(ind as usize) {
                    out.push_str(name);
                }
            }
            SymbolBody::Varnode { .. } => out.push_str(&self.name),
            SymbolBody::Varnodelist {
                patval, varnode_table, ..
            } => {
                let ind = match patval {
                    Some(patval) => patval.get_value(walker)? as u32,
                    None => 0,
                };
                if ind as usize >= varnode_table.len() {
                    return Err(Error::Sleigh("Value out of range for varnode table".to_string()));
                }
                if let Some(symid) = varnode_table[ind as usize] {
                    out.push_str(walker.symtab().get(symid).get_name());
                }
            }
            SymbolBody::Operand(oper) => {
                walker.push_operand(oper.hand)?;
                match oper.triple {
                    Some(triple) => {
                        let tsym = walker.symtab().get(triple);
                        if tsym.get_type() == SymbolType::Subtable {
                            if let Some(ct) = walker.get_constructor() {
                                ct.print(out, walker)?;
                            }
                        } else {
                            tsym.print(out, walker)?;
                        }
                    }
                    None => {
                        let val = match &oper.defexp {
                            Some(defexp) => defexp.get_value(walker)?,
                            None => 0,
                        };
                        write_signed_hex(out, val);
                    }
                }
                walker.pop_operand();
            }
            SymbolBody::Start { .. } => write_address_hex(out, walker.get_addr().get_offset()),
            SymbolBody::End { .. } => write_address_hex(out, walker.get_naddr().get_offset()),
            SymbolBody::Next2 { .. } => write_address_hex(out, walker.get_n2addr()?.get_offset()),
            SymbolBody::Flowdest { .. } => write_address_hex(out, walker.get_dest_addr().get_offset()),
            SymbolBody::Flowref { .. } => write_address_hex(out, walker.get_ref_addr().get_offset()),
            SymbolBody::Subtable(_) => {
                return Err(Error::Sleigh("Cannot use subtable in expression".to_string()));
            }
            _ => {}
        }
        Ok(())
    }

    pub fn get_varnode(&self, symtab: &SymbolTable) -> Option<VarnodeTpl> {
        match &self.body {
            SymbolBody::Epsilon { const_space } => Some(VarnodeTpl::new(
                space_const(const_space),
                ConstTpl::new_value(ConstType::Real, 0),
                ConstTpl::new_value(ConstType::Real, 0),
            )),
            SymbolBody::Varnode { fix, .. } => Some(VarnodeTpl::new(
                space_const(&fix.space),
                ConstTpl::new_value(ConstType::Real, fix.offset),
                ConstTpl::new_value(ConstType::Real, fix.size as u64),
            )),
            SymbolBody::Operand(oper) => {
                if oper.defexp.is_some() {
                    return Some(VarnodeTpl::new_handle(oper.hand, true));
                }
                if let Some(triple) = oper.triple {
                    let tsym = symtab.get(triple);
                    if tsym.is_specific() {
                        return tsym.get_varnode(symtab);
                    }
                    if tsym.get_type() == SymbolType::Valuemap || tsym.get_type() == SymbolType::Name {
                        return Some(VarnodeTpl::new_handle(oper.hand, true));
                    }
                }
                Some(VarnodeTpl::new_handle(oper.hand, false))
            }
            SymbolBody::Start { const_space } => Some(VarnodeTpl::new(
                space_const(const_space),
                ConstTpl::new_type(ConstType::JStart),
                ConstTpl::new(),
            )),
            SymbolBody::End { const_space } => Some(VarnodeTpl::new(
                space_const(const_space),
                ConstTpl::new_type(ConstType::JNext),
                ConstTpl::new(),
            )),
            SymbolBody::Next2 { const_space } => Some(VarnodeTpl::new(
                space_const(const_space),
                ConstTpl::new_type(ConstType::JNext2),
                ConstTpl::new(),
            )),
            SymbolBody::Flowdest { const_space } => Some(VarnodeTpl::new(
                space_const(const_space),
                ConstTpl::new_type(ConstType::JFlowdest),
                ConstTpl::new(),
            )),
            SymbolBody::Flowref { const_space } => Some(VarnodeTpl::new(
                space_const(const_space),
                ConstTpl::new_type(ConstType::JFlowref),
                ConstTpl::new(),
            )),
            _ => None,
        }
    }

    pub fn collect_local_values(&self, symtab: &SymbolTable, results: &mut Vec<u64>) {
        match &self.body {
            SymbolBody::Varnode { fix, .. }
                if fix
                    .space
                    .as_ref()
                    .is_some_and(|spc| spc.get_type() == SpaceType::Internal) =>
            {
                results.push(fix.offset);
            }
            SymbolBody::Operand(oper) => {
                if let Some(triple) = oper.triple {
                    symtab.get(triple).collect_local_values(symtab, results);
                }
            }
            SymbolBody::Subtable(sub) => {
                for ct in sub.construct.iter() {
                    ct.collect_local_exports(symtab, results);
                }
            }
            _ => {}
        }
    }
}

impl Constructor {
    pub fn collect_local_exports(&self, symtab: &SymbolTable, results: &mut Vec<u64>) {
        let Some(templ) = &self.templ else {
            return;
        };
        let Some(handle) = templ.get_result() else {
            return;
        };
        if handle.get_space().is_const_space() {
            return;
        }
        if handle.get_ptr_space().get_type() != ConstType::Real {
            if handle.get_temp_space().is_unique_space() {
                results.push(handle.get_temp_offset().get_real());
            }
            return;
        }
        if handle.get_space().is_unique_space() {
            results.push(handle.get_ptr_offset().get_real());
            return;
        }
        if handle.get_space().get_type() == ConstType::Handle {
            let handle_index = handle.get_space().get_handle_index();
            if let Some(op_sym) = self.get_operand(handle_index) {
                symtab.get(op_sym).collect_local_values(symtab, results);
            }
        }
    }
}

fn space_const(space: &Option<SpaceRef>) -> ConstTpl {
    match space {
        Some(spc) => ConstTpl::new_space(spc.clone()),
        None => ConstTpl::new_type(ConstType::Spaceid),
    }
}

fn bad_table_entry(walker: &ParserWalker<'_>, table: &str) -> Error {
    let addr = walker.get_addr();
    let mut message = String::new();
    message.push(addr.get_shortcut());
    addr.print_raw(&mut message);
    let _ = write!(message, ": No corresponding entry in {table}");
    Error::BadData(message)
}

#[derive(Clone, Debug)]
pub struct SymbolScope {
    parent: Option<u32>,
    tree: BTreeMap<String, SymbolId>,
    id: u32,
}

impl SymbolScope {
    pub fn new(parent: Option<u32>, id: u32) -> SymbolScope {
        SymbolScope {
            parent,
            tree: BTreeMap::new(),
            id,
        }
    }

    pub fn get_parent(&self) -> Option<u32> {
        self.parent
    }

    pub fn get_id(&self) -> u32 {
        self.id
    }

    pub fn add_symbol(&mut self, name: &str, id: SymbolId) -> SymbolId {
        if let Some(existing) = self.tree.get(name) {
            return *existing;
        }
        self.tree.insert(name.to_string(), id);
        id
    }

    pub fn find_symbol(&self, name: &str) -> Option<SymbolId> {
        self.tree.get(name).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.tree.values().copied()
    }

    pub fn remove_symbol(&mut self, name: &str) {
        self.tree.remove(name);
    }
}

#[derive(Clone, Debug, Default)]
pub struct SymbolTable {
    symbollist: Vec<Option<SleighSymbol>>,
    table: Vec<Option<SymbolScope>>,
    curscope: Option<u32>,
}

const MAX_TABLES: i64 = 0x100000;
const MAX_SYMBOLS: i64 = 0x1000000;

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable::default()
    }

    pub fn get(&self, id: SymbolId) -> &SleighSymbol {
        match self.symbollist.get(id as usize) {
            Some(Some(sym)) => sym,
            _ => &DUMMY_SYMBOL,
        }
    }

    pub fn get_mut(&mut self, id: SymbolId) -> Option<&mut SleighSymbol> {
        self.symbollist.get_mut(id as usize).and_then(|sym| sym.as_mut())
    }

    pub fn num_symbols(&self) -> usize {
        self.symbollist.len()
    }

    pub fn get_constructor(&self, ct: ConstructorRef) -> &Constructor {
        match &self.get(ct.table).body {
            SymbolBody::Subtable(sub) => sub.construct.get(ct.index as usize).unwrap_or(&EMPTY_CONSTRUCTOR),
            _ => &EMPTY_CONSTRUCTOR,
        }
    }

    pub fn get_current_scope(&self) -> Option<u32> {
        self.curscope
    }

    pub fn get_global_scope(&self) -> Option<&SymbolScope> {
        self.table.first().and_then(|scope| scope.as_ref())
    }

    pub fn get_scope(&self, id: u32) -> Option<&SymbolScope> {
        self.table.get(id as usize).and_then(|scope| scope.as_ref())
    }

    pub fn set_current_scope(&mut self, scope: Option<u32>) {
        self.curscope = scope;
    }

    pub fn add_scope(&mut self) {
        let id = self.table.len() as u32;
        self.table.push(Some(SymbolScope::new(self.curscope, id)));
        self.curscope = Some(id);
    }

    pub fn pop_scope(&mut self) {
        if let Some(cur) = self.curscope {
            self.curscope = self.get_scope(cur).and_then(|scope| scope.parent);
        }
    }

    fn skip_scope(&self, count: i32) -> Option<u32> {
        let mut res = self.curscope;
        let mut remaining = count;
        while remaining > 0 {
            let parent = res.and_then(|id| self.get_scope(id)).and_then(|scope| scope.parent);
            match parent {
                None => return res,
                Some(parent) => res = Some(parent),
            }
            remaining -= 1;
        }
        res
    }

    fn insert_into_scope(&mut self, scope: u32, mut sym: SleighSymbol) -> Result<SymbolId> {
        let id = self.symbollist.len() as SymbolId;
        sym.id = id;
        sym.scopeid = scope;
        let name = sym.name.clone();
        self.symbollist.push(Some(sym));
        let res = match self.table.get_mut(scope as usize) {
            Some(Some(table)) => table.add_symbol(&name, id),
            _ => return Err(Error::Sleigh("Bad symbol scope".to_string())),
        };
        if res != id {
            return Err(Error::Sleigh(format!("Duplicate symbol name: {name}")));
        }
        Ok(id)
    }

    pub fn add_global_symbol(&mut self, sym: SleighSymbol) -> Result<SymbolId> {
        let name = sym.name.clone();
        self.insert_into_scope(0, sym).map_err(|err| match err {
            Error::Sleigh(message) if message.starts_with("Duplicate") => {
                Error::Sleigh(format!("Duplicate symbol name '{name}'"))
            }
            other => other,
        })
    }

    pub fn add_symbol(&mut self, sym: SleighSymbol) -> Result<SymbolId> {
        let scope = self.curscope.unwrap_or(0);
        self.insert_into_scope(scope, sym)
    }

    fn find_symbol_internal(&self, mut scope: Option<u32>, name: &str) -> Option<SymbolId> {
        while let Some(id) = scope {
            let current = self.get_scope(id)?;
            if let Some(res) = current.find_symbol(name) {
                return Some(res);
            }
            scope = current.parent;
        }
        None
    }

    pub fn find_symbol(&self, name: &str) -> Option<&SleighSymbol> {
        self.find_symbol_internal(self.curscope, name).map(|id| self.get(id))
    }

    pub fn find_symbol_skip(&self, name: &str, skip: i32) -> Option<&SleighSymbol> {
        self.find_symbol_internal(self.skip_scope(skip), name)
            .map(|id| self.get(id))
    }

    pub fn find_global_symbol(&self, name: &str) -> Option<&SleighSymbol> {
        let global = if self.table.is_empty() { None } else { Some(0) };
        self.find_symbol_internal(global, name).map(|id| self.get(id))
    }

    pub fn find_symbol_by_id(&self, id: u32) -> Result<&SleighSymbol> {
        if id as usize >= self.symbollist.len() {
            return Err(Error::Sleigh("Bad symbol id".to_string()));
        }
        Ok(self.get(id))
    }

    pub fn replace_symbol(&mut self, old: SymbolId, mut replacement: SleighSymbol) {
        let Some(Some(oldsym)) = self.symbollist.get(old as usize) else {
            return;
        };
        let name = oldsym.name.clone();
        let scopeid = oldsym.scopeid;
        for index in (0..self.table.len()).rev() {
            let Some(Some(scope)) = self.table.get_mut(index) else {
                continue;
            };
            if scope.find_symbol(&name) == Some(old) {
                scope.remove_symbol(&name);
                replacement.id = old;
                replacement.scopeid = scopeid;
                let newname = replacement.name.clone();
                self.symbollist[old as usize] = Some(replacement);
                if let Some(Some(scope)) = self.table.get_mut(index) {
                    scope.add_symbol(&newname, old);
                }
                return;
            }
        }
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, const_space: &SpaceRef) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_SYMBOL_TABLE)?;
        let table_size = decoder.read_signed_integer_attr(ATTRIB_SCOPESIZE)?;
        let symbol_size = decoder.read_signed_integer_attr(ATTRIB_SYMBOLSIZE)?;
        if table_size < 0 || symbol_size < 0 {
            return Err(Error::Sleigh("Bad symbol table size".to_string()));
        }
        if table_size > MAX_TABLES {
            return Err(Error::Sleigh("Maximum scopes exceeded".to_string()));
        }
        if symbol_size > MAX_SYMBOLS {
            return Err(Error::Sleigh("Maximum symbols exceeded".to_string()));
        }
        self.table.resize(table_size as usize, None);
        self.symbollist.resize(symbol_size as usize, None);
        for _ in 0..self.table.len() {
            let subel = decoder.open_element_expect(ELEM_SCOPE)?;
            let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)? as u32;
            if id as usize >= self.table.len() {
                return Err(Error::Sleigh(
                    "Bad symbol scope id: exceeds symbol scope table size".to_string(),
                ));
            }
            let parent = decoder.read_unsigned_integer_attr(ATTRIB_PARENT)? as u32;
            if parent as usize >= self.table.len() {
                return Err(Error::Sleigh(
                    "Bad symbol scope parent id: exceeds symbol scope table size".to_string(),
                ));
            }
            let parscope = if parent == id || self.table[parent as usize].is_none() {
                None
            } else {
                Some(parent)
            };
            if self.table[id as usize].is_some() {
                return Err(Error::Sleigh("Bad symbol scope parent id: not unique".to_string()));
            }
            self.table[id as usize] = Some(SymbolScope::new(parscope, id));
            decoder.close_element(subel)?;
        }
        self.curscope = if self.table.first().is_some_and(|scope| scope.is_some()) {
            Some(0)
        } else {
            None
        };
        for _ in 0..self.symbollist.len() {
            self.decode_symbol_header(decoder)?;
        }
        while decoder.peek_element()? != 0 {
            decoder.open_element()?;
            let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)? as u32;
            self.find_symbol_by_id(id)?;
            self.decode_symbol_content(decoder, id, const_space)?;
        }
        decoder.close_element(el)
    }

    fn decode_symbol_header(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.peek_element()?;
        let body = if el == ELEM_USEROP_HEAD {
            SymbolBody::Userop { index: 0 }
        } else if el == ELEM_EPSILON_SYM_HEAD {
            SymbolBody::Epsilon { const_space: None }
        } else if el == ELEM_VALUE_SYM_HEAD {
            SymbolBody::Value { patval: None }
        } else if el == ELEM_VALUEMAP_SYM_HEAD {
            SymbolBody::Valuemap {
                patval: None,
                valuetable: Vec::new(),
                tableisfilled: false,
            }
        } else if el == ELEM_NAME_SYM_HEAD {
            SymbolBody::Name {
                patval: None,
                nametable: Vec::new(),
                tableisfilled: false,
            }
        } else if el == ELEM_VARNODE_SYM_HEAD {
            SymbolBody::Varnode {
                fix: VarnodeData::default(),
                context_bits: false,
            }
        } else if el == ELEM_CONTEXT_SYM_HEAD {
            SymbolBody::Context {
                patval: None,
                vn: 0,
                low: 0,
                high: 0,
                flow: false,
            }
        } else if el == ELEM_VARLIST_SYM_HEAD {
            SymbolBody::Varnodelist {
                patval: None,
                varnode_table: Vec::new(),
                tableisfilled: false,
            }
        } else if el == ELEM_OPERAND_SYM_HEAD {
            SymbolBody::Operand(Box::default())
        } else if el == ELEM_START_SYM_HEAD {
            SymbolBody::Start { const_space: None }
        } else if el == ELEM_END_SYM_HEAD {
            SymbolBody::End { const_space: None }
        } else if el == ELEM_NEXT2_SYM_HEAD {
            SymbolBody::Next2 { const_space: None }
        } else if el == ELEM_SUBTABLE_SYM_HEAD {
            SymbolBody::Subtable(Box::default())
        } else {
            return Err(Error::Sleigh("Bad symbol xml".to_string()));
        };
        let subel = decoder.open_element()?;
        let name = decoder.read_string_attr(ATTRIB_NAME)?;
        let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)? as u32;
        let scopeid = decoder.read_unsigned_integer_attr(ATTRIB_SCOPE)? as u32;
        decoder.close_element(subel)?;
        if id as usize >= self.symbollist.len() {
            return Err(Error::Sleigh("Bad symbol id: exceeds symbollist size".to_string()));
        }
        if self.symbollist[id as usize].is_some() {
            return Err(Error::Sleigh("Bad symbol id: not unique".to_string()));
        }
        if scopeid as usize >= self.table.len() {
            return Err(Error::Sleigh("Bad symbol scope id: too large".to_string()));
        }
        if self.table[scopeid as usize].is_none() {
            return Err(Error::Sleigh("Bad symbol scope id: undefined".to_string()));
        }
        if let Some(Some(scope)) = self.table.get_mut(scopeid as usize) {
            scope.add_symbol(&name, id);
        }
        self.symbollist[id as usize] = Some(SleighSymbol {
            name,
            id,
            scopeid,
            body,
        });
        Ok(())
    }

    fn decode_symbol_content(&mut self, decoder: &mut dyn Decoder, id: SymbolId, const_space: &SpaceRef) -> Result<()> {
        let sym_type = self.get(id).get_type();
        if sym_type == SymbolType::Subtable {
            return self.decode_subtable(decoder, id);
        }
        let name = self.get(id).name.clone();
        let mut body = match self.get_mut(id) {
            Some(sym) => std::mem::replace(&mut sym.body, SymbolBody::Dummy),
            None => return Err(Error::Sleigh("Bad symbol id".to_string())),
        };
        let res = self.decode_body(decoder, &mut body, const_space, &name);
        if let Some(sym) = self.get_mut(id) {
            sym.body = body;
        }
        res
    }

    fn decode_body(
        &self,
        decoder: &mut dyn Decoder,
        body: &mut SymbolBody,
        const_space: &SpaceRef,
        name: &str,
    ) -> Result<()> {
        match body {
            SymbolBody::Userop { index } => {
                *index = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as u32;
                decoder.close_element(ELEM_USEROP.get_id())
            }
            SymbolBody::Epsilon { const_space: space } => {
                *space = Some(const_space.clone());
                decoder.close_element(ELEM_EPSILON_SYM.get_id())
            }
            SymbolBody::Value { patval } => {
                if patval.is_some() {
                    return Err(Error::Decoder("Already decoded symbol".to_string()));
                }
                *patval = Some(PatternExpression::decode_expression(decoder, self)?);
                decoder.close_element(ELEM_VALUE_SYM.get_id())
            }
            SymbolBody::Valuemap {
                patval,
                valuetable,
                tableisfilled,
            } => {
                if patval.is_some() {
                    return Err(Error::Decoder("Already decoded symbol".to_string()));
                }
                *patval = Some(PatternExpression::decode_expression(decoder, self)?);
                while decoder.peek_element()? != 0 {
                    let subel = decoder.open_element()?;
                    let val = decoder.read_signed_integer_attr(ATTRIB_VAL)?;
                    valuetable.push(val);
                    decoder.close_element(subel)?;
                }
                decoder.close_element(ELEM_VALUEMAP_SYM.get_id())?;
                *tableisfilled = check_table_fill(patval, valuetable.len()) && !valuetable.contains(&0xBADBEEF);
                Ok(())
            }
            SymbolBody::Name {
                patval,
                nametable,
                tableisfilled,
            } => {
                if patval.is_some() {
                    return Err(Error::Decoder("Already decoded symbol".to_string()));
                }
                *patval = Some(PatternExpression::decode_expression(decoder, self)?);
                while decoder.peek_element()? != 0 {
                    let subel = decoder.open_element()?;
                    if decoder.get_next_attribute_id()? == ATTRIB_NAME {
                        nametable.push(decoder.read_string()?);
                    } else {
                        nametable.push("\t".to_string());
                    }
                    decoder.close_element(subel)?;
                }
                decoder.close_element(ELEM_NAME_SYM.get_id())?;
                let mut filled = check_table_fill(patval, nametable.len());
                for entry in nametable.iter_mut() {
                    if entry == "_" || entry == "\t" {
                        *entry = "\t".to_string();
                        filled = false;
                    }
                }
                *tableisfilled = filled;
                Ok(())
            }
            SymbolBody::Varnode { fix, .. } => {
                fix.space = Some(decoder.read_space_attr(ATTRIB_SPACE)?);
                fix.offset = decoder.read_unsigned_integer_attr(ATTRIB_OFF)?;
                fix.size = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as u32;
                decoder.close_element(ELEM_VARNODE_SYM.get_id())
            }
            SymbolBody::Context {
                patval,
                vn,
                low,
                high,
                flow,
            } => {
                *flow = false;
                let mut high_missing = true;
                let mut low_missing = true;
                let mut attrib = decoder.get_next_attribute_id()?;
                while attrib != 0 {
                    if attrib == ATTRIB_VARNODE {
                        let id = decoder.read_unsigned_integer()? as u32;
                        self.find_symbol_by_id(id)?;
                        *vn = id;
                    } else if attrib == ATTRIB_LOW {
                        *low = decoder.read_signed_integer()? as u32;
                        low_missing = false;
                    } else if attrib == ATTRIB_HIGH {
                        *high = decoder.read_signed_integer()? as u32;
                        high_missing = false;
                    } else if attrib == ATTRIB_FLOW {
                        *flow = decoder.read_bool()?;
                    }
                    attrib = decoder.get_next_attribute_id()?;
                }
                if low_missing || high_missing {
                    return Err(Error::Decoder("Missing high/low attributes".to_string()));
                }
                if patval.is_some() {
                    return Err(Error::Decoder("Already decoded symbol".to_string()));
                }
                *patval = Some(PatternExpression::decode_expression(decoder, self)?);
                decoder.close_element(ELEM_CONTEXT_SYM.get_id())
            }
            SymbolBody::Varnodelist {
                patval,
                varnode_table,
                tableisfilled,
            } => {
                if patval.is_some() {
                    return Err(Error::Decoder("Already decoded symbol".to_string()));
                }
                *patval = Some(PatternExpression::decode_expression(decoder, self)?);
                while decoder.peek_element()? != 0 {
                    let subel = decoder.open_element()?;
                    if subel == ELEM_VAR {
                        let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)? as u32;
                        self.find_symbol_by_id(id)?;
                        varnode_table.push(Some(id));
                    } else {
                        varnode_table.push(None);
                    }
                    decoder.close_element(subel)?;
                }
                decoder.close_element(ELEM_VARLIST_SYM.get_id())?;
                *tableisfilled =
                    check_table_fill(patval, varnode_table.len()) && varnode_table.iter().all(|entry| entry.is_some());
                Ok(())
            }
            SymbolBody::Operand(oper) => {
                if oper.defexp.is_some() || oper.localexp.is_some() {
                    return Err(Error::Decoder("Already decoded symbol".to_string()));
                }
                oper.defexp = None;
                oper.triple = None;
                oper.flags = 0;
                let mut attrib = decoder.get_next_attribute_id()?;
                while attrib != 0 {
                    attrib = decoder.get_next_attribute_id()?;
                    if attrib == ATTRIB_INDEX {
                        oper.hand = decoder.read_signed_integer()? as i32;
                    } else if attrib == ATTRIB_OFF {
                        oper.reloffset = decoder.read_signed_integer()? as u32;
                    } else if attrib == ATTRIB_BASE {
                        oper.offsetbase = decoder.read_signed_integer()? as i32;
                    } else if attrib == ATTRIB_MINLEN {
                        oper.minimumlength = decoder.read_signed_integer()? as i32;
                    } else if attrib == ATTRIB_SUBSYM {
                        let id = decoder.read_unsigned_integer()? as u32;
                        self.find_symbol_by_id(id)?;
                        oper.triple = Some(id);
                    } else if attrib == ATTRIB_CODE && decoder.read_bool()? {
                        oper.flags |= OperandSymbol::CODE_ADDRESS;
                    }
                }
                oper.localexp = Some(PatternExpression::decode_expression(decoder, self)?);
                if decoder.peek_element()? != 0 {
                    oper.defexp = Some(PatternExpression::decode_expression(decoder, self)?);
                }
                decoder.close_element(ELEM_OPERAND_SYM.get_id())
            }
            SymbolBody::Start { const_space: space } => {
                *space = Some(const_space.clone());
                decoder.close_element(ELEM_START_SYM.get_id())
            }
            SymbolBody::End { const_space: space } => {
                *space = Some(const_space.clone());
                decoder.close_element(ELEM_END_SYM.get_id())
            }
            SymbolBody::Next2 { const_space: space } => {
                *space = Some(const_space.clone());
                decoder.close_element(ELEM_NEXT2_SYM.get_id())
            }
            _ => Err(Error::Lowlevel(format!(
                "Symbol {name} cannot be decoded from stream directly"
            ))),
        }
    }

    fn subtable_mut(&mut self, id: SymbolId) -> Option<&mut SubtableSymbol> {
        match self.get_mut(id).map(|sym| &mut sym.body) {
            Some(SymbolBody::Subtable(sub)) => Some(sub),
            _ => None,
        }
    }

    fn decode_subtable(&mut self, decoder: &mut dyn Decoder, id: SymbolId) -> Result<()> {
        let numct = decoder.read_signed_integer_attr(ATTRIB_NUMCT)?;
        if let Some(sub) = self.subtable_mut(id) {
            sub.construct.reserve(numct.clamp(0, 0x10000) as usize);
        }
        let mut subel = decoder.peek_element()?;
        while subel != 0 {
            if subel == ELEM_CONSTRUCTOR {
                let index = match self.subtable_mut(id) {
                    Some(sub) => {
                        let index = sub.construct.len() as u32;
                        let mut placeholder = Constructor::empty();
                        placeholder.id = index;
                        sub.construct.push(placeholder);
                        index
                    }
                    None => return Err(Error::Sleigh("Bad symbol id".to_string())),
                };
                let mut ct = Constructor::empty();
                ct.id = index;
                let res = ct.decode(decoder, self);
                if let Some(sub) = self.subtable_mut(id) {
                    sub.construct[index as usize] = ct;
                }
                res?;
            } else if subel == ELEM_DECISION {
                let numct = self.get(id).subtable_num_constructors();
                let mut tree = DecisionNode::default();
                tree.decode(decoder, numct)?;
                if let Some(sub) = self.subtable_mut(id) {
                    sub.decisiontree = Some(tree);
                }
            } else {
                return Err(Error::Decoder("unexpected element in subtable symbol".to_string()));
            }
            subel = decoder.peek_element()?;
        }
        if let Some(sub) = self.subtable_mut(id) {
            sub.beingbuilt = false;
            sub.errors = false;
        }
        decoder.close_element(ELEM_SUBTABLE_SYM.get_id())
    }
}
