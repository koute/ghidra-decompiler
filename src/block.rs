use std::cmp::Ordering;
use std::fmt::Write;

use crate::address::{Address, RangeList};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::define_id;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::jumptable::{JumpTable, JumpTableId};
use crate::marshal::{ATTRIB_INDEX, ATTRIB_TYPE, AttributeId, Decoder, ELEM_TARGET, ElementId, Encoder};
use crate::op::{OpId, PcodeOp};
use crate::opcodes::{OpCode, get_opname};
use crate::oplist::OpList;
use crate::printlanguage::{PrintContext, PrintLanguage};
use crate::types::TypeId;
use crate::varnode::VarnodeId;

pub const ATTRIB_ALTINDEX: AttributeId = AttributeId::new("altindex", 75);
pub const ATTRIB_DEPTH: AttributeId = AttributeId::new("depth", 76);
pub const ATTRIB_END: AttributeId = AttributeId::new("end", 77);
pub const ATTRIB_OPCODE: AttributeId = AttributeId::new("opcode", 78);
pub const ATTRIB_REV: AttributeId = AttributeId::new("rev", 79);
pub const ELEM_BHEAD: ElementId = ElementId::new("bhead", 102);
pub const ELEM_BLOCK: ElementId = ElementId::new("block", 103);
pub const ELEM_BLOCKEDGE: ElementId = ElementId::new("blockedge", 104);
pub const ELEM_EDGE: ElementId = ElementId::new("edge", 105);

define_id!(BlockId);

#[derive(Clone, Debug)]
pub struct BlockEdge {
    pub label: u32,
    pub point: BlockId,
    pub reverse_index: i32,
}

impl BlockEdge {
    pub fn new(pt: BlockId, lab: u32, rev: i32) -> BlockEdge {
        BlockEdge {
            label: lab,
            point: pt,
            reverse_index: rev,
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, blocks: &Arena<BlockId, FlowBlock>) -> Result<()> {
        encoder.open_element(ELEM_EDGE);
        encoder.write_signed_integer(ATTRIB_END, blocks[self.point].get_index() as i64);
        encoder.write_signed_integer(ATTRIB_REV, self.reverse_index as i64);
        encoder.close_element(ELEM_EDGE);
        Ok(())
    }

    pub fn decode(
        decoder: &mut dyn Decoder,
        resolver: &BlockMap,
        blocks: &Arena<BlockId, FlowBlock>,
    ) -> Result<BlockEdge> {
        let elem_id = decoder.open_element_expect(ELEM_EDGE)?;
        let end_index = decoder.read_signed_integer_attr(ATTRIB_END)? as i32;
        let point = resolver
            .find_level_block(end_index, blocks)
            .ok_or_else(|| Error::Lowlevel("Bad serialized edge in block graph".to_string()))?;
        let reverse_index = decoder.read_signed_integer_attr(ATTRIB_REV)? as i32;
        decoder.close_element(elem_id)?;
        Ok(BlockEdge::new(point, 0, reverse_index))
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BlockType {
    Plain = 0,
    Basic = 1,
    Graph = 2,
    Copy = 3,
    Goto = 4,
    MultiGoto = 5,
    Ls = 6,
    Condition = 7,
    If = 8,
    IfElse = 9,
    IfNoExit = 10,
    IfGoto = 11,
    WhileDo = 12,
    DoWhile = 13,
    Switch = 14,
    InfLoop = 15,
}

#[derive(Clone, Debug)]
pub struct BlockBasicData {
    pub op: OpList,
    pub cover: RangeList,
}

#[derive(Clone, Debug)]
pub struct CaseOrder {
    pub block: BlockId,
    pub basicblock: BlockId,
    pub label: u64,
    pub depth: i32,
    pub chain: i32,
    pub outindex: i32,
    pub gototype: u32,
    pub isexit: bool,
    pub isdefault: bool,
}

impl CaseOrder {
    pub fn compare(first: &CaseOrder, second: &CaseOrder) -> bool {
        if first.label != second.label {
            return first.label < second.label;
        }
        first.depth < second.depth
    }
}

#[derive(Clone, Debug)]
pub enum BlockKind {
    Plain,
    Basic(BlockBasicData),
    Graph,
    Copy {
        copy: Option<BlockId>,
    },
    Goto {
        gototarget: BlockId,
        gototype: u32,
    },
    MultiGoto {
        gotoedges: Vec<BlockId>,
        defaultswitch: bool,
    },
    List,
    Condition {
        opc: OpCode,
    },
    If,
    IfElse,
    IfNoExit,
    IfGoto {
        gototype: u32,
        gototarget: BlockId,
    },
    WhileDo {
        initialize_op: Option<OpId>,
        iterate_op: Option<OpId>,
        loop_def: Option<OpId>,
    },
    DoWhile,
    InfLoop,
    Switch {
        jump: Option<JumpTableId>,
        caseblocks: Vec<CaseOrder>,
    },
}

#[derive(Clone, Debug)]
pub struct FlowBlock {
    pub parent: Option<BlockId>,
    pub immed_dom: Option<BlockId>,
    pub copymap: Option<BlockId>,
    pub intothis: Vec<BlockEdge>,
    pub outofthis: Vec<BlockEdge>,
    pub flags: u32,
    pub index: i32,
    pub visitcount: i32,
    pub numdesc: i32,
    pub leaf_count: i32,
    pub structure_depth: i32,
    pub list: Vec<BlockId>,
    pub kind: BlockKind,
}

impl FlowBlock {
    pub const F_GOTO_GOTO: u32 = 1;
    pub const F_BREAK_GOTO: u32 = 2;
    pub const F_CONTINUE_GOTO: u32 = 4;
    pub const F_SWITCH_OUT: u32 = 0x10;
    pub const F_UNSTRUCTURED_TARG: u32 = 0x20;
    pub const F_MARK: u32 = 0x80;
    pub const F_MARK2: u32 = 0x100;
    pub const F_ENTRY_POINT: u32 = 0x200;
    pub const F_INTERIOR_GOTOOUT: u32 = 0x400;
    pub const F_INTERIOR_GOTOIN: u32 = 0x800;
    pub const F_LABEL_BUMPUP: u32 = 0x1000;
    pub const F_DONOTHING_LOOP: u32 = 0x2000;
    pub const F_DEAD: u32 = 0x4000;
    pub const F_WHILEDO_OVERFLOW: u32 = 0x8000;
    pub const F_FLIP_PATH: u32 = 0x10000;
    pub const F_JOINED_BLOCK: u32 = 0x20000;
    pub const F_DUPLICATE_BLOCK: u32 = 0x40000;
    pub const F_DELAYED_DONOTHING: u32 = 0x80000;
    pub const F_FINAL_TRANSFORM: u32 = 0x100000;

    pub const F_GOTO_EDGE: u32 = 1;
    pub const F_LOOP_EDGE: u32 = 2;
    pub const F_DEFAULTSWITCH_EDGE: u32 = 4;
    pub const F_IRREDUCIBLE: u32 = 8;
    pub const F_TREE_EDGE: u32 = 0x10;
    pub const F_FORWARD_EDGE: u32 = 0x20;
    pub const F_CROSS_EDGE: u32 = 0x40;
    pub const F_BACK_EDGE: u32 = 0x80;
    pub const F_LOOP_EXIT_EDGE: u32 = 0x100;
    pub const F_IMMED_COPY: u32 = 0x200;

    pub fn new(kind: BlockKind) -> FlowBlock {
        FlowBlock {
            parent: None,
            immed_dom: None,
            copymap: None,
            intothis: Vec::new(),
            outofthis: Vec::new(),
            flags: 0,
            index: 0,
            visitcount: 0,
            numdesc: 0,
            leaf_count: 1,
            structure_depth: 0,
            list: Vec::new(),
            kind,
        }
    }

    pub fn new_graph_kind(kind: BlockKind) -> FlowBlock {
        let mut block = FlowBlock::new(kind);
        block.leaf_count = 0;
        block
    }

    pub fn new_basic() -> FlowBlock {
        FlowBlock::new(BlockKind::Basic(BlockBasicData {
            op: OpList::new(PcodeOp::BASIC_LIST),
            cover: RangeList::new(),
        }))
    }

    pub fn new_copy(bl: Option<BlockId>) -> FlowBlock {
        FlowBlock::new(BlockKind::Copy { copy: bl })
    }

    pub fn new_goto(bl: BlockId) -> FlowBlock {
        FlowBlock::new_graph_kind(BlockKind::Goto {
            gototarget: bl,
            gototype: FlowBlock::F_GOTO_GOTO,
        })
    }

    pub fn new_multi_goto(_bl: BlockId) -> FlowBlock {
        FlowBlock::new_graph_kind(BlockKind::MultiGoto {
            gotoedges: Vec::new(),
            defaultswitch: false,
        })
    }

    pub fn new_condition(opc: OpCode) -> FlowBlock {
        FlowBlock::new_graph_kind(BlockKind::Condition { opc })
    }

    pub fn new_if_goto(target: BlockId) -> FlowBlock {
        FlowBlock::new_graph_kind(BlockKind::IfGoto {
            gototype: FlowBlock::F_GOTO_GOTO,
            gototarget: target,
        })
    }

    pub fn new_while_do() -> FlowBlock {
        FlowBlock::new_graph_kind(BlockKind::WhileDo {
            initialize_op: None,
            iterate_op: None,
            loop_def: None,
        })
    }

    pub fn is_graph(&self) -> bool {
        !matches!(
            self.kind,
            BlockKind::Plain | BlockKind::Basic(_) | BlockKind::Copy { .. }
        )
    }

    pub fn basic(&self) -> &BlockBasicData {
        match &self.kind {
            BlockKind::Basic(data) => data,
            _ => panic!("block is not a basic block"),
        }
    }

    pub fn basic_mut(&mut self) -> &mut BlockBasicData {
        match &mut self.kind {
            BlockKind::Basic(data) => data,
            _ => panic!("block is not a basic block"),
        }
    }

    pub fn set_flag(&mut self, fl: u32) {
        self.flags |= fl;
    }

    pub fn clear_flag(&mut self, fl: u32) {
        self.flags &= !fl;
    }

    pub fn clear_all_flags(&mut self) {
        self.flags = 0;
    }

    pub fn get_index(&self) -> i32 {
        self.index
    }

    pub fn get_parent(&self) -> Option<BlockId> {
        self.parent
    }

    pub fn get_immed_dom(&self) -> Option<BlockId> {
        self.immed_dom
    }

    pub fn get_copy_map(&self) -> Option<BlockId> {
        self.copymap
    }

    pub fn get_flags(&self) -> u32 {
        self.flags
    }

    pub fn get_start(&self) -> Address {
        match &self.kind {
            BlockKind::Basic(data) => match data.cover.get_first_range() {
                None => Address::invalid(),
                Some(range) => range.get_first_addr(),
            },
            _ => Address::invalid(),
        }
    }

    pub fn get_stop(&self) -> Address {
        match &self.kind {
            BlockKind::Basic(data) => match data.cover.get_last_range() {
                None => Address::invalid(),
                Some(range) => range.get_last_addr(),
            },
            _ => Address::invalid(),
        }
    }

    pub fn get_type(&self) -> BlockType {
        match &self.kind {
            BlockKind::Plain => BlockType::Plain,
            BlockKind::Basic(_) => BlockType::Basic,
            BlockKind::Graph => BlockType::Graph,
            BlockKind::Copy { .. } => BlockType::Copy,
            BlockKind::Goto { .. } => BlockType::Goto,
            BlockKind::MultiGoto { .. } => BlockType::MultiGoto,
            BlockKind::List => BlockType::Ls,
            BlockKind::Condition { .. } => BlockType::Condition,
            BlockKind::If => BlockType::If,
            BlockKind::IfElse => BlockType::IfElse,
            BlockKind::IfNoExit => BlockType::IfNoExit,
            BlockKind::IfGoto { .. } => BlockType::IfGoto,
            BlockKind::WhileDo { .. } => BlockType::WhileDo,
            BlockKind::DoWhile => BlockType::DoWhile,
            BlockKind::InfLoop => BlockType::InfLoop,
            BlockKind::Switch { .. } => BlockType::Switch,
        }
    }

    pub fn sub_block(&self, index: i32) -> Option<BlockId> {
        match &self.kind {
            BlockKind::Plain | BlockKind::Basic(_) => None,
            BlockKind::Copy { copy } => *copy,
            _ => Some(self.list[index as usize]),
        }
    }

    pub fn print_short_header(&self, stream: &mut String) {
        let _ = write!(stream, "Block_{}", self.index);
        let start = self.get_start();
        if !start.is_invalid() {
            let _ = write!(stream, ":{}", start);
        }
    }

    pub fn set_visit_count(&mut self, index: i32) {
        self.visitcount = index;
    }

    pub fn get_visit_count(&self) -> i32 {
        self.visitcount
    }

    pub fn is_mark(&self) -> bool {
        (self.flags & FlowBlock::F_MARK) != 0
    }

    pub fn set_mark(&mut self) {
        self.flags |= FlowBlock::F_MARK;
    }

    pub fn clear_mark(&mut self) {
        self.flags &= !FlowBlock::F_MARK;
    }

    pub fn set_donothing_loop(&mut self) {
        self.flags |= FlowBlock::F_DONOTHING_LOOP;
    }

    pub fn set_dead(&mut self) {
        self.flags |= FlowBlock::F_DEAD;
    }

    pub fn has_special_label(&self) -> bool {
        (self.flags & (FlowBlock::F_JOINED_BLOCK | FlowBlock::F_DUPLICATE_BLOCK)) != 0
    }

    pub fn is_joined(&self) -> bool {
        (self.flags & FlowBlock::F_JOINED_BLOCK) != 0
    }

    pub fn is_duplicated(&self) -> bool {
        (self.flags & FlowBlock::F_DUPLICATE_BLOCK) != 0
    }

    pub fn has_immed_copy_edge(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label & FlowBlock::F_IMMED_COPY) != 0
    }

    pub fn get_flip_path(&self) -> bool {
        (self.flags & FlowBlock::F_FLIP_PATH) != 0
    }

    pub fn get_false_out(&self) -> BlockId {
        self.outofthis[0].point
    }

    pub fn get_true_out(&self) -> BlockId {
        self.outofthis[1].point
    }

    pub fn get_out(&self, index: i32) -> BlockId {
        self.outofthis[index as usize].point
    }

    pub fn get_out_rev_index(&self, index: i32) -> i32 {
        self.outofthis[index as usize].reverse_index
    }

    pub fn get_in(&self, index: i32) -> BlockId {
        self.intothis[index as usize].point
    }

    pub fn get_in_rev_index(&self, index: i32) -> i32 {
        self.intothis[index as usize].reverse_index
    }

    pub fn size_out(&self) -> i32 {
        self.outofthis.len() as i32
    }

    pub fn size_in(&self) -> i32 {
        self.intothis.len() as i32
    }

    pub fn has_loop_in(&self) -> bool {
        self.intothis
            .iter()
            .any(|edge| (edge.label & FlowBlock::F_LOOP_EDGE) != 0)
    }

    pub fn has_loop_out(&self) -> bool {
        self.outofthis
            .iter()
            .any(|edge| (edge.label & FlowBlock::F_LOOP_EDGE) != 0)
    }

    pub fn is_loop_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label & FlowBlock::F_LOOP_EDGE) != 0
    }

    pub fn is_loop_out(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label & FlowBlock::F_LOOP_EDGE) != 0
    }

    pub fn get_in_index(&self, bl: BlockId) -> i32 {
        match self.intothis.iter().position(|edge| edge.point == bl) {
            None => -1,
            Some(position) => position as i32,
        }
    }

    pub fn get_out_index(&self, bl: BlockId) -> i32 {
        match self.outofthis.iter().position(|edge| edge.point == bl) {
            None => -1,
            Some(position) => position as i32,
        }
    }

    pub fn is_default_branch(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label & FlowBlock::F_DEFAULTSWITCH_EDGE) != 0
    }

    pub fn is_label_bump_up(&self) -> bool {
        (self.flags & FlowBlock::F_LABEL_BUMPUP) != 0
    }

    pub fn is_unstructured_target(&self) -> bool {
        (self.flags & FlowBlock::F_UNSTRUCTURED_TARG) != 0
    }

    pub fn is_interior_goto_target(&self) -> bool {
        (self.flags & FlowBlock::F_INTERIOR_GOTOIN) != 0
    }

    pub fn has_interior_goto(&self) -> bool {
        (self.flags & FlowBlock::F_INTERIOR_GOTOOUT) != 0
    }

    pub fn is_entry_point(&self) -> bool {
        (self.flags & FlowBlock::F_ENTRY_POINT) != 0
    }

    pub fn is_switch_out(&self) -> bool {
        (self.flags & FlowBlock::F_SWITCH_OUT) != 0
    }

    pub fn is_donothing_loop(&self) -> bool {
        (self.flags & FlowBlock::F_DONOTHING_LOOP) != 0
    }

    pub fn is_dead(&self) -> bool {
        (self.flags & FlowBlock::F_DEAD) != 0
    }

    pub fn is_tree_edge_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label & FlowBlock::F_TREE_EDGE) != 0
    }

    pub fn is_back_edge_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label & FlowBlock::F_BACK_EDGE) != 0
    }

    pub fn is_back_edge_out(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label & FlowBlock::F_BACK_EDGE) != 0
    }

    pub fn is_irreducible_out(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label & FlowBlock::F_IRREDUCIBLE) != 0
    }

    pub fn is_irreducible_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label & FlowBlock::F_IRREDUCIBLE) != 0
    }

    pub fn is_decision_out(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label
            & (FlowBlock::F_IRREDUCIBLE | FlowBlock::F_BACK_EDGE | FlowBlock::F_GOTO_EDGE))
            == 0
    }

    pub fn is_decision_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label
            & (FlowBlock::F_IRREDUCIBLE | FlowBlock::F_BACK_EDGE | FlowBlock::F_GOTO_EDGE))
            == 0
    }

    pub fn is_loop_dag_out(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label
            & (FlowBlock::F_IRREDUCIBLE
                | FlowBlock::F_BACK_EDGE
                | FlowBlock::F_LOOP_EXIT_EDGE
                | FlowBlock::F_GOTO_EDGE))
            == 0
    }

    pub fn is_loop_dag_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label
            & (FlowBlock::F_IRREDUCIBLE
                | FlowBlock::F_BACK_EDGE
                | FlowBlock::F_LOOP_EXIT_EDGE
                | FlowBlock::F_GOTO_EDGE))
            == 0
    }

    pub fn is_goto_in(&self, index: i32) -> bool {
        (self.intothis[index as usize].label & (FlowBlock::F_IRREDUCIBLE | FlowBlock::F_GOTO_EDGE)) != 0
    }

    pub fn is_goto_out(&self, index: i32) -> bool {
        (self.outofthis[index as usize].label & (FlowBlock::F_IRREDUCIBLE | FlowBlock::F_GOTO_EDGE)) != 0
    }

    pub fn get_basic_count(&self) -> i32 {
        self.leaf_count
    }

    pub fn get_structure_depth(&self) -> i32 {
        self.structure_depth
    }

    pub fn name_to_type(name: &str) -> BlockType {
        match name {
            "graph" => BlockType::Graph,
            "copy" => BlockType::Copy,
            _ => BlockType::Plain,
        }
    }

    pub fn type_to_name(bt: BlockType) -> String {
        match bt {
            BlockType::Plain => "plain",
            BlockType::Basic => "basic",
            BlockType::Graph => "graph",
            BlockType::Copy => "copy",
            BlockType::Goto => "goto",
            BlockType::MultiGoto => "multigoto",
            BlockType::Ls => "list",
            BlockType::Condition => "condition",
            BlockType::If => "properif",
            BlockType::IfElse | BlockType::IfNoExit => "ifelse",
            BlockType::IfGoto => "ifgoto",
            BlockType::WhileDo => "whiledo",
            BlockType::DoWhile => "dowhile",
            BlockType::Switch => "switch",
            BlockType::InfLoop => "infloop",
        }
        .to_string()
    }

    pub fn compare_block_index(bl1: &FlowBlock, bl2: &FlowBlock) -> bool {
        bl1.get_index() < bl2.get_index()
    }

    pub fn get_list(&self) -> &[BlockId] {
        &self.list
    }

    pub fn get_size(&self) -> i32 {
        self.list.len() as i32
    }

    pub fn get_block(&self, index: i32) -> BlockId {
        self.list[index as usize]
    }

    pub fn has_final_transform(&self) -> bool {
        (self.get_flags() & FlowBlock::F_FINAL_TRANSFORM) != 0
    }

    pub fn contains(&self, addr: &Address) -> bool {
        self.basic().cover.in_range(addr, 1)
    }

    pub fn set_initial_range(&mut self, beg: &Address, end: &Address) {
        let cover = &mut self.basic_mut().cover;
        cover.clear();
        let space = beg.get_space().expect("basic block range without space");
        cover.insert_range(space, beg.get_offset(), end.get_offset());
    }

    pub fn get_op_list(&self) -> &OpList {
        &self.basic().op
    }

    pub fn get_op_list_mut(&mut self) -> &mut OpList {
        &mut self.basic_mut().op
    }

    pub fn empty_op(&self) -> bool {
        self.basic().op.is_empty()
    }

    pub fn set_delayed_donothing(&mut self) {
        self.set_flag(FlowBlock::F_DELAYED_DONOTHING);
    }

    pub fn clear_delayed_donothing(&mut self) {
        self.clear_flag(FlowBlock::F_DELAYED_DONOTHING);
    }

    pub fn is_delayed_donothing(&self) -> bool {
        (self.get_flags() & FlowBlock::F_DELAYED_DONOTHING) != 0
    }

    pub fn get_goto_target(&self) -> BlockId {
        match &self.kind {
            BlockKind::Goto { gototarget, .. } | BlockKind::IfGoto { gototarget, .. } => *gototarget,
            _ => panic!("block has no goto target"),
        }
    }

    pub fn get_goto_type(&self) -> u32 {
        match &self.kind {
            BlockKind::Goto { gototype, .. } | BlockKind::IfGoto { gototype, .. } => *gototype,
            _ => panic!("block has no goto type"),
        }
    }

    pub fn set_default_goto(&mut self) {
        if let BlockKind::MultiGoto { defaultswitch, .. } = &mut self.kind {
            *defaultswitch = true;
        }
    }

    pub fn has_default_goto(&self) -> bool {
        match &self.kind {
            BlockKind::MultiGoto { defaultswitch, .. } => *defaultswitch,
            _ => false,
        }
    }

    pub fn multigoto_add_edge(&mut self, bl: BlockId) {
        if let BlockKind::MultiGoto { gotoedges, .. } = &mut self.kind {
            gotoedges.push(bl);
        }
    }

    pub fn num_gotos(&self) -> i32 {
        match &self.kind {
            BlockKind::MultiGoto { gotoedges, .. } => gotoedges.len() as i32,
            _ => 0,
        }
    }

    pub fn get_goto(&self, index: i32) -> BlockId {
        match &self.kind {
            BlockKind::MultiGoto { gotoedges, .. } => gotoedges[index as usize],
            _ => panic!("block is not a multigoto"),
        }
    }

    pub fn get_opcode(&self) -> OpCode {
        match &self.kind {
            BlockKind::Condition { opc } => *opc,
            _ => panic!("block is not a condition"),
        }
    }

    pub fn get_initialize_op(&self) -> Option<OpId> {
        match &self.kind {
            BlockKind::WhileDo { initialize_op, .. } => *initialize_op,
            _ => None,
        }
    }

    pub fn get_iterate_op(&self) -> Option<OpId> {
        match &self.kind {
            BlockKind::WhileDo { iterate_op, .. } => *iterate_op,
            _ => None,
        }
    }

    pub fn has_overflow_syntax(&self) -> bool {
        (self.get_flags() & FlowBlock::F_WHILEDO_OVERFLOW) != 0
    }

    pub fn set_overflow_syntax(&mut self) {
        self.set_flag(FlowBlock::F_WHILEDO_OVERFLOW);
    }

    pub fn caseblocks(&self) -> &Vec<CaseOrder> {
        match &self.kind {
            BlockKind::Switch { caseblocks, .. } => caseblocks,
            _ => panic!("block is not a switch"),
        }
    }

    pub fn get_switch_block(&self) -> BlockId {
        self.get_block(0)
    }

    pub fn get_num_case_blocks(&self) -> i32 {
        self.caseblocks().len() as i32
    }

    pub fn get_case_block(&self, index: i32) -> BlockId {
        self.caseblocks()[index as usize].block
    }

    pub fn is_default_case(&self, index: i32) -> bool {
        self.caseblocks()[index as usize].isdefault
    }

    pub fn get_case_goto_type(&self, index: i32) -> u32 {
        self.caseblocks()[index as usize].gototype
    }

    pub fn is_exit(&self, index: i32) -> bool {
        self.caseblocks()[index as usize].isexit
    }
}

fn ordering_from_less(first_less: bool, second_less: bool) -> Ordering {
    if first_less {
        Ordering::Less
    } else if second_less {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

impl Funcdata {
    fn block_graph_kind(&self, bl: BlockId) -> bool {
        self.blocks[bl].is_graph()
    }

    pub fn block_add_in_edge(&mut self, bl: BlockId, source: BlockId, lab: u32) {
        let ourrev = self.blocks[source].outofthis.len() as i32;
        let brev = self.blocks[bl].intothis.len() as i32;
        self.blocks[bl].intothis.push(BlockEdge::new(source, lab, ourrev));
        self.blocks[source].outofthis.push(BlockEdge::new(bl, lab, brev));
    }

    pub fn block_decode_next_in_edge(
        &mut self,
        bl: BlockId,
        decoder: &mut dyn Decoder,
        resolver: &BlockMap,
    ) -> Result<()> {
        let inedge = BlockEdge::decode(decoder, resolver, &self.blocks)?;
        self.blocks[bl].intothis.push(inedge.clone());
        let intosize = self.blocks[bl].intothis.len() as i32;
        let reverse = inedge.reverse_index as usize;
        let point = inedge.point;
        while self.blocks[point].outofthis.len() <= reverse {
            self.blocks[point].outofthis.push(BlockEdge::new(bl, 0, 0));
        }
        let outedge = &mut self.blocks[point].outofthis[reverse];
        outedge.label = 0;
        outedge.point = bl;
        outedge.reverse_index = intosize - 1;
        Ok(())
    }

    pub fn block_half_delete_in_edge(&mut self, bl: BlockId, slot: i32) {
        let mut slot = slot as usize;
        while slot + 1 < self.blocks[bl].intothis.len() {
            let edge = self.blocks[bl].intothis[slot + 1].clone();
            self.blocks[bl].intothis[slot] = edge.clone();
            self.blocks[edge.point].outofthis[edge.reverse_index as usize].reverse_index -= 1;
            slot += 1;
        }
        self.blocks[bl].intothis.pop();
    }

    pub fn block_half_delete_out_edge(&mut self, bl: BlockId, slot: i32) {
        let mut slot = slot as usize;
        while slot + 1 < self.blocks[bl].outofthis.len() {
            let edge = self.blocks[bl].outofthis[slot + 1].clone();
            self.blocks[bl].outofthis[slot] = edge.clone();
            self.blocks[edge.point].intothis[edge.reverse_index as usize].reverse_index -= 1;
            slot += 1;
        }
        self.blocks[bl].outofthis.pop();
    }

    pub fn block_remove_in_edge(&mut self, bl: BlockId, slot: i32) {
        let edge = self.blocks[bl].intothis[slot as usize].clone();
        self.block_half_delete_in_edge(bl, slot);
        self.block_half_delete_out_edge(edge.point, edge.reverse_index);
    }

    pub fn block_remove_out_edge(&mut self, bl: BlockId, slot: i32) {
        let edge = self.blocks[bl].outofthis[slot as usize].clone();
        self.block_half_delete_out_edge(bl, slot);
        self.block_half_delete_in_edge(edge.point, edge.reverse_index);
    }

    pub fn block_replace_in_edge(&mut self, bl: BlockId, num: i32, source: BlockId) {
        let slot = num as usize;
        let oldedge = self.blocks[bl].intothis[slot].clone();
        self.block_half_delete_out_edge(oldedge.point, oldedge.reverse_index);
        let newrev = self.blocks[source].outofthis.len() as i32;
        let label = {
            let edge = &mut self.blocks[bl].intothis[slot];
            edge.point = source;
            edge.reverse_index = newrev;
            edge.label
        };
        self.blocks[source].outofthis.push(BlockEdge::new(bl, label, num));
    }

    pub fn block_replace_out_edge(&mut self, bl: BlockId, num: i32, source: BlockId) {
        let slot = num as usize;
        let oldedge = self.blocks[bl].outofthis[slot].clone();
        self.block_half_delete_in_edge(oldedge.point, oldedge.reverse_index);
        let newrev = self.blocks[source].intothis.len() as i32;
        let label = {
            let edge = &mut self.blocks[bl].outofthis[slot];
            edge.point = source;
            edge.reverse_index = newrev;
            edge.label
        };
        self.blocks[source].intothis.push(BlockEdge::new(bl, label, num));
    }

    pub fn block_replace_edges_thru(&mut self, bl: BlockId, input: i32, out: i32) {
        let inedge = self.blocks[bl].intothis[input as usize].clone();
        let outedge = self.blocks[bl].outofthis[out as usize].clone();
        let inb = inedge.point;
        let inblock_outslot = inedge.reverse_index;
        let outb = outedge.point;
        let outblock_inslot = outedge.reverse_index;
        {
            let edge = &mut self.blocks[inb].outofthis[inblock_outslot as usize];
            edge.point = outb;
            edge.reverse_index = outblock_inslot;
        }
        {
            let edge = &mut self.blocks[outb].intothis[outblock_inslot as usize];
            edge.point = inb;
            edge.reverse_index = inblock_outslot;
        }
        self.block_half_delete_in_edge(bl, input);
        self.block_half_delete_out_edge(bl, out);
    }

    pub fn block_swap_edges(&mut self, bl: BlockId) {
        self.blocks[bl].outofthis.swap(0, 1);
        let first = self.blocks[bl].outofthis[0].clone();
        self.blocks[first.point].intothis[first.reverse_index as usize].reverse_index = 0;
        let second = self.blocks[bl].outofthis[1].clone();
        self.blocks[second.point].intothis[second.reverse_index as usize].reverse_index = 1;
        self.blocks[bl].flags ^= FlowBlock::F_FLIP_PATH;
    }

    pub fn block_set_out_edge_flag(&mut self, bl: BlockId, index: i32, lab: u32) {
        let edge = {
            let edge = &mut self.blocks[bl].outofthis[index as usize];
            edge.label |= lab;
            edge.clone()
        };
        self.blocks[edge.point].intothis[edge.reverse_index as usize].label |= lab;
    }

    pub fn block_clear_out_edge_flag(&mut self, bl: BlockId, index: i32, lab: u32) {
        let edge = {
            let edge = &mut self.blocks[bl].outofthis[index as usize];
            edge.label &= !lab;
            edge.clone()
        };
        self.blocks[edge.point].intothis[edge.reverse_index as usize].label &= !lab;
    }

    pub fn block_eliminate_in_dups(&mut self, bl: BlockId, dup: BlockId) {
        let mut indval: i32 = -1;
        let mut slot = 0usize;
        while slot < self.blocks[bl].intothis.len() {
            if self.blocks[bl].intothis[slot].point == dup {
                if indval == -1 {
                    indval = slot as i32;
                    slot += 1;
                } else {
                    let label = self.blocks[bl].intothis[slot].label;
                    self.blocks[bl].intothis[indval as usize].label |= label;
                    let rev = self.blocks[bl].intothis[slot].reverse_index;
                    self.block_half_delete_in_edge(bl, slot as i32);
                    self.block_half_delete_out_edge(dup, rev);
                }
            } else {
                slot += 1;
            }
        }
    }

    pub fn block_eliminate_out_dups(&mut self, bl: BlockId, dup: BlockId) {
        let mut indval: i32 = -1;
        let mut slot = 0usize;
        while slot < self.blocks[bl].outofthis.len() {
            if self.blocks[bl].outofthis[slot].point == dup {
                if indval == -1 {
                    indval = slot as i32;
                    slot += 1;
                } else {
                    let label = self.blocks[bl].outofthis[slot].label;
                    self.blocks[bl].outofthis[indval as usize].label |= label;
                    let rev = self.blocks[bl].outofthis[slot].reverse_index;
                    self.block_half_delete_out_edge(bl, slot as i32);
                    self.block_half_delete_in_edge(dup, rev);
                }
            } else {
                slot += 1;
            }
        }
    }

    pub fn block_find_dups(&mut self, reference: &[BlockEdge], duplist: &mut Vec<BlockId>) {
        for edge in reference.iter() {
            let point = edge.point;
            if (self.blocks[point].flags & FlowBlock::F_MARK2) != 0 {
                continue;
            }
            if (self.blocks[point].flags & FlowBlock::F_MARK) != 0 {
                duplist.push(point);
                self.blocks[point].flags |= FlowBlock::F_MARK2;
            } else {
                self.blocks[point].flags |= FlowBlock::F_MARK;
            }
        }
        for edge in reference.iter() {
            self.blocks[edge.point].flags &= !(FlowBlock::F_MARK | FlowBlock::F_MARK2);
        }
    }

    pub fn block_dedup(&mut self, bl: BlockId) {
        let mut duplist = Vec::new();
        let intothis = self.blocks[bl].intothis.clone();
        self.block_find_dups(&intothis, &mut duplist);
        for dup in duplist.iter() {
            self.block_eliminate_in_dups(bl, *dup);
        }
        duplist.clear();
        let outofthis = self.blocks[bl].outofthis.clone();
        self.block_find_dups(&outofthis, &mut duplist);
        for dup in duplist.iter() {
            self.block_eliminate_out_dups(bl, *dup);
        }
    }

    pub fn block_replace_edge_map(&self, vec: &mut [BlockEdge]) {
        for edge in vec.iter_mut() {
            edge.point = self.blocks[edge.point].copymap.expect("block edge without copy map");
        }
    }

    pub fn block_replace_using_map(&mut self, bl: BlockId) {
        let mut intothis = std::mem::take(&mut self.blocks[bl].intothis);
        self.block_replace_edge_map(&mut intothis);
        self.blocks[bl].intothis = intothis;
        let mut outofthis = std::mem::take(&mut self.blocks[bl].outofthis);
        self.block_replace_edge_map(&mut outofthis);
        self.blocks[bl].outofthis = outofthis;
        if let Some(dom) = self.blocks[bl].immed_dom {
            self.blocks[bl].immed_dom = self.blocks[dom].copymap;
        }
    }

    pub fn block_check_edges(&self, bl: BlockId) -> Result<()> {
        let block = &self.blocks[bl];
        for (slot, edge) in block.intothis.iter().enumerate() {
            let rev = edge.reverse_index as usize;
            let other = &self.blocks[edge.point];
            if other.outofthis.len() <= rev {
                return Err(Error::Lowlevel("Not enough outofthis blocks".to_string()));
            }
            let edger = &other.outofthis[rev];
            if edger.point != bl {
                return Err(Error::Lowlevel("Intothis edge mismatch".to_string()));
            }
            if edger.reverse_index != slot as i32 {
                return Err(Error::Lowlevel("Intothis index mismatch".to_string()));
            }
        }
        for (slot, edge) in block.outofthis.iter().enumerate() {
            let rev = edge.reverse_index as usize;
            let other = &self.blocks[edge.point];
            if other.intothis.len() <= rev {
                return Err(Error::Lowlevel("Not enough intothis blocks".to_string()));
            }
            let edger = &other.intothis[rev];
            if edger.point != bl {
                return Err(Error::Lowlevel("Outofthis edge mismatch".to_string()));
            }
            if edger.reverse_index != slot as i32 {
                return Err(Error::Lowlevel("Outofthis index mismatch".to_string()));
            }
        }
        Ok(())
    }

    pub fn block_set_loop_exit(&mut self, bl: BlockId, index: i32) {
        self.block_set_out_edge_flag(bl, index, FlowBlock::F_LOOP_EXIT_EDGE);
    }

    pub fn block_clear_loop_exit(&mut self, bl: BlockId, index: i32) {
        self.block_clear_out_edge_flag(bl, index, FlowBlock::F_LOOP_EXIT_EDGE);
    }

    pub fn block_set_back_edge(&mut self, bl: BlockId, index: i32) {
        self.block_set_out_edge_flag(bl, index, FlowBlock::F_BACK_EDGE);
    }

    pub fn block_set_immed_copy_edge(&mut self, bl: BlockId, index: i32) {
        self.block_set_out_edge_flag(bl, index, FlowBlock::F_IMMED_COPY);
    }

    fn block_graph_mark_unstructured(&mut self, bl: BlockId) {
        let list = self.blocks[bl].list.clone();
        for child in list {
            self.block_mark_unstructured(child);
        }
    }

    pub fn block_mark_unstructured(&mut self, bl: BlockId) {
        match self.blocks[bl].kind.clone() {
            BlockKind::Plain | BlockKind::Basic(_) | BlockKind::Copy { .. } => {}
            BlockKind::Goto { gototarget, gototype } => {
                self.block_graph_mark_unstructured(bl);
                if gototype == FlowBlock::F_GOTO_GOTO && self.block_goto_prints(bl) {
                    self.block_mark_copy_block(gototarget, FlowBlock::F_UNSTRUCTURED_TARG);
                }
            }
            BlockKind::IfGoto { gototype, gototarget } => {
                self.block_graph_mark_unstructured(bl);
                if gototype == FlowBlock::F_GOTO_GOTO {
                    self.block_mark_copy_block(gototarget, FlowBlock::F_UNSTRUCTURED_TARG);
                }
            }
            BlockKind::Switch { caseblocks, .. } => {
                self.block_graph_mark_unstructured(bl);
                for case in caseblocks.iter() {
                    if case.gototype == FlowBlock::F_GOTO_GOTO {
                        self.block_mark_copy_block(case.block, FlowBlock::F_UNSTRUCTURED_TARG);
                    }
                }
            }
            _ => self.block_graph_mark_unstructured(bl),
        }
    }

    fn block_mark_label_bump_up_base(&mut self, bl: BlockId, bump: bool) {
        if bump {
            self.blocks[bl].flags |= FlowBlock::F_LABEL_BUMPUP;
        }
    }

    fn block_graph_mark_label_bump_up(&mut self, bl: BlockId, bump: bool) {
        self.block_mark_label_bump_up_base(bl, bump);
        let list = self.blocks[bl].list.clone();
        if list.is_empty() {
            return;
        }
        self.block_mark_label_bump_up(list[0], bump);
        for child in list.iter().skip(1) {
            self.block_mark_label_bump_up(*child, false);
        }
    }

    pub fn block_mark_label_bump_up(&mut self, bl: BlockId, bump: bool) {
        match &self.blocks[bl].kind {
            BlockKind::Plain | BlockKind::Basic(_) | BlockKind::Copy { .. } => {
                self.block_mark_label_bump_up_base(bl, bump)
            }
            BlockKind::WhileDo { .. } | BlockKind::DoWhile | BlockKind::InfLoop => {
                self.block_graph_mark_label_bump_up(bl, true);
                if !bump {
                    self.blocks[bl].clear_flag(FlowBlock::F_LABEL_BUMPUP);
                }
            }
            _ => self.block_graph_mark_label_bump_up(bl, bump),
        }
    }

    pub fn block_scope_break(&mut self, bl: BlockId, curexit: i32, curloopexit: i32) {
        let list = self.blocks[bl].list.clone();
        match self.blocks[bl].kind.clone() {
            BlockKind::Plain | BlockKind::Basic(_) | BlockKind::Copy { .. } => {}
            BlockKind::Goto { gototarget, .. } => {
                let targetindex = self.blocks[gototarget].index;
                self.block_scope_break(list[0], targetindex, curloopexit);
                if curloopexit == targetindex
                    && let BlockKind::Goto { gototype, .. } = &mut self.blocks[bl].kind
                {
                    *gototype = FlowBlock::F_BREAK_GOTO;
                }
            }
            BlockKind::MultiGoto { .. } => self.block_scope_break(list[0], -1, curloopexit),
            BlockKind::Condition { .. } => {
                self.block_scope_break(list[0], -1, curloopexit);
                self.block_scope_break(list[1], -1, curloopexit);
            }
            BlockKind::If => {
                self.block_scope_break(list[0], -1, curloopexit);
                self.block_scope_break(list[1], curexit, curloopexit);
            }
            BlockKind::IfElse => {
                self.block_scope_break(list[0], -1, curloopexit);
                self.block_scope_break(list[1], curexit, curloopexit);
                self.block_scope_break(list[2], curexit, curloopexit);
            }
            BlockKind::IfNoExit => {
                self.block_scope_break(list[0], -1, curloopexit);
                let follow_block = list[2];
                let followindex = self.blocks[follow_block].index;
                self.block_scope_break(list[1], followindex, curloopexit);
                self.block_scope_break(follow_block, curexit, curloopexit);
            }
            BlockKind::IfGoto { gototarget, .. } => {
                self.block_scope_break(list[0], -1, curloopexit);
                if self.blocks[gototarget].index == curloopexit
                    && let BlockKind::IfGoto { gototype, .. } = &mut self.blocks[bl].kind
                {
                    *gototype = FlowBlock::F_BREAK_GOTO;
                }
            }
            BlockKind::WhileDo { .. } => {
                self.block_scope_break(list[0], -1, curexit);
                let topindex = self.blocks[list[0]].index;
                self.block_scope_break(list[1], topindex, curexit);
            }
            BlockKind::DoWhile => self.block_scope_break(list[0], -1, curexit),
            BlockKind::InfLoop => {
                let topindex = self.blocks[list[0]].index;
                self.block_scope_break(list[0], topindex, curexit);
            }
            BlockKind::Switch { caseblocks, .. } => {
                self.block_scope_break(list[0], -1, curexit);
                for (slot, case) in caseblocks.iter().enumerate() {
                    let casebl = case.block;
                    if case.gototype != 0 {
                        if self.blocks[casebl].index == curexit
                            && let BlockKind::Switch { caseblocks, .. } = &mut self.blocks[bl].kind
                        {
                            caseblocks[slot].gototype = FlowBlock::F_BREAK_GOTO;
                        }
                    } else {
                        self.block_scope_break(casebl, curexit, curexit);
                    }
                }
            }
            BlockKind::Graph | BlockKind::List => {
                for (slot, child) in list.iter().enumerate() {
                    let ind = if slot + 1 == list.len() {
                        curexit
                    } else {
                        self.blocks[list[slot + 1]].index
                    };
                    self.block_scope_break(*child, ind, curloopexit);
                }
            }
        }
    }

    fn block_print_header_base(&self, bl: BlockId, stream: &mut String) {
        let block = &self.blocks[bl];
        let _ = write!(stream, "{}", block.index);
        let start = block.get_start();
        let stop = block.get_stop();
        if !start.is_invalid() && !stop.is_invalid() {
            let _ = write!(stream, " {}-{}", start, stop);
        }
    }

    pub fn block_print_header(&self, bl: BlockId, stream: &mut String) {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Basic(_) => stream.push_str("Basic Block "),
            BlockKind::Copy { .. } => stream.push_str("Basic(copy) block "),
            BlockKind::Goto { .. } => stream.push_str("Plain goto block "),
            BlockKind::MultiGoto { .. } => stream.push_str("Multi goto block "),
            BlockKind::List => stream.push_str("List block "),
            BlockKind::Condition { opc } => {
                stream.push_str("Condition block(");
                if *opc == OpCode::BoolAnd {
                    stream.push_str("&&");
                } else {
                    stream.push_str("||");
                }
                stream.push_str(") ");
            }
            BlockKind::If => stream.push_str("If block "),
            BlockKind::IfElse => stream.push_str("If/else block "),
            BlockKind::IfNoExit => stream.push_str("If (no exit) block "),
            BlockKind::IfGoto { .. } => stream.push_str("If goto block "),
            BlockKind::WhileDo { .. } => {
                stream.push_str("Whiledo block ");
                if block.has_overflow_syntax() {
                    stream.push_str("(overflow) ");
                }
            }
            BlockKind::DoWhile => stream.push_str("Dowhile block "),
            BlockKind::InfLoop => stream.push_str("Infinite loop block "),
            BlockKind::Switch { .. } => stream.push_str("Switch block "),
            BlockKind::Plain | BlockKind::Graph => {}
        }
        self.block_print_header_base(bl, stream);
    }

    fn block_print_tree_base(&self, bl: BlockId, stream: &mut String, level: i32) {
        for _ in 0..level {
            stream.push_str("  ");
        }
        self.block_print_header(bl, stream);
        stream.push('\n');
    }

    pub fn block_print_tree(&self, bl: BlockId, stream: &mut String, level: i32) {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Plain | BlockKind::Basic(_) => self.block_print_tree_base(bl, stream, level),
            BlockKind::Copy { copy } => {
                self.block_print_tree(copy.expect("copy block without copied block"), stream, level)
            }
            _ => {
                self.block_print_tree_base(bl, stream, level);
                for child in block.list.iter() {
                    self.block_print_tree(*child, stream, level + 1);
                }
            }
        }
    }

    pub fn block_print_raw(&self, bl: BlockId, stream: &mut String, glb: &mut Architecture) {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Plain => {}
            BlockKind::Basic(data) => {
                self.block_print_header(bl, stream);
                stream.push('\n');
                for inst in data.op.iter(&self.obank.ops) {
                    let _ = write!(stream, "{}:\t", self.op(inst).get_seq_num());
                    self.op_print_raw(inst, stream, glb);
                    stream.push('\n');
                }
            }
            BlockKind::Copy { copy } => {
                self.block_print_raw(copy.expect("copy block without copied block"), stream, glb)
            }
            BlockKind::Goto { .. } | BlockKind::MultiGoto { .. } => {
                self.block_print_raw(block.get_block(0), stream, glb)
            }
            _ => {
                self.block_print_header(bl, stream);
                stream.push('\n');
                let list = &block.list;
                if list.is_empty() {
                    return;
                }
                let mut last_bl = list[0];
                self.block_print_raw(last_bl, stream, glb);
                for cur_bl in list.iter().skip(1) {
                    self.block_print_raw_implied_goto(last_bl, stream, Some(*cur_bl));
                    self.block_print_raw(*cur_bl, stream, glb);
                    last_bl = *cur_bl;
                }
            }
        }
    }

    pub fn block_print_raw_implied_goto(&self, bl: BlockId, stream: &mut String, next_block: Option<BlockId>) {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Plain => {}
            BlockKind::Basic(data) => {
                if block.size_out() != 1 {
                    return;
                }
                let out_block = block.get_out(0);
                let mut next = next_block.expect("implied goto without next block");
                let mut next_basic = Some(next);
                if self.blocks[next].get_type() != BlockType::Basic {
                    match self.block_get_front_leaf(next) {
                        None => return,
                        Some(leaf) => next = leaf,
                    }
                    next_basic = self.blocks[next].sub_block(0);
                }
                if Some(block.get_out(0)) == next_basic {
                    return;
                }
                if let Some(last) = data.op.back()
                    && self.op(last).is_branch()
                {
                    return;
                }
                block.get_stop().print_raw(stream);
                stream.push_str(":   \t[ goto ");
                self.blocks[out_block].print_short_header(stream);
                stream.push_str(" ]\n");
            }
            BlockKind::Copy { copy } => {
                self.block_print_raw_implied_goto(copy.expect("copy block without copied block"), stream, next_block)
            }
            _ => {
                if let Some(last) = block.list.last() {
                    self.block_print_raw_implied_goto(*last, stream, next_block);
                }
            }
        }
    }

    pub fn block_emit(bl: BlockId, lng: &mut dyn PrintLanguage, ctx: &mut PrintContext<'_>) -> Result<()> {
        let data = ctx.data.as_deref().expect("block emission without a function");
        let block = &data.blocks[bl];
        match &block.kind {
            BlockKind::Plain => Ok(()),
            BlockKind::Basic(_) => lng.emit_block_basic(ctx, bl),
            BlockKind::Graph => lng.emit_block_graph(ctx, bl),
            BlockKind::Copy { .. } => lng.emit_block_copy(ctx, bl),
            BlockKind::Goto { .. } => lng.emit_block_goto(ctx, bl),
            BlockKind::MultiGoto { .. } => {
                let first = block.get_block(0);
                Funcdata::block_emit(first, lng, ctx)
            }
            BlockKind::List => lng.emit_block_ls(ctx, bl),
            BlockKind::Condition { .. } => lng.emit_block_condition(ctx, bl),
            BlockKind::If | BlockKind::IfElse | BlockKind::IfNoExit | BlockKind::IfGoto { .. } => {
                lng.emit_block_if(ctx, bl)
            }
            BlockKind::WhileDo { .. } => lng.emit_block_while_do(ctx, bl),
            BlockKind::DoWhile => lng.emit_block_do_while(ctx, bl),
            BlockKind::InfLoop => lng.emit_block_inf_loop(ctx, bl),
            BlockKind::Switch { .. } => lng.emit_block_switch(ctx, bl),
        }
    }

    pub fn block_get_exit_leaf(&self, bl: BlockId) -> Option<BlockId> {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Basic(_) | BlockKind::Copy { .. } => Some(bl),
            BlockKind::Goto { .. } | BlockKind::MultiGoto { .. } | BlockKind::IfGoto { .. } => {
                self.block_get_exit_leaf(block.get_block(0))
            }
            BlockKind::List => match block.list.last() {
                None => None,
                Some(last) => self.block_get_exit_leaf(*last),
            },
            _ => None,
        }
    }

    pub fn block_first_op(&self, bl: BlockId) -> Option<OpId> {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Plain => None,
            BlockKind::Basic(data) => data.op.front(),
            BlockKind::Copy { copy } => self.block_first_op(copy.expect("copy block without copied block")),
            _ => match block.list.first() {
                None => None,
                Some(first) => self.block_first_op(*first),
            },
        }
    }

    pub fn block_last_op(&self, bl: BlockId) -> Option<OpId> {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Basic(data) => data.op.back(),
            BlockKind::Copy { copy } => self.block_last_op(copy.expect("copy block without copied block")),
            BlockKind::Goto { .. } | BlockKind::MultiGoto { .. } | BlockKind::IfGoto { .. } => {
                self.block_last_op(block.get_block(0))
            }
            BlockKind::List => match block.list.last() {
                None => None,
                Some(last) => self.block_last_op(*last),
            },
            BlockKind::Condition { .. } => self.block_last_op(block.get_block(1)),
            BlockKind::IfNoExit => self.block_last_op(block.get_block(2)),
            _ => None,
        }
    }

    pub fn block_negate_condition(&mut self, bl: BlockId, toporbottom: bool) -> bool {
        match self.blocks[bl].kind.clone() {
            BlockKind::Basic(data) => {
                let lastop = data.op.back().expect("negating condition of empty basic block");
                self.op_mut(lastop).flip_flag(PcodeOp::BOOLEAN_FLIP);
                self.op_mut(lastop).flip_flag(PcodeOp::FALLTHRU_TRUE);
                self.block_negate_condition_base(bl, true);
                true
            }
            BlockKind::Copy { copy } => {
                let copied = copy.expect("copy block without copied block");
                let res = self.block_negate_condition(copied, true);
                self.block_negate_condition_base(bl, toporbottom);
                res
            }
            BlockKind::List => {
                let last = *self.blocks[bl]
                    .list
                    .last()
                    .expect("negating condition of empty list block");
                let res = self.block_negate_condition(last, false);
                self.block_negate_condition_base(bl, toporbottom);
                res
            }
            BlockKind::Condition { .. } => {
                let first = self.blocks[bl].get_block(0);
                let second = self.blocks[bl].get_block(1);
                let res1 = self.block_negate_condition(first, false);
                let res2 = self.block_negate_condition(second, false);
                self.block_toggle_condition_opcode(bl);
                self.block_negate_condition_base(bl, toporbottom);
                res1 || res2
            }
            _ => self.block_negate_condition_base(bl, toporbottom),
        }
    }

    fn block_toggle_condition_opcode(&mut self, bl: BlockId) {
        if let BlockKind::Condition { opc } = &mut self.blocks[bl].kind {
            *opc = if *opc == OpCode::BoolAnd {
                OpCode::BoolOr
            } else {
                OpCode::BoolAnd
            };
        }
    }

    pub fn block_negate_condition_base(&mut self, bl: BlockId, toporbottom: bool) -> bool {
        if !toporbottom {
            return false;
        }
        self.block_swap_edges(bl);
        false
    }

    pub fn block_prefer_complement(
        &mut self,
        bl: BlockId,
        allow_op_removal: bool,
        glb: &mut Architecture,
    ) -> Result<bool> {
        match &self.blocks[bl].kind {
            BlockKind::IfElse => {
                let first = self.blocks[bl].get_block(0);
                let split = match self.block_get_split_point(first) {
                    None => return Ok(false),
                    Some(split) => split,
                };
                let mut fliplist = Vec::new();
                if 0 != self.block_flip_in_place_test(split, &mut fliplist, allow_op_removal) {
                    return Ok(false);
                }
                self.block_flip_in_place_execute(split);
                self.op_flip_in_place_execute(&fliplist, glb)?;
                self.block_swap_blocks(bl, 1, 2);
                Ok(true)
            }
            BlockKind::IfNoExit => {
                let body1 = self.blocks[bl].get_block(1);
                let body2 = self.blocks[bl].get_block(2);
                let mut diff = self.blocks[body1].get_structure_depth() - self.blocks[body2].get_structure_depth();
                if diff < 0 {
                    return Ok(false);
                }
                if diff == 0 {
                    diff = self.blocks[body1].get_basic_count() - self.blocks[body2].get_basic_count();
                    if diff < 0 {
                        return Ok(false);
                    }
                    if diff == 0 {
                        let halt1 = self.block_get_halt_type(body1);
                        let halt2 = self.block_get_halt_type(body2);
                        if halt1 > halt2 {
                            return Ok(false);
                        }
                        if halt1 < halt2 {
                            diff = 1;
                        }
                    }
                }
                let first = self.blocks[bl].get_block(0);
                let split = match self.block_get_split_point(first) {
                    None => return Ok(false),
                    Some(split) => split,
                };
                let mut fliplist = Vec::new();
                let test_result = self.block_flip_in_place_test(split, &mut fliplist, allow_op_removal);
                if test_result == 2 {
                    return Ok(false);
                }
                if diff == 0 && test_result != 0 {
                    return Ok(false);
                }
                self.block_flip_in_place_execute(split);
                self.op_flip_in_place_execute(&fliplist, glb)?;
                self.block_swap_blocks(bl, 1, 2);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub fn block_get_split_point(&self, bl: BlockId) -> Option<BlockId> {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Basic(_) => {
                if block.size_out() != 2 {
                    None
                } else {
                    Some(bl)
                }
            }
            BlockKind::Copy { copy } => self.block_get_split_point(copy.expect("copy block without copied block")),
            BlockKind::List => match block.list.last() {
                None => None,
                Some(last) => self.block_get_split_point(*last),
            },
            BlockKind::Condition { .. } => Some(bl),
            _ => None,
        }
    }

    pub fn block_flip_in_place_test(&self, bl: BlockId, fliplist: &mut Vec<OpId>, allow_op_removal: bool) -> i32 {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Basic(data) => {
                let lastop = match data.op.back() {
                    None => return 2,
                    Some(lastop) => lastop,
                };
                if self.op(lastop).code() != OpCode::Cbranch {
                    return 2;
                }
                if self.op(lastop).is_boolean_flip() {
                    let mut unused_ops = Vec::new();
                    self.op_flip_in_place_test(lastop, &mut unused_ops, allow_op_removal)
                } else {
                    self.op_flip_in_place_test(lastop, fliplist, allow_op_removal)
                }
            }
            BlockKind::Condition { .. } => {
                let split1 = match self.block_get_split_point(block.get_block(0)) {
                    None => return 2,
                    Some(split) => split,
                };
                let split2 = match self.block_get_split_point(block.get_block(1)) {
                    None => return 2,
                    Some(split) => split,
                };
                let subtest1 = self.block_flip_in_place_test(split1, fliplist, allow_op_removal);
                if subtest1 == 2 {
                    return 2;
                }
                let subtest2 = self.block_flip_in_place_test(split2, fliplist, allow_op_removal);
                if subtest2 == 2 {
                    return 2;
                }
                subtest1
            }
            _ => 2,
        }
    }

    pub fn block_flip_in_place_execute(&mut self, bl: BlockId) {
        match self.blocks[bl].kind.clone() {
            BlockKind::Basic(data) => {
                let lastop = data.op.back().expect("flipping empty basic block");
                self.op_mut(lastop).flip_flag(PcodeOp::FALLTHRU_TRUE);
                if self.op(lastop).is_boolean_flip() {
                    self.op_mut(lastop).flip_flag(PcodeOp::BOOLEAN_FLIP);
                }
                self.block_negate_condition_base(bl, true);
            }
            BlockKind::Condition { .. } => {
                self.block_toggle_condition_opcode(bl);
                let first = self.blocks[bl].get_block(0);
                let second = self.blocks[bl].get_block(1);
                let split1 = self
                    .block_get_split_point(first)
                    .expect("condition block without split point");
                self.block_flip_in_place_execute(split1);
                let split2 = self
                    .block_get_split_point(second)
                    .expect("condition block without split point");
                self.block_flip_in_place_execute(split2);
            }
            _ => {}
        }
    }

    pub fn block_is_complex(&self, bl: BlockId, glb: &Architecture) -> bool {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Basic(data) => {
                let mut statement = 0;
                if block.size_out() >= 2 {
                    statement = 1;
                }
                let maxref = glb.max_implied_ref;
                for inst in data.op.iter(&self.obank.ops) {
                    let instop = self.op(inst);
                    if instop.is_marker() {
                        continue;
                    }
                    let outvn = instop.get_out();
                    if instop.is_call() {
                        statement += 1;
                    } else {
                        match outvn {
                            None => {
                                if instop.is_flow_break() {
                                    continue;
                                }
                                statement += 1;
                            }
                            Some(vn) => {
                                let varnode = self.vn(vn);
                                let mut yesstatement = false;
                                if varnode.has_no_descend() || varnode.is_addr_tied() {
                                    yesstatement = true;
                                } else {
                                    let mut totalref = 0;
                                    for d_op in varnode.descend().iter() {
                                        let descop = self.op(*d_op);
                                        if descop.is_marker() || descop.get_parent() != Some(bl) {
                                            yesstatement = true;
                                            break;
                                        }
                                        totalref += 1;
                                        if totalref > maxref {
                                            yesstatement = true;
                                            break;
                                        }
                                    }
                                }
                                if yesstatement {
                                    statement += 1;
                                }
                            }
                        }
                    }
                    if statement > 2 {
                        return true;
                    }
                }
                false
            }
            BlockKind::Copy { copy } => self.block_is_complex(copy.expect("copy block without copied block"), glb),
            BlockKind::Condition { .. } => self.block_is_complex(block.get_block(0), glb),
            _ => true,
        }
    }

    pub fn block_next_flow_after(&self, bl: BlockId, sub: BlockId) -> Option<BlockId> {
        let block = &self.blocks[bl];
        match &block.kind {
            BlockKind::Plain | BlockKind::Basic(_) | BlockKind::Copy { .. } => None,
            BlockKind::Goto { gototarget, .. } => self.block_get_front_leaf(*gototarget),
            BlockKind::MultiGoto { .. } => None,
            BlockKind::Condition { .. } => None,
            BlockKind::If | BlockKind::IfElse | BlockKind::IfNoExit | BlockKind::IfGoto { .. } => {
                if block.get_block(0) == sub {
                    return None;
                }
                match block.parent {
                    None => None,
                    Some(parent) => self.block_next_flow_after(parent, bl),
                }
            }
            BlockKind::WhileDo { .. } => {
                if block.get_block(0) == sub {
                    return None;
                }
                self.block_get_front_leaf(block.get_block(0))
            }
            BlockKind::DoWhile => None,
            BlockKind::InfLoop => self.block_get_front_leaf(block.get_block(0)),
            BlockKind::Switch { caseblocks, .. } => {
                if block.get_block(0) == sub {
                    return None;
                }
                if self.blocks[sub].get_type() != BlockType::Goto {
                    return None;
                }
                let position = caseblocks.iter().position(|case| case.block == sub)?;
                let next = position + 1;
                if next < caseblocks.len() {
                    return self.block_get_front_leaf(caseblocks[next].block);
                }
                match block.parent {
                    None => None,
                    Some(parent) => self.block_next_flow_after(parent, bl),
                }
            }
            BlockKind::Graph | BlockKind::List => {
                let next = match block.list.iter().position(|child| *child == sub) {
                    None => block.list.len(),
                    Some(position) => position + 1,
                };
                if next >= block.list.len() {
                    return match block.parent {
                        None => None,
                        Some(parent) => self.block_next_flow_after(parent, bl),
                    };
                }
                self.block_get_front_leaf(block.list[next])
            }
        }
    }

    fn block_graph_final_transform(&mut self, bl: BlockId, allow_op_moves: bool, glb: &mut Architecture) -> Result<()> {
        if self.blocks[bl].has_final_transform() {
            return Ok(());
        }
        let list = self.blocks[bl].list.clone();
        for child in list {
            self.block_final_transform(child, allow_op_moves, glb)?;
        }
        self.blocks[bl].set_flag(FlowBlock::F_FINAL_TRANSFORM);
        Ok(())
    }

    pub fn block_final_transform(&mut self, bl: BlockId, allow_op_moves: bool, glb: &mut Architecture) -> Result<()> {
        match self.blocks[bl].kind.clone() {
            BlockKind::Plain => Ok(()),
            BlockKind::Basic(_) => {
                if self.blocks[bl].size_out() != 2 {
                    return Ok(());
                }
                let cbranch = match self.block_last_op(bl) {
                    None => return Ok(()),
                    Some(cbranch) => cbranch,
                };
                if self.op(cbranch).code() != OpCode::Cbranch {
                    return Ok(());
                }
                if !self.op(cbranch).is_boolean_flip() {
                    return Ok(());
                }
                self.op_normalize_flip(cbranch, glb)?;
                Ok(())
            }
            BlockKind::Copy { copy } => {
                let copied = copy.expect("copy block without copied block");
                self.block_final_transform(copied, allow_op_moves, glb)
            }
            BlockKind::WhileDo { .. } => self.block_while_do_final_transform(bl, allow_op_moves, glb),
            _ => self.block_graph_final_transform(bl, allow_op_moves, glb),
        }
    }

    fn block_graph_finalize_printing(&mut self, bl: BlockId, glb: &mut Architecture) -> Result<()> {
        let list = self.blocks[bl].list.clone();
        for child in list {
            self.block_finalize_printing(child, glb)?;
        }
        Ok(())
    }

    pub fn block_finalize_printing(&mut self, bl: BlockId, glb: &mut Architecture) -> Result<()> {
        match &self.blocks[bl].kind {
            BlockKind::Plain | BlockKind::Basic(_) | BlockKind::Copy { .. } => Ok(()),
            BlockKind::WhileDo { .. } => self.block_while_do_finalize_printing(bl, glb),
            BlockKind::Switch { .. } => self.block_switch_finalize_printing(bl, glb),
            _ => self.block_graph_finalize_printing(bl, glb),
        }
    }

    fn block_encode_header_base(&self, bl: BlockId, encoder: &mut dyn Encoder) {
        encoder.write_signed_integer(ATTRIB_INDEX, self.blocks[bl].index as i64);
    }

    pub fn block_encode_header(&self, bl: BlockId, encoder: &mut dyn Encoder) -> Result<()> {
        self.block_encode_header_base(bl, encoder);
        match &self.blocks[bl].kind {
            BlockKind::Copy { copy } => {
                let altindex = self.blocks[copy.expect("copy block without copied block")].index;
                encoder.write_signed_integer(ATTRIB_ALTINDEX, altindex as i64);
            }
            BlockKind::Condition { opc } => {
                encoder.write_string(ATTRIB_OPCODE, get_opname(*opc));
            }
            _ => {}
        }
        Ok(())
    }

    pub fn block_decode_header(&mut self, bl: BlockId, decoder: &mut dyn Decoder) -> Result<()> {
        self.blocks[bl].index = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
        Ok(())
    }

    fn block_graph_encode_body(&self, bl: BlockId, encoder: &mut dyn Encoder) -> Result<()> {
        let list = &self.blocks[bl].list;
        for child in list.iter() {
            let childblock = &self.blocks[*child];
            encoder.open_element(ELEM_BHEAD);
            encoder.write_signed_integer(ATTRIB_INDEX, childblock.get_index() as i64);
            let nm = FlowBlock::type_to_name(childblock.get_type());
            encoder.write_string(ATTRIB_TYPE, &nm);
            encoder.close_element(ELEM_BHEAD);
        }
        for child in list.iter() {
            self.block_encode(*child, encoder)?;
        }
        Ok(())
    }

    fn block_encode_goto_target(&self, gototarget: BlockId, gototype: Option<u32>, encoder: &mut dyn Encoder) {
        let leaf = self
            .block_get_front_leaf(gototarget)
            .expect("goto target without leaf block");
        let depth = self.block_calc_depth(gototarget, leaf);
        encoder.open_element(ELEM_TARGET);
        encoder.write_signed_integer(ATTRIB_INDEX, self.blocks[leaf].get_index() as i64);
        encoder.write_signed_integer(ATTRIB_DEPTH, depth as i64);
        if let Some(gototype) = gototype {
            encoder.write_unsigned_integer(ATTRIB_TYPE, gototype as u64);
        }
        encoder.close_element(ELEM_TARGET);
    }

    pub fn block_encode_body(&self, bl: BlockId, encoder: &mut dyn Encoder) -> Result<()> {
        match &self.blocks[bl].kind {
            BlockKind::Plain | BlockKind::Copy { .. } => Ok(()),
            BlockKind::Basic(data) => {
                data.cover.encode(encoder);
                Ok(())
            }
            BlockKind::Goto { gototarget, gototype } => {
                self.block_graph_encode_body(bl, encoder)?;
                self.block_encode_goto_target(*gototarget, Some(*gototype), encoder);
                Ok(())
            }
            BlockKind::MultiGoto { gotoedges, .. } => {
                self.block_graph_encode_body(bl, encoder)?;
                for gototarget in gotoedges.iter() {
                    self.block_encode_goto_target(*gototarget, None, encoder);
                }
                Ok(())
            }
            BlockKind::IfGoto { gototype, gototarget } => {
                self.block_graph_encode_body(bl, encoder)?;
                self.block_encode_goto_target(*gototarget, Some(*gototype), encoder);
                Ok(())
            }
            _ => self.block_graph_encode_body(bl, encoder),
        }
    }

    pub fn block_decode_body(&mut self, bl: BlockId, decoder: &mut dyn Decoder) -> Result<()> {
        match &self.blocks[bl].kind {
            BlockKind::Plain | BlockKind::Copy { .. } => Ok(()),
            BlockKind::Basic(_) => self.blocks[bl].basic_mut().cover.decode(decoder),
            _ => {
                let mut newresolver = BlockMap::new();
                let mut tmplist = Vec::new();
                loop {
                    let sub_id = decoder.peek_element()?;
                    if sub_id != ELEM_BHEAD {
                        break;
                    }
                    decoder.open_element()?;
                    let newindex = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
                    let name = decoder.read_string_attr(ATTRIB_TYPE)?;
                    let newbl = newresolver
                        .create_block(&name, &mut self.blocks)
                        .expect("block type without factory");
                    self.blocks[newbl].index = newindex;
                    tmplist.push(newbl);
                    decoder.close_element(sub_id)?;
                }
                newresolver.sort_list(&self.blocks);
                for child in tmplist {
                    self.block_decode(child, decoder, &newresolver)?;
                    self.block_add_block(bl, child);
                }
                Ok(())
            }
        }
    }

    pub fn block_encode_edges(&self, bl: BlockId, encoder: &mut dyn Encoder) -> Result<()> {
        for edge in self.blocks[bl].intothis.iter() {
            edge.encode(encoder, &self.blocks)?;
        }
        Ok(())
    }

    pub fn block_decode_edges(&mut self, bl: BlockId, decoder: &mut dyn Decoder, resolver: &BlockMap) -> Result<()> {
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id != ELEM_EDGE {
                break;
            }
            self.block_decode_next_in_edge(bl, decoder, resolver)?;
        }
        Ok(())
    }

    pub fn block_encode(&self, bl: BlockId, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_BLOCK);
        self.block_encode_header(bl, encoder)?;
        self.block_encode_body(bl, encoder)?;
        self.block_encode_edges(bl, encoder)?;
        encoder.close_element(ELEM_BLOCK);
        Ok(())
    }

    pub fn block_decode(&mut self, bl: BlockId, decoder: &mut dyn Decoder, resolver: &BlockMap) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_BLOCK)?;
        self.block_decode_header(bl, decoder)?;
        self.block_decode_body(bl, decoder)?;
        self.block_decode_edges(bl, decoder, resolver)?;
        decoder.close_element(elem_id)?;
        Ok(())
    }

    pub fn block_next_in_flow(&self, bl: BlockId) -> Option<BlockId> {
        let block = &self.blocks[bl];
        if block.size_out() == 1 {
            return Some(block.get_out(0));
        }
        if block.size_out() == 2 {
            let op = self.block_last_op(bl)?;
            if self.op(op).code() != OpCode::Cbranch {
                return None;
            }
            return if self.op(op).is_fallthru_true() {
                Some(block.get_out(1))
            } else {
                Some(block.get_out(0))
            };
        }
        None
    }

    pub fn block_set_goto_branch(&mut self, bl: BlockId, index: i32) -> Result<()> {
        if index >= 0 && index < self.blocks[bl].size_out() {
            self.block_set_out_edge_flag(bl, index, FlowBlock::F_GOTO_EDGE);
        } else {
            return Err(Error::Lowlevel(
                "Could not find block edge to mark unstructured".to_string(),
            ));
        }
        self.blocks[bl].flags |= FlowBlock::F_INTERIOR_GOTOOUT;
        let target = self.blocks[bl].get_out(index);
        self.blocks[target].flags |= FlowBlock::F_INTERIOR_GOTOIN;
        Ok(())
    }

    pub fn block_set_default_switch(&mut self, bl: BlockId, pos: i32) {
        for slot in 0..self.blocks[bl].size_out() {
            if self.blocks[bl].is_default_branch(slot) {
                self.block_clear_out_edge_flag(bl, slot, FlowBlock::F_DEFAULTSWITCH_EDGE);
            }
        }
        self.block_set_out_edge_flag(bl, pos, FlowBlock::F_DEFAULTSWITCH_EDGE);
    }

    pub fn block_is_jump_target(&self, bl: BlockId) -> bool {
        let block = &self.blocks[bl];
        block
            .intothis
            .iter()
            .any(|edge| self.blocks[edge.point].index != block.index - 1)
    }

    pub fn block_get_front_leaf(&self, bl: BlockId) -> Option<BlockId> {
        let mut cur = bl;
        while self.blocks[cur].get_type() != BlockType::Copy {
            cur = self.blocks[cur].sub_block(0)?;
        }
        Some(cur)
    }

    pub fn block_calc_depth(&self, bl: BlockId, leaf: BlockId) -> i32 {
        let mut depth = 0;
        let mut cur = Some(leaf);
        while cur != Some(bl) {
            match cur {
                None => return -1,
                Some(block) => cur = self.blocks[block].parent,
            }
            depth += 1;
        }
        depth
    }

    pub fn block_dominates(&self, bl: BlockId, sub_block: BlockId) -> bool {
        let index = self.blocks[bl].index;
        let mut cur = Some(sub_block);
        while let Some(block) = cur {
            if index > self.blocks[block].index {
                break;
            }
            if block == bl {
                return true;
            }
            cur = self.blocks[block].immed_dom;
        }
        false
    }

    pub fn block_restricted_by_conditional(&self, bl: BlockId, cond: BlockId) -> bool {
        let block = &self.blocks[bl];
        if block.size_in() == 1 {
            return true;
        }
        if block.immed_dom != Some(cond) {
            return false;
        }
        let mut seen_cond = false;
        for slot in 0..block.size_in() {
            let mut in_block = block.get_in(slot);
            if in_block == cond {
                if seen_cond {
                    return false;
                }
                seen_cond = true;
                continue;
            }
            while in_block != bl {
                if in_block == cond {
                    return false;
                }
                in_block = self.blocks[in_block]
                    .immed_dom
                    .expect("block without immediate dominator");
            }
        }
        true
    }

    pub fn block_get_jumptable(&self, bl: BlockId) -> Option<JumpTableId> {
        if !self.blocks[bl].is_switch_out() {
            return None;
        }
        let indop = self.block_last_op(bl)?;
        self.find_jump_table(indop)
    }

    pub fn block_get_halt_type(&self, bl: BlockId) -> u32 {
        match self.block_last_op(bl) {
            Some(op) => self.op(op).get_halt_type(),
            None => 0,
        }
    }

    pub fn block_compare_final_order(&self, bl1: BlockId, bl2: BlockId) -> bool {
        if self.blocks[bl1].index == 0 {
            return true;
        }
        if self.blocks[bl2].index == 0 {
            return false;
        }
        let op1 = self.block_last_op(bl1);
        let op2 = self.block_last_op(bl2);
        match op1 {
            Some(first) => {
                let code1 = self.op(first).code();
                if let Some(second) = op2 {
                    let code2 = self.op(second).code();
                    if code1 == OpCode::Return && code2 != OpCode::Return {
                        return false;
                    } else if code1 != OpCode::Return && code2 == OpCode::Return {
                        return true;
                    }
                }
                if code1 == OpCode::Return {
                    return false;
                }
            }
            None => {
                if let Some(second) = op2
                    && self.op(second).code() == OpCode::Return
                {
                    return true;
                }
            }
        }
        self.blocks[bl1].index < self.blocks[bl2].index
    }

    pub fn block_find_common_block(&mut self, bl1: BlockId, bl2: BlockId) -> Option<BlockId> {
        let mut common = None;
        let mut b1 = Some(bl1);
        let mut b2 = Some(bl2);
        loop {
            let second = match b2 {
                None => {
                    while let Some(first) = b1 {
                        if self.blocks[first].is_mark() {
                            common = Some(first);
                            break;
                        }
                        b1 = self.blocks[first].immed_dom;
                    }
                    break;
                }
                Some(second) => second,
            };
            let first = match b1 {
                None => {
                    let mut cur = Some(second);
                    while let Some(block) = cur {
                        if self.blocks[block].is_mark() {
                            common = Some(block);
                            break;
                        }
                        cur = self.blocks[block].immed_dom;
                    }
                    break;
                }
                Some(first) => first,
            };
            if self.blocks[first].is_mark() {
                common = Some(first);
                break;
            }
            self.blocks[first].set_mark();
            if self.blocks[second].is_mark() {
                common = Some(second);
                break;
            }
            self.blocks[second].set_mark();
            b1 = self.blocks[first].immed_dom;
            b2 = self.blocks[second].immed_dom;
        }
        let mut cur = Some(bl1);
        while let Some(block) = cur {
            if !self.blocks[block].is_mark() {
                break;
            }
            self.blocks[block].clear_mark();
            cur = self.blocks[block].immed_dom;
        }
        let mut cur = Some(bl2);
        while let Some(block) = cur {
            if !self.blocks[block].is_mark() {
                break;
            }
            self.blocks[block].clear_mark();
            cur = self.blocks[block].immed_dom;
        }
        common
    }

    pub fn block_find_common_block_set(&mut self, block_set: &[BlockId]) -> Option<BlockId> {
        let mut marked_set = Vec::new();
        let mut res = block_set[0];
        let mut best_index = self.blocks[res].index;
        let mut cur = Some(res);
        while let Some(block) = cur {
            self.blocks[block].set_mark();
            marked_set.push(block);
            cur = self.blocks[block].immed_dom;
        }
        for member in block_set.iter().skip(1) {
            if best_index == 0 {
                break;
            }
            let mut block = *member;
            while !self.blocks[block].is_mark() {
                self.blocks[block].set_mark();
                marked_set.push(block);
                block = self.blocks[block].immed_dom.expect("block without immediate dominator");
            }
            if self.blocks[block].index < best_index {
                res = block;
                best_index = self.blocks[res].index;
            }
        }
        for block in marked_set {
            self.blocks[block].clear_mark();
        }
        Some(res)
    }

    pub fn block_find_condition(
        &self,
        bl1: BlockId,
        edge1: i32,
        bl2: BlockId,
        edge2: i32,
        slot1: &mut i32,
    ) -> Option<BlockId> {
        let mut bl1 = bl1;
        let mut edge1 = edge1;
        let mut bl2 = bl2;
        let mut edge2 = edge2;
        let mut cond = self.blocks[bl1].get_in(edge1);
        while self.blocks[cond].size_out() != 2 {
            if self.blocks[cond].size_out() != 1 {
                return None;
            }
            bl1 = cond;
            edge1 = 0;
            cond = self.blocks[bl1].get_in(0);
        }
        while cond != self.blocks[bl2].get_in(edge2) {
            bl2 = self.blocks[bl2].get_in(edge2);
            if self.blocks[bl2].size_out() != 1 {
                return None;
            }
            edge2 = 0;
        }
        *slot1 = self.blocks[bl1].get_in_rev_index(edge1);
        Some(cond)
    }

    pub fn block_add_block(&mut self, graph: BlockId, bl: BlockId) {
        let min = self.blocks[bl].index;
        let leaf_count = self.blocks[bl].get_basic_count();
        let depth = self.blocks[bl].get_structure_depth() + 1;
        self.blocks[bl].parent = Some(graph);
        let graphblock = &mut self.blocks[graph];
        if graphblock.list.is_empty() {
            graphblock.index = min;
        } else if min < graphblock.index {
            graphblock.index = min;
        }
        graphblock.list.push(bl);
        graphblock.leaf_count += leaf_count;
        if depth > graphblock.structure_depth {
            graphblock.structure_depth = depth;
        }
    }

    pub fn block_force_output_num(&mut self, graph: BlockId, index: i32) -> Result<()> {
        while self.blocks[graph].size_out() < index {
            self.block_add_in_edge(graph, graph, FlowBlock::F_LOOP_EDGE | FlowBlock::F_BACK_EDGE);
        }
        Ok(())
    }

    pub fn block_self_identify(&mut self, graph: BlockId) -> Result<()> {
        let list = self.blocks[graph].list.clone();
        if list.is_empty() {
            return Ok(());
        }
        for mybl in list {
            let mut slot = 0usize;
            while slot < self.blocks[mybl].intothis.len() {
                let otherbl = self.blocks[mybl].intothis[slot].point;
                if self.blocks[otherbl].parent == Some(graph) {
                    slot += 1;
                } else {
                    let mut edgeslot = 0usize;
                    while edgeslot < self.blocks[otherbl].outofthis.len() {
                        if self.blocks[otherbl].outofthis[edgeslot].point == mybl {
                            self.block_replace_out_edge(otherbl, edgeslot as i32, graph);
                        }
                        edgeslot += 1;
                    }
                }
            }
            slot = 0;
            while slot < self.blocks[mybl].outofthis.len() {
                let otherbl = self.blocks[mybl].outofthis[slot].point;
                if self.blocks[otherbl].parent == Some(graph) {
                    slot += 1;
                } else {
                    let mut edgeslot = 0usize;
                    while edgeslot < self.blocks[otherbl].intothis.len() {
                        if self.blocks[otherbl].intothis[edgeslot].point == mybl {
                            self.block_replace_in_edge(otherbl, edgeslot as i32, graph);
                        }
                        edgeslot += 1;
                    }
                    if self.blocks[mybl].is_switch_out() {
                        self.blocks[graph].set_flag(FlowBlock::F_SWITCH_OUT);
                    }
                }
            }
        }
        self.block_dedup(graph);
        Ok(())
    }

    pub fn block_identify_internal(&mut self, graph: BlockId, ident: BlockId, nodes: &[BlockId]) -> Result<()> {
        for node in nodes.iter() {
            self.blocks[*node].set_mark();
            self.block_add_block(ident, *node);
            let nodeflags = self.blocks[*node].flags & (FlowBlock::F_INTERIOR_GOTOOUT | FlowBlock::F_INTERIOR_GOTOIN);
            self.blocks[ident].flags |= nodeflags;
        }
        let list = std::mem::take(&mut self.blocks[graph].list);
        let mut newlist = Vec::with_capacity(list.len());
        for child in list {
            if !self.blocks[child].is_mark() {
                newlist.push(child);
            } else {
                self.blocks[child].clear_mark();
            }
        }
        self.blocks[graph].list = newlist;
        self.block_self_identify(ident)
    }

    pub fn block_clear_edge_flags(&mut self, graph: BlockId, fl: u32) {
        let mask = !fl;
        let list = self.blocks[graph].list.clone();
        for child in list {
            let block = &mut self.blocks[child];
            for edge in block.intothis.iter_mut() {
                edge.label &= mask;
            }
            for edge in block.outofthis.iter_mut() {
                edge.label &= mask;
            }
        }
    }

    pub fn block_create_virtual_root(&mut self, rootlist: &[BlockId]) -> BlockId {
        let newroot = self.blocks.alloc(FlowBlock::new(BlockKind::Plain));
        for root in rootlist.iter() {
            self.block_add_in_edge(*root, newroot, 0);
        }
        newroot
    }

    pub fn block_find_spanning_tree(
        &mut self,
        graph: BlockId,
        preorder: &mut Vec<BlockId>,
        rootlist: &mut Vec<BlockId>,
    ) -> Result<()> {
        let list = self.blocks[graph].list.clone();
        if list.is_empty() {
            return Ok(());
        }
        let mut rpostorder: Vec<Option<BlockId>> = vec![None; list.len()];
        let mut state: Vec<BlockId> = Vec::with_capacity(list.len());
        let mut istate: Vec<i32> = Vec::with_capacity(list.len());
        preorder.reserve(list.len());
        for child in list.iter() {
            let block = &mut self.blocks[*child];
            block.index = -1;
            block.visitcount = -1;
            block.copymap = Some(*child);
            if block.size_in() == 0 {
                rootlist.push(*child);
            }
        }
        if rootlist.len() > 1 {
            let last = rootlist.len() - 1;
            rootlist.swap(0, last);
        } else if rootlist.is_empty() {
            rootlist.push(list[0]);
        }
        let origrootpos = rootlist.len() - 1;

        for repeat in 0..2 {
            let mut extraroots = false;
            let mut rpostcount = list.len();
            let mut rootindex = 0usize;
            self.block_clear_edge_flags(
                graph,
                FlowBlock::F_IRREDUCIBLE
                    | FlowBlock::F_TREE_EDGE
                    | FlowBlock::F_FORWARD_EDGE
                    | FlowBlock::F_CROSS_EDGE
                    | FlowBlock::F_BACK_EDGE
                    | FlowBlock::F_LOOP_EDGE
                    | FlowBlock::F_LOOP_EXIT_EDGE,
            );
            while preorder.len() < list.len() {
                let mut startbl: Option<BlockId> = None;
                while rootindex < rootlist.len() {
                    let candidate = rootlist[rootindex];
                    rootindex += 1;
                    if self.blocks[candidate].visitcount == -1 {
                        startbl = Some(candidate);
                        break;
                    }
                    rootlist.remove(rootindex - 1);
                    rootindex -= 1;
                }
                let startbl = match startbl {
                    Some(startbl) => startbl,
                    None => {
                        extraroots = true;
                        let mut chosen = list[0];
                        for child in list.iter() {
                            chosen = *child;
                            if self.blocks[chosen].visitcount == -1 {
                                break;
                            }
                        }
                        rootlist.push(chosen);
                        rootindex += 1;
                        chosen
                    }
                };

                state.push(startbl);
                istate.push(0);
                self.blocks[startbl].visitcount = preorder.len() as i32;
                preorder.push(startbl);
                self.blocks[startbl].numdesc = 1;

                while let Some(curbl) = state.last().copied() {
                    let curstate = *istate.last().expect("spanning tree state out of sync");
                    if self.blocks[curbl].size_out() <= curstate {
                        state.pop();
                        istate.pop();
                        rpostcount -= 1;
                        self.blocks[curbl].index = rpostcount as i32;
                        rpostorder[rpostcount] = Some(curbl);
                        if let Some(parentbl) = state.last().copied() {
                            let numdesc = self.blocks[curbl].numdesc;
                            self.blocks[parentbl].numdesc += numdesc;
                        }
                    } else {
                        let edgenum = curstate;
                        *istate.last_mut().expect("spanning tree state out of sync") += 1;
                        if self.blocks[curbl].is_irreducible_out(edgenum) {
                            continue;
                        }
                        let childbl = self.blocks[curbl].get_out(edgenum);
                        if self.blocks[childbl].visitcount == -1 {
                            self.block_set_out_edge_flag(curbl, edgenum, FlowBlock::F_TREE_EDGE);
                            state.push(childbl);
                            istate.push(0);
                            self.blocks[childbl].visitcount = preorder.len() as i32;
                            preorder.push(childbl);
                            self.blocks[childbl].numdesc = 1;
                        } else if self.blocks[childbl].index == -1 {
                            self.block_set_out_edge_flag(
                                curbl,
                                edgenum,
                                FlowBlock::F_BACK_EDGE | FlowBlock::F_LOOP_EDGE,
                            );
                        } else if self.blocks[curbl].visitcount < self.blocks[childbl].visitcount {
                            self.block_set_out_edge_flag(curbl, edgenum, FlowBlock::F_FORWARD_EDGE);
                        } else {
                            self.block_set_out_edge_flag(curbl, edgenum, FlowBlock::F_CROSS_EDGE);
                        }
                    }
                }
            }
            if !extraroots {
                break;
            }
            if repeat == 1 {
                return Err(Error::Lowlevel("Could not generate spanning tree".to_string()));
            }
            let last = rootlist.len() - 1;
            rootlist.swap(last, origrootpos);
            for child in list.iter() {
                let block = &mut self.blocks[*child];
                block.index = -1;
                block.visitcount = -1;
                block.copymap = Some(*child);
            }
            preorder.clear();
            state.clear();
            istate.clear();
        }

        if rootlist.len() > 1 {
            let last = rootlist.len() - 1;
            rootlist.swap(0, last);
        }
        self.blocks[graph].list = rpostorder
            .into_iter()
            .map(|entry| entry.expect("block missing from reverse post order"))
            .collect();
        Ok(())
    }

    pub fn block_find_irreducible(
        &mut self,
        _graph: BlockId,
        preorder: &[BlockId],
        irreduciblecount: &mut i32,
    ) -> bool {
        let mut reachunder: Vec<BlockId> = Vec::new();
        let mut needrebuild = false;
        let mut preorder_index = preorder.len() as i32 - 1;
        while preorder_index >= 0 {
            let head = preorder[preorder_index as usize];
            preorder_index -= 1;
            let sizein = self.blocks[head].size_in();
            for slot in 0..sizein {
                if !self.blocks[head].is_back_edge_in(slot) {
                    continue;
                }
                let source = self.blocks[head].get_in(slot);
                if source == head {
                    continue;
                }
                let ymap = self.blocks[source].copymap.expect("block without copy map");
                reachunder.push(ymap);
                self.blocks[ymap].set_mark();
            }
            let mut queue_index = 0usize;
            while queue_index < reachunder.len() {
                let member_block = reachunder[queue_index];
                queue_index += 1;
                let member_sizein = self.blocks[member_block].size_in();
                for slot in 0..member_sizein {
                    if self.blocks[member_block].is_irreducible_in(slot) {
                        continue;
                    }
                    let source = self.blocks[member_block].get_in(slot);
                    let yprime = self.blocks[source].copymap.expect("block without copy map");
                    let xvisit = self.blocks[head].visitcount;
                    let xdesc = self.blocks[head].numdesc;
                    let yvisit = self.blocks[yprime].visitcount;
                    if xvisit > yvisit || xvisit + xdesc <= yvisit {
                        *irreduciblecount += 1;
                        let edgeout = self.blocks[member_block].get_in_rev_index(slot);
                        self.block_set_out_edge_flag(source, edgeout, FlowBlock::F_IRREDUCIBLE);
                        if self.blocks[member_block].is_tree_edge_in(slot) {
                            needrebuild = true;
                        } else {
                            self.block_clear_out_edge_flag(
                                source,
                                edgeout,
                                FlowBlock::F_CROSS_EDGE | FlowBlock::F_FORWARD_EDGE,
                            );
                        }
                    } else if !self.blocks[yprime].is_mark() && yprime != head {
                        reachunder.push(yprime);
                        self.blocks[yprime].set_mark();
                    }
                }
            }
            for member in reachunder.iter() {
                self.blocks[*member].clear_mark();
                self.blocks[*member].copymap = Some(head);
            }
            reachunder.clear();
        }
        needrebuild
    }

    pub fn block_force_false_edge(&mut self, graph: BlockId, out0: BlockId) -> Result<()> {
        if self.blocks[graph].size_out() != 2 {
            return Err(Error::Lowlevel("Can only preserve binary condition".to_string()));
        }
        let mut out0 = out0;
        if self.blocks[out0].parent == Some(graph) {
            out0 = graph;
        }
        if self.blocks[graph].outofthis[0].point != out0 {
            self.block_swap_edges(graph);
        }
        if self.blocks[graph].outofthis[0].point != out0 {
            return Err(Error::Lowlevel("Unable to preserve condition".to_string()));
        }
        Ok(())
    }

    pub fn block_swap_blocks(&mut self, graph: BlockId, index: i32, second_index: i32) {
        self.blocks[graph].list.swap(index as usize, second_index as usize);
    }

    pub fn block_mark_copy_block(&mut self, bl: BlockId, fl: u32) {
        if let Some(leaf) = self.block_get_front_leaf(bl) {
            self.blocks[leaf].flags |= fl;
        }
    }

    fn block_destroy(&mut self, bl: BlockId) {
        if self.block_graph_kind(bl) {
            let list = std::mem::take(&mut self.blocks[bl].list);
            for child in list {
                self.block_destroy(child);
            }
        }
        self.blocks.remove(bl);
    }

    pub fn block_clear(&mut self, graph: BlockId) {
        let list = std::mem::take(&mut self.blocks[graph].list);
        for child in list {
            self.block_destroy(child);
        }
        self.blocks[graph].clear_all_flags();
    }

    pub fn block_graph_decode(&mut self, graph: BlockId, decoder: &mut dyn Decoder) -> Result<()> {
        let resolver = BlockMap::new();
        self.block_decode(graph, decoder, &resolver)
    }

    pub fn block_add_edge(&mut self, _graph: BlockId, begin: BlockId, end: BlockId) -> Result<()> {
        self.block_add_in_edge(end, begin, 0);
        Ok(())
    }

    pub fn block_add_loop_edge(&mut self, _graph: BlockId, begin: BlockId, outindex: i32) -> Result<()> {
        self.block_set_out_edge_flag(begin, outindex, FlowBlock::F_LOOP_EDGE);
        Ok(())
    }

    pub fn block_remove_edge(&mut self, _graph: BlockId, begin: BlockId, end: BlockId) -> Result<()> {
        let intothis = &self.blocks[end].intothis;
        let slot = intothis
            .iter()
            .position(|edge| edge.point == begin)
            .unwrap_or(intothis.len());
        self.block_remove_in_edge(end, slot as i32);
        Ok(())
    }

    pub fn block_switch_edge(&mut self, _graph: BlockId, input: BlockId, outbefore: BlockId, outafter: BlockId) {
        let mut slot = 0usize;
        while slot < self.blocks[input].outofthis.len() {
            if self.blocks[input].outofthis[slot].point == outbefore {
                self.block_replace_out_edge(input, slot as i32, outafter);
            }
            slot += 1;
        }
    }

    pub fn block_move_out_edge(&mut self, _graph: BlockId, blold: BlockId, slot: i32, blnew: BlockId) -> Result<()> {
        let outbl = self.blocks[blold].get_out(slot);
        let rev = self.blocks[blold].get_out_rev_index(slot);
        self.block_replace_in_edge(outbl, rev, blnew);
        Ok(())
    }

    pub fn block_remove_block(&mut self, graph: BlockId, bl: BlockId) -> Result<()> {
        while self.blocks[bl].size_in() > 0 {
            let inbl = self.blocks[bl].get_in(0);
            self.block_remove_edge(graph, inbl, bl)?;
        }
        while self.blocks[bl].size_out() > 0 {
            let outbl = self.blocks[bl].get_out(0);
            self.block_remove_edge(graph, bl, outbl)?;
        }
        let list = &mut self.blocks[graph].list;
        if let Some(position) = list.iter().position(|child| *child == bl) {
            list.remove(position);
        }
        self.block_destroy(bl);
        Ok(())
    }

    pub fn block_remove_from_flow(&mut self, _graph: BlockId, bl: BlockId) -> Result<()> {
        while self.blocks[bl].size_out() > 0 {
            let lastslot = self.blocks[bl].size_out() - 1;
            let bbout = self.blocks[bl].get_out(lastslot);
            self.block_remove_out_edge(bl, lastslot);
            while self.blocks[bl].size_in() > 0 {
                let bbin = self.blocks[bl].get_in(0);
                let rev = self.blocks[bl].intothis[0].reverse_index;
                self.block_replace_out_edge(bbin, rev, bbout);
            }
        }
        Ok(())
    }

    pub fn block_remove_from_flow_split(&mut self, _graph: BlockId, bl: BlockId, flipflow: bool) -> Result<()> {
        if flipflow {
            self.block_replace_edges_thru(bl, 0, 1);
        } else {
            self.block_replace_edges_thru(bl, 1, 1);
        }
        self.block_replace_edges_thru(bl, 0, 0);
        Ok(())
    }

    pub fn block_splice_block(&mut self, graph: BlockId, bl: BlockId) -> Result<()> {
        let mut outbl = None;
        if self.blocks[bl].size_out() == 1 {
            let candidate = self.blocks[bl].get_out(0);
            if self.blocks[candidate].size_in() == 1 {
                outbl = Some(candidate);
            }
        }
        let outbl = match outbl {
            None => {
                return Err(Error::Lowlevel(
                    "Can only splice a block with 1 output to a block with 1 input".to_string(),
                ));
            }
            Some(outbl) => outbl,
        };
        let fl1 = self.blocks[bl].flags & (FlowBlock::F_UNSTRUCTURED_TARG | FlowBlock::F_ENTRY_POINT);
        let fl2 = self.blocks[outbl].flags & FlowBlock::F_SWITCH_OUT;
        self.block_remove_out_edge(bl, 0);
        let szout = self.blocks[outbl].size_out();
        for _ in 0..szout {
            self.block_move_out_edge(graph, outbl, 0, bl)?;
        }
        self.block_remove_block(graph, outbl)?;
        self.blocks[bl].flags = fl1 | fl2;
        Ok(())
    }

    pub fn block_set_start_block(&mut self, graph: BlockId, bl: BlockId) -> Result<()> {
        let first = self.blocks[graph].list[0];
        if (self.blocks[first].flags & FlowBlock::F_ENTRY_POINT) != 0 {
            if bl == first {
                return Ok(());
            }
            self.blocks[first].flags &= !FlowBlock::F_ENTRY_POINT;
        }
        let list = &mut self.blocks[graph].list;
        let position = list.iter().position(|child| *child == bl).unwrap_or(list.len());
        for slot in (1..=position.min(list.len().saturating_sub(1))).rev() {
            list[slot] = list[slot - 1];
        }
        list[0] = bl;
        self.blocks[bl].flags |= FlowBlock::F_ENTRY_POINT;
        Ok(())
    }

    pub fn block_get_start_block(&self, graph: BlockId) -> Result<BlockId> {
        let list = &self.blocks[graph].list;
        if list.is_empty() || (self.blocks[list[0]].flags & FlowBlock::F_ENTRY_POINT) == 0 {
            return Err(Error::Lowlevel("No start block registered".to_string()));
        }
        Ok(list[0])
    }

    pub fn block_new_block(&mut self, graph: BlockId) -> BlockId {
        let ret = self.blocks.alloc(FlowBlock::new(BlockKind::Plain));
        self.block_add_block(graph, ret);
        ret
    }

    pub fn block_new_block_basic(&mut self, graph: BlockId) -> BlockId {
        let ret = self.blocks.alloc(FlowBlock::new_basic());
        self.block_add_block(graph, ret);
        ret
    }

    pub fn block_new_block_copy(&mut self, graph: BlockId, bl: BlockId) -> BlockId {
        let source = &self.blocks[bl];
        let mut copyblock = FlowBlock::new_copy(Some(bl));
        copyblock.intothis = source.intothis.clone();
        copyblock.outofthis = source.outofthis.clone();
        copyblock.immed_dom = source.immed_dom;
        copyblock.index = source.index;
        copyblock.numdesc = source.numdesc;
        copyblock.flags |= source.flags;
        if copyblock.outofthis.len() > 2 {
            copyblock.flags |= FlowBlock::F_SWITCH_OUT;
        }
        let ret = self.blocks.alloc(copyblock);
        self.block_add_block(graph, ret);
        ret
    }

    pub fn block_new_block_goto(&mut self, graph: BlockId, bl: BlockId) -> Result<BlockId> {
        let target = self.blocks[bl].get_out(0);
        let ret = self.blocks.alloc(FlowBlock::new_goto(target));
        self.block_identify_internal(graph, ret, &[bl])?;
        self.block_add_block(graph, ret);
        self.block_force_output_num(ret, 1)?;
        let out = self.blocks[ret].get_out(0);
        self.block_remove_edge(graph, ret, out)?;
        Ok(ret)
    }

    pub fn block_new_block_multi_goto(&mut self, graph: BlockId, bl: BlockId, outedge: i32) -> Result<BlockId> {
        let targetbl = self.blocks[bl].get_out(outedge);
        let isdefaultedge = self.blocks[bl].is_default_branch(outedge);
        if self.blocks[bl].get_type() == BlockType::MultiGoto {
            let ret = bl;
            self.blocks[ret].multigoto_add_edge(targetbl);
            self.block_remove_edge(graph, ret, targetbl)?;
            if isdefaultedge {
                self.blocks[ret].set_default_goto();
            }
            Ok(ret)
        } else {
            let ret = self.blocks.alloc(FlowBlock::new_multi_goto(bl));
            let orig_size_out = self.blocks[bl].size_out();
            self.block_identify_internal(graph, ret, &[bl])?;
            self.block_add_block(graph, ret);
            self.blocks[ret].multigoto_add_edge(targetbl);
            if targetbl != bl {
                if self.blocks[ret].size_out() != orig_size_out {
                    let forced = self.blocks[ret].size_out() + 1;
                    self.block_force_output_num(ret, forced)?;
                }
                self.block_remove_edge(graph, ret, targetbl)?;
            }
            if isdefaultedge {
                self.blocks[ret].set_default_goto();
            }
            Ok(ret)
        }
    }

    pub fn block_new_block_list(&mut self, graph: BlockId, nodes: &[BlockId]) -> Result<BlockId> {
        let lastnode = *nodes.last().expect("list block without nodes");
        let outforce = self.blocks[lastnode].size_out();
        let out0 = if outforce == 2 {
            Some(self.blocks[lastnode].get_out(0))
        } else {
            None
        };
        let ret = self.blocks.alloc(FlowBlock::new_graph_kind(BlockKind::List));
        self.block_identify_internal(graph, ret, nodes)?;
        self.block_add_block(graph, ret);
        self.block_force_output_num(ret, outforce)?;
        if self.blocks[ret].size_out() == 2 {
            let out0 = out0.ok_or_else(|| Error::Lowlevel("Unable to preserve condition".to_string()))?;
            self.block_force_false_edge(ret, out0)?;
        }
        Ok(ret)
    }

    pub fn block_new_block_condition(&mut self, graph: BlockId, b1: BlockId, b2: BlockId) -> Result<BlockId> {
        let out0 = self.blocks[b2].get_out(0);
        let opc = if self.blocks[b1].get_false_out() == b2 {
            OpCode::IntOr
        } else {
            OpCode::IntAnd
        };
        let ret = self.blocks.alloc(FlowBlock::new_condition(opc));
        self.block_identify_internal(graph, ret, &[b1, b2])?;
        self.block_add_block(graph, ret);
        self.block_force_output_num(ret, 2)?;
        self.block_force_false_edge(ret, out0)?;
        Ok(ret)
    }

    pub fn block_new_block_if_goto(&mut self, graph: BlockId, cond: BlockId) -> Result<BlockId> {
        if !self.blocks[cond].is_goto_out(1) {
            return Err(Error::Lowlevel(
                "Building ifgoto where true branch is not the goto".to_string(),
            ));
        }
        let out0 = self.blocks[cond].get_out(0);
        let target = self.blocks[cond].get_out(1);
        let ret = self.blocks.alloc(FlowBlock::new_if_goto(target));
        self.block_identify_internal(graph, ret, &[cond])?;
        self.block_add_block(graph, ret);
        self.block_force_output_num(ret, 2)?;
        self.block_force_false_edge(ret, out0)?;
        let trueout = self.blocks[ret].get_true_out();
        self.block_remove_edge(graph, ret, trueout)?;
        Ok(ret)
    }

    fn block_new_structure(
        &mut self,
        graph: BlockId,
        kind: BlockKind,
        nodes: &[BlockId],
        outputs: Option<i32>,
    ) -> Result<BlockId> {
        let ret = self.blocks.alloc(FlowBlock::new_graph_kind(kind));
        self.block_identify_internal(graph, ret, nodes)?;
        self.block_add_block(graph, ret);
        if let Some(outputs) = outputs {
            self.block_force_output_num(ret, outputs)?;
        }
        Ok(ret)
    }

    pub fn block_new_block_if(&mut self, graph: BlockId, cond: BlockId, tc: BlockId) -> Result<BlockId> {
        self.block_new_structure(graph, BlockKind::If, &[cond, tc], Some(1))
    }

    pub fn block_new_block_if_else(
        &mut self,
        graph: BlockId,
        cond: BlockId,
        tc: BlockId,
        fc: BlockId,
    ) -> Result<BlockId> {
        self.block_new_structure(graph, BlockKind::IfElse, &[cond, tc, fc], Some(1))
    }

    pub fn block_new_block_if_no_exit(
        &mut self,
        graph: BlockId,
        cond: BlockId,
        tc: BlockId,
        fc: BlockId,
    ) -> Result<BlockId> {
        self.block_new_structure(graph, BlockKind::IfNoExit, &[cond, tc, fc], None)
    }

    pub fn block_new_block_while_do(&mut self, graph: BlockId, cond: BlockId, cl: BlockId) -> Result<BlockId> {
        let kind = FlowBlock::new_while_do().kind;
        self.block_new_structure(graph, kind, &[cond, cl], Some(1))
    }

    pub fn block_new_block_do_while(&mut self, graph: BlockId, condcl: BlockId) -> Result<BlockId> {
        self.block_new_structure(graph, BlockKind::DoWhile, &[condcl], Some(1))
    }

    pub fn block_new_block_inf_loop(&mut self, graph: BlockId, body: BlockId) -> Result<BlockId> {
        self.block_new_structure(graph, BlockKind::InfLoop, &[body], None)
    }

    pub fn block_new_block_switch(&mut self, graph: BlockId, cs: &[BlockId], has_exit: bool) -> Result<BlockId> {
        let rootbl = cs[0];
        let kind = self.block_switch_kind(rootbl);
        let ret = self.blocks.alloc(FlowBlock::new_graph_kind(kind));
        let leafbl = match self.block_get_exit_leaf(rootbl) {
            Some(leaf) if self.blocks[leaf].get_type() == BlockType::Copy => leaf,
            _ => {
                self.blocks.remove(ret);
                return Err(Error::Lowlevel("Could not get switch leaf".to_string()));
            }
        };
        let switchbl = self.blocks[leafbl]
            .sub_block(0)
            .expect("switch leaf without copied block");
        if let Err(err) = self.block_grab_case_basic(ret, switchbl, cs) {
            self.blocks.remove(ret);
            return Err(err);
        }
        self.block_identify_internal(graph, ret, cs)?;
        self.block_add_block(graph, ret);
        if has_exit {
            self.block_force_output_num(ret, 1)?;
        }
        self.blocks[ret].clear_flag(FlowBlock::F_SWITCH_OUT);
        Ok(ret)
    }

    pub fn block_order_blocks(&mut self, graph: BlockId) {
        let mut list = self.blocks[graph].list.clone();
        if list.len() != 1 {
            list.sort_by(|first, second| {
                ordering_from_less(
                    self.block_compare_final_order(*first, *second),
                    self.block_compare_final_order(*second, *first),
                )
            });
        }
        self.blocks[graph].list = list;
    }

    pub fn block_build_copy(&mut self, graph: BlockId, source: BlockId) {
        let startsize = self.blocks[graph].list.len();
        let sourcelist = self.blocks[source].list.clone();
        for original in sourcelist {
            let copyblock = self.block_new_block_copy(graph, original);
            self.blocks[original].copymap = Some(copyblock);
        }
        let newlist: Vec<BlockId> = self.blocks[graph].list[startsize..].to_vec();
        for copyblock in newlist {
            self.block_replace_using_map(copyblock);
        }
    }

    pub fn block_clear_visit_count(&mut self, graph: BlockId) {
        let list = self.blocks[graph].list.clone();
        for child in list {
            self.blocks[child].visitcount = 0;
        }
    }

    pub fn block_calc_forward_dominator(&mut self, graph: BlockId, rootlist: &[BlockId]) -> Result<()> {
        let list = self.blocks[graph].list.clone();
        if list.is_empty() {
            return Ok(());
        }
        let numnodes = list.len() as i32 - 1;
        let mut postorder: Vec<BlockId> = vec![list[0]; list.len()];
        for (slot, child) in list.iter().enumerate() {
            self.blocks[*child].immed_dom = None;
            postorder[(numnodes - slot as i32) as usize] = *child;
        }
        let mut virtualroot = None;
        if rootlist.len() > 1 {
            let root = self.block_create_virtual_root(rootlist);
            postorder.push(root);
            virtualroot = Some(root);
        }
        let mut source = *postorder.last().expect("dominator order without blocks");
        if self.blocks[source].size_in() != 0 {
            if rootlist.len() != 1 || rootlist[0] != source {
                return Err(Error::Lowlevel("Problems finding root node of graph".to_string()));
            }
            let root = self.block_create_virtual_root(rootlist);
            postorder.push(root);
            virtualroot = Some(root);
            source = root;
        }
        self.blocks[source].immed_dom = Some(source);
        for slot in 0..self.blocks[source].size_out() {
            let out = self.blocks[source].get_out(slot);
            self.blocks[out].immed_dom = Some(source);
        }
        let mut changed = true;
        let mut new_idom: Option<BlockId> = None;
        let rootnode = *postorder.last().expect("dominator order without blocks");
        while changed {
            changed = false;
            let mut position = postorder.len() as i32 - 2;
            while position >= 0 {
                let cur = postorder[position as usize];
                position -= 1;
                if self.blocks[cur].immed_dom == Some(rootnode) {
                    continue;
                }
                let sizein = self.blocks[cur].size_in();
                let mut slot = 0;
                while slot < sizein {
                    new_idom = Some(self.blocks[cur].get_in(slot));
                    if self.blocks[new_idom.expect("dominator candidate")].immed_dom.is_some() {
                        break;
                    }
                    slot += 1;
                }
                slot += 1;
                while slot < sizein {
                    let rho = self.blocks[cur].get_in(slot);
                    if self.blocks[rho].immed_dom.is_some() {
                        let mut finger1 = numnodes - self.blocks[rho].index;
                        let mut finger2 = numnodes - self.blocks[new_idom.expect("dominator candidate")].index;
                        while finger1 != finger2 {
                            while finger1 < finger2 {
                                let dom = self.blocks[postorder[finger1 as usize]]
                                    .immed_dom
                                    .expect("dominator chain broken");
                                finger1 = numnodes - self.blocks[dom].index;
                            }
                            while finger2 < finger1 {
                                let dom = self.blocks[postorder[finger2 as usize]]
                                    .immed_dom
                                    .expect("dominator chain broken");
                                finger2 = numnodes - self.blocks[dom].index;
                            }
                        }
                        new_idom = Some(postorder[finger1 as usize]);
                    }
                    slot += 1;
                }
                if self.blocks[cur].immed_dom != new_idom {
                    self.blocks[cur].immed_dom = new_idom;
                    changed = true;
                }
            }
        }
        match virtualroot {
            Some(root) => {
                for slot in 0..list.len() {
                    if self.blocks[postorder[slot]].immed_dom == Some(root) {
                        self.blocks[postorder[slot]].immed_dom = None;
                    }
                }
                while self.blocks[root].size_out() > 0 {
                    let last = self.blocks[root].size_out() - 1;
                    self.block_remove_out_edge(root, last);
                }
                self.blocks.remove(root);
            }
            None => {
                self.blocks[rootnode].immed_dom = None;
            }
        }
        Ok(())
    }

    pub fn block_build_dom_tree(&self, graph: BlockId, child: &mut Vec<Vec<BlockId>>) {
        let list = &self.blocks[graph].list;
        child.clear();
        child.resize(list.len() + 1, Vec::new());
        for bl in list.iter() {
            match self.blocks[*bl].immed_dom {
                Some(dom) => child[self.blocks[dom].index as usize].push(*bl),
                None => child[list.len()].push(*bl),
            }
        }
    }

    pub fn block_build_dom_depth(&self, graph: BlockId, depth: &mut Vec<i32>) -> i32 {
        let list = &self.blocks[graph].list;
        let mut max = 0;
        depth.resize(list.len() + 1, 0);
        for (slot, bl) in list.iter().enumerate() {
            match self.blocks[*bl].immed_dom {
                Some(dom) => depth[slot] = depth[self.blocks[dom].index as usize] + 1,
                None => depth[slot] = 1,
            }
            if max < depth[slot] {
                max = depth[slot];
            }
        }
        depth[list.len()] = 0;
        max
    }

    pub fn block_build_dom_sub_tree(&self, graph: BlockId, res: &mut Vec<BlockId>, root: BlockId) {
        let list = &self.blocks[graph].list;
        let rootindex = self.blocks[root].index;
        res.push(root);
        let mut slot = (rootindex + 1) as usize;
        while slot < list.len() {
            let bl = list[slot];
            let dombl = match self.blocks[bl].immed_dom {
                None => break,
                Some(dombl) => dombl,
            };
            if self.blocks[dombl].index > rootindex {
                break;
            }
            res.push(bl);
            slot += 1;
        }
    }

    pub fn block_calc_loop(&mut self, graph: BlockId) -> Result<()> {
        let list = self.blocks[graph].list.clone();
        if list.is_empty() {
            return Ok(());
        }
        let mut path: Vec<BlockId> = vec![list[0]];
        let mut state: Vec<i32> = vec![0];
        self.blocks[list[0]].set_flag(FlowBlock::F_MARK | FlowBlock::F_MARK2);
        while let Some(bl) = path.last().copied() {
            let slot = *state.last().expect("loop state out of sync");
            if slot >= self.blocks[bl].size_out() {
                self.blocks[bl].clear_flag(FlowBlock::F_MARK2);
                path.pop();
                state.pop();
            } else {
                *state.last_mut().expect("loop state out of sync") += 1;
                if self.blocks[bl].is_loop_out(slot) {
                    continue;
                }
                let nextbl = self.blocks[bl].get_out(slot);
                if (self.blocks[nextbl].flags & FlowBlock::F_MARK2) != 0 {
                    self.block_add_loop_edge(graph, bl, slot)?;
                } else if (self.blocks[nextbl].flags & FlowBlock::F_MARK) == 0 {
                    self.blocks[nextbl].set_flag(FlowBlock::F_MARK | FlowBlock::F_MARK2);
                    path.push(nextbl);
                    state.push(0);
                }
            }
        }
        for child in list {
            self.blocks[child].clear_flag(FlowBlock::F_MARK | FlowBlock::F_MARK2);
        }
        Ok(())
    }

    pub fn block_collect_reachable(&mut self, graph: BlockId, res: &mut Vec<BlockId>, bl: BlockId, un: bool) {
        self.blocks[bl].set_mark();
        res.push(bl);
        let mut total = 0usize;
        while total < res.len() {
            let blk = res[total];
            total += 1;
            for slot in 0..self.blocks[blk].size_out() {
                let blk2 = self.blocks[blk].get_out(slot);
                if self.blocks[blk2].is_mark() {
                    continue;
                }
                self.blocks[blk2].set_mark();
                res.push(blk2);
            }
        }
        if un {
            res.clear();
            let list = self.blocks[graph].list.clone();
            for blk in list {
                if self.blocks[blk].is_mark() {
                    self.blocks[blk].clear_mark();
                } else {
                    res.push(blk);
                }
            }
        } else {
            for blk in res.iter() {
                self.blocks[*blk].clear_mark();
            }
        }
    }

    pub fn block_structure_loops(&mut self, graph: BlockId, rootlist: &mut Vec<BlockId>) -> Result<()> {
        let mut preorder = Vec::new();
        let mut irreduciblecount = 0;
        loop {
            self.block_find_spanning_tree(graph, &mut preorder, rootlist)?;
            let needrebuild = self.block_find_irreducible(graph, &preorder, &mut irreduciblecount);
            if needrebuild {
                self.block_clear_edge_flags(
                    graph,
                    FlowBlock::F_TREE_EDGE
                        | FlowBlock::F_FORWARD_EDGE
                        | FlowBlock::F_CROSS_EDGE
                        | FlowBlock::F_BACK_EDGE
                        | FlowBlock::F_LOOP_EDGE,
                );
                preorder.clear();
                rootlist.clear();
            } else {
                break;
            }
        }
        if irreduciblecount > 0 {
            self.block_calc_loop(graph)?;
        }
        Ok(())
    }

    pub fn block_is_consistent(&self, graph: BlockId) -> bool {
        for bl1 in self.blocks[graph].list.iter() {
            let block1 = &self.blocks[*bl1];
            for slot in 0..block1.size_in() {
                let bl2 = block1.get_in(slot);
                let count1 = (0..block1.size_in()).filter(|slot| block1.get_in(*slot) == bl2).count();
                let block2 = &self.blocks[bl2];
                let count2 = (0..block2.size_out())
                    .filter(|slot| block2.get_out(*slot) == *bl1)
                    .count();
                if count1 != count2 {
                    return false;
                }
            }
            for slot in 0..block1.size_out() {
                let bl2 = block1.get_out(slot);
                let count1 = (0..block1.size_out())
                    .filter(|slot| block1.get_out(*slot) == bl2)
                    .count();
                let block2 = &self.blocks[bl2];
                let count2 = (0..block2.size_in())
                    .filter(|slot| block2.get_in(*slot) == *bl1)
                    .count();
                if count1 != count2 {
                    return false;
                }
            }
        }
        true
    }

    pub fn block_insert_op(&mut self, bb: BlockId, iter: Option<OpId>, inst: OpId) {
        self.obank.ops[inst].set_parent(Some(bb));
        self.blocks[bb].basic_mut().op.insert(&mut self.obank.ops, iter, inst);
        let prev = self.blocks[bb].basic().op.prev(&self.obank.ops, inst);
        let ordbefore: u32 = match prev {
            None => 2,
            Some(prev) => self.obank.ops[prev].get_seq_num().get_order(),
        };
        let ordafter: u32 = match iter {
            None => {
                let candidate = ordbefore.wrapping_add(0x1000000);
                if candidate <= ordbefore { u32::MAX } else { candidate }
            }
            Some(follow) => self.obank.ops[follow].get_seq_num().get_order(),
        };
        if ordafter.wrapping_sub(ordbefore) <= 1 {
            self.block_set_order(bb);
        } else {
            self.obank.ops[inst].set_order(ordafter / 2 + ordbefore / 2);
        }
        let instop = &self.obank.ops[inst];
        if instop.is_branch() && instop.code() == OpCode::Branchind {
            self.blocks[bb].set_flag(FlowBlock::F_SWITCH_OUT);
        }
    }

    pub fn block_set_order(&mut self, bb: BlockId) {
        let ops = self.blocks[bb].basic().op.to_vec(&self.obank.ops);
        if ops.is_empty() {
            return;
        }
        let step = (u32::MAX / ops.len() as u32).wrapping_sub(1);
        let mut count: u32 = 0;
        for op in ops {
            count = count.wrapping_add(step);
            self.obank.ops[op].set_order(count);
        }
    }

    pub fn block_remove_op(&mut self, bb: BlockId, inst: OpId) {
        self.obank.ops[inst].set_parent(None);
        self.blocks[bb].basic_mut().op.remove(&mut self.obank.ops, inst);
    }

    pub fn block_copy_range(&mut self, bb: BlockId, source: BlockId) {
        let cover = self.blocks[source].basic().cover.clone();
        self.blocks[bb].basic_mut().cover = cover;
    }

    pub fn block_merge_range(&mut self, bb: BlockId, source: BlockId) {
        let cover = self.blocks[source].basic().cover.clone();
        self.blocks[bb].basic_mut().cover.merge(&cover);
    }

    pub fn block_get_entry_addr(&self, bb: BlockId) -> Address {
        let data = self.blocks[bb].basic();
        let range = if data.cover.num_ranges() == 1 {
            data.cover.get_first_range()
        } else {
            let first = match data.op.front() {
                None => return Address::invalid(),
                Some(first) => first,
            };
            let addr = self.op(first).get_addr();
            let space = addr.get_space().expect("op address without space");
            match data.cover.get_range(space, addr.get_offset()) {
                None => return addr.clone(),
                Some(range) => Some(range),
            }
        };
        range.expect("basic block without range").get_first_addr()
    }

    pub fn block_unblocked_multi(&self, bb: BlockId, outslot: i32) -> bool {
        let block = &self.blocks[bb];
        let blout = block.get_out(outslot);
        let mut redundlist = Vec::new();
        for slot in 0..block.size_in() {
            let bl = block.get_in(slot);
            let inblock = &self.blocks[bl];
            for outpos in 0..inblock.size_out() {
                if inblock.get_out(outpos) == blout {
                    redundlist.push(bl);
                }
            }
        }
        if redundlist.is_empty() {
            return true;
        }
        let outblock = &self.blocks[blout];
        let in_index_to_this = outblock.get_in_index(bb);
        for multiop in outblock.basic().op.iter(&self.obank.ops) {
            let multi = self.op(multiop);
            if multi.code() != OpCode::Multiequal {
                continue;
            }
            for bl in redundlist.iter() {
                let vnredund = multi.get_in(outblock.get_in_index(*bl));
                let mut vnremove = multi.get_in(in_index_to_this);
                if let Some(othermulti) = self.vn(vnremove).get_def() {
                    let other = self.op(othermulti);
                    if other.code() == OpCode::Multiequal && other.get_parent() == Some(bb) {
                        vnremove = other.get_in(block.get_in_index(*bl));
                    }
                }
                if vnremove != vnredund {
                    return false;
                }
            }
        }
        true
    }

    pub fn block_has_no_immediate_copy(&self, bb: BlockId, outslot: i32) -> bool {
        let block = &self.blocks[bb];
        if !block.has_immed_copy_edge(outslot) {
            return true;
        }
        let blout = &self.blocks[block.get_out(outslot)];
        let in_index_to_this = blout.get_in_index(bb);
        for multiop in blout.basic().op.iter(&self.obank.ops) {
            let multi = self.op(multiop);
            if multi.code() != OpCode::Multiequal {
                continue;
            }
            if self.op_has_copy_immed(multiop, in_index_to_this) {
                return false;
            }
        }
        true
    }

    pub fn block_has_only_markers(&self, bb: BlockId) -> bool {
        for bop in self.blocks[bb].basic().op.iter(&self.obank.ops) {
            let op = self.op(bop);
            if op.is_marker() || op.is_branch() {
                continue;
            }
            return false;
        }
        true
    }

    pub fn block_is_do_nothing(&self, bb: BlockId) -> bool {
        let block = &self.blocks[bb];
        if block.size_out() != 1 {
            return false;
        }
        if block.size_in() == 0 {
            return false;
        }
        for slot in 0..block.size_in() {
            let switchbl = &self.blocks[block.get_in(slot)];
            if !switchbl.is_switch_out() {
                continue;
            }
            if switchbl.size_out() > 1 && self.blocks[block.get_out(0)].size_in() > 1 {
                return false;
            }
        }
        if let Some(lastop) = self.block_last_op(bb)
            && self.op(lastop).code() == OpCode::Branchind
        {
            return false;
        }
        self.block_has_only_markers(bb)
    }

    pub fn block_no_intervening_statement(&self, bb: BlockId) -> bool {
        for bop in self.blocks[bb].basic().op.iter(&self.obank.ops) {
            let op = self.op(bop);
            if op.is_marker() || op.is_branch() {
                continue;
            }
            if op.get_eval_type() == PcodeOp::SPECIAL {
                if op.is_call() {
                    return false;
                }
                let opc = op.code();
                if opc == OpCode::Store || opc == OpCode::New {
                    return false;
                }
            } else {
                let opc = op.code();
                if opc == OpCode::Copy || opc == OpCode::Subpiece {
                    continue;
                }
            }
            let outvn = self.vn(op.get_out().expect("statement without output"));
            if outvn.is_addr_tied() {
                return false;
            }
            for desc in outvn.descend().iter() {
                if self.op(*desc).get_parent() != Some(bb) {
                    return false;
                }
            }
        }
        true
    }

    pub fn block_find_multiequal(&self, bb: BlockId, var_array: &[VarnodeId]) -> Option<OpId> {
        let vn = var_array[0];
        let found = self.vn(vn).descend().iter().copied().find(|op| {
            let candidate = self.op(*op);
            candidate.code() == OpCode::Multiequal && candidate.get_parent() == Some(bb)
        })?;
        let op = self.op(found);
        for slot in 0..op.num_input() {
            if op.get_in(slot) != var_array[slot as usize] {
                return None;
            }
        }
        Some(found)
    }

    pub fn block_earliest_use(&self, bb: BlockId, vn: VarnodeId) -> Option<OpId> {
        let mut res: Option<OpId> = None;
        for op in self.vn(vn).descend().iter() {
            if self.op(*op).get_parent() != Some(bb) {
                continue;
            }
            match res {
                None => res = Some(*op),
                Some(current) => {
                    if self.op(*op).get_seq_num().get_order() < self.op(current).get_seq_num().get_order() {
                        res = Some(*op);
                    }
                }
            }
        }
        res
    }

    pub fn block_lift_verify_unroll(&self, var_array: &mut [VarnodeId], slot: i32) -> bool {
        let vn = var_array[0];
        let defop = match self.vn(vn).get_def() {
            None => return false,
            Some(defop) => defop,
        };
        let op = self.op(defop);
        let opc = op.code();
        let cvn = if op.num_input() == 2 {
            let cvn = op.get_in(1 - slot);
            if !self.vn(cvn).is_constant() {
                return false;
            }
            Some(cvn)
        } else {
            None
        };
        var_array[0] = op.get_in(slot);
        for position in 1..var_array.len() {
            let vn = var_array[position];
            let defop = match self.vn(vn).get_def() {
                None => return false,
                Some(defop) => defop,
            };
            let op = self.op(defop);
            if op.code() != opc {
                return false;
            }
            if let Some(cvn) = cvn {
                let cvn2 = op.get_in(1 - slot);
                if !self.vn(cvn2).is_constant() {
                    return false;
                }
                if self.vn(cvn).get_size() != self.vn(cvn2).get_size() {
                    return false;
                }
                if self.vn(cvn).get_offset() != self.vn(cvn2).get_offset() {
                    return false;
                }
            }
            var_array[position] = op.get_in(slot);
        }
        true
    }

    pub fn block_goto_prints(&self, bl: BlockId) -> bool {
        let block = &self.blocks[bl];
        if let Some(parent) = block.parent {
            let nextbl = self.block_next_flow_after(parent, bl);
            let gotobl = self.block_get_front_leaf(block.get_goto_target());
            return gotobl != nextbl;
        }
        false
    }

    fn block_while_do_state(&self, bl: BlockId) -> (Option<OpId>, Option<OpId>, Option<OpId>) {
        match &self.blocks[bl].kind {
            BlockKind::WhileDo {
                initialize_op,
                iterate_op,
                loop_def,
            } => (*initialize_op, *iterate_op, *loop_def),
            _ => panic!("block is not a whiledo"),
        }
    }

    fn block_while_do_set_state(
        &mut self,
        bl: BlockId,
        initialize: Option<Option<OpId>>,
        iterate: Option<Option<OpId>>,
        loopdef: Option<Option<OpId>>,
    ) {
        if let BlockKind::WhileDo {
            initialize_op,
            iterate_op,
            loop_def,
        } = &mut self.blocks[bl].kind
        {
            if let Some(value) = initialize {
                *initialize_op = value;
            }
            if let Some(value) = iterate {
                *iterate_op = value;
            }
            if let Some(value) = loopdef {
                *loop_def = value;
            }
        }
    }

    pub fn block_find_loop_variable(
        &mut self,
        bl: BlockId,
        cbranch: OpId,
        head: BlockId,
        tail: BlockId,
        last_op: OpId,
    ) {
        let vn = self.op(cbranch).get_in(1);
        let op = match self.vn(vn).get_def() {
            None => return,
            Some(op) => op,
        };
        let slot = self.blocks[tail].get_out_rev_index(0);
        let mut path: [(OpId, i32); 4] = [(op, 0); 4];
        let mut count: i32 = 0;
        if self.op(op).is_call() || self.op(op).is_marker() {
            return;
        }
        path[0] = (op, 0);
        while count >= 0 {
            let cur_op = path[count as usize].0;
            let ind = path[count as usize].1;
            path[count as usize].1 += 1;
            if ind >= self.op(cur_op).num_input() {
                count -= 1;
                continue;
            }
            let next_vn = self.op(cur_op).get_in(ind);
            let def_op = match self.vn(next_vn).get_def() {
                None => continue,
                Some(def_op) => def_op,
            };
            if self.op(def_op).code() == OpCode::Multiequal {
                if self.op(def_op).get_parent() != Some(head) {
                    continue;
                }
                let itvn = self.op(def_op).get_in(slot);
                let possible_iterate = match self.vn(itvn).get_def() {
                    None => continue,
                    Some(possible) => possible,
                };
                if self.op(possible_iterate).get_parent() == Some(tail) {
                    if self.op(possible_iterate).is_marker() {
                        continue;
                    }
                    if !self.op_is_moveable(possible_iterate, last_op) {
                        continue;
                    }
                    self.block_while_do_set_state(bl, None, Some(Some(possible_iterate)), Some(Some(def_op)));
                    return;
                }
            } else {
                if count == 3 {
                    continue;
                }
                if self.op(def_op).is_call() || self.op(def_op).is_marker() {
                    continue;
                }
                count += 1;
                path[count as usize] = (def_op, 0);
            }
        }
    }

    pub fn block_find_initializer(&mut self, bl: BlockId, head: BlockId, slot: i32) -> Option<OpId> {
        if self.blocks[head].size_in() != 2 {
            return None;
        }
        let slot = 1 - slot;
        let (_, _, loop_def) = self.block_while_do_state(bl);
        let loop_def = loop_def.expect("whiledo without loop variable");
        let init_vn = self.op(loop_def).get_in(slot);
        let res = self.vn(init_vn).get_def()?;
        if self.op(res).is_marker() {
            return None;
        }
        let initial_block = self.op(res).get_parent().expect("initializer op without block");
        if initial_block != self.blocks[head].get_in(slot) {
            return None;
        }
        let mut last_op = self.block_last_op(initial_block)?;
        if self.blocks[initial_block].size_out() != 1 {
            return None;
        }
        if self.op(last_op).is_branch() {
            last_op = self.op_previous_op(last_op)?;
        }
        self.block_while_do_set_state(bl, Some(Some(res)), None, None);
        Some(last_op)
    }

    pub fn block_test_terminal(&mut self, bl: BlockId, slot: i32) -> Option<OpId> {
        let (_, _, loop_def) = self.block_while_do_state(bl);
        let loop_def = loop_def.expect("whiledo without loop variable");
        let mut vn = self.op(loop_def).get_in(slot);
        let final_op = self.vn(vn).get_def()?;
        let loop_parent = self.op(loop_def).get_parent().expect("loop variable without block");
        let parent_block = self.blocks[loop_parent].get_in(slot);
        let mut res_op = final_op;
        if self.op(final_op).code() == OpCode::Copy && self.op(final_op).not_printed() {
            vn = self.op(final_op).get_in(0);
            res_op = self.vn(vn).get_def()?;
            if self.op(res_op).get_parent() != Some(parent_block) {
                return None;
            }
        }
        if !self.vn(vn).is_explicit() {
            return None;
        }
        if self.op(res_op).not_printed() {
            return None;
        }
        let final_parent = self.op(final_op).get_parent().expect("statement without block");
        let mut last_op = self.block_last_op(final_parent).expect("block without ops");
        if self.op(last_op).is_branch() {
            last_op = self.op_previous_op(last_op).expect("branch without previous op");
        }
        if !self.move_respecting_cover(final_op, last_op) {
            return None;
        }
        Some(res_op)
    }

    pub fn block_test_iterate_form(&self, bl: BlockId) -> bool {
        let (_, iterate_op, loop_def) = self.block_while_do_state(bl);
        let loop_def = loop_def.expect("whiledo without loop variable");
        let target_vn = self.op(loop_def).get_out().expect("loop variable without output");
        let high = self.vn(target_vn).get_high_option();
        let mut path: Vec<(OpId, i32)> = vec![(iterate_op.expect("whiledo without iterate op"), 0)];
        while let Some(node) = path.last_mut() {
            let (node_op, node_slot) = *node;
            if self.op(node_op).num_input() <= node_slot {
                path.pop();
                continue;
            }
            let vn = self.op(node_op).get_in(node_slot);
            node.1 += 1;
            let varnode = self.vn(vn);
            if varnode.is_annotation() {
                continue;
            }
            if varnode.get_high_option() == high {
                return true;
            }
            if varnode.is_explicit() {
                continue;
            }
            match varnode.get_def() {
                None => continue,
                Some(def_op) => path.push((def_op, 0)),
            }
        }
        false
    }

    fn block_while_do_final_transform(
        &mut self,
        bl: BlockId,
        allow_op_moves: bool,
        glb: &mut Architecture,
    ) -> Result<()> {
        self.block_graph_final_transform(bl, allow_op_moves, glb)?;
        if !glb.analyze_for_loops {
            return Ok(());
        }
        if self.blocks[bl].has_overflow_syntax() {
            return Ok(());
        }
        let copy_bl = match self.block_get_front_leaf(bl) {
            None => return Ok(()),
            Some(copy_bl) => copy_bl,
        };
        let head = match self.blocks[copy_bl].sub_block(0) {
            None => return Ok(()),
            Some(head) => head,
        };
        if self.blocks[head].get_type() != BlockType::Basic {
            return Ok(());
        }
        let body = self.blocks[bl].get_block(1);
        let mut last_op = match self.block_last_op(body) {
            None => return Ok(()),
            Some(last_op) => last_op,
        };
        let tail = self.op(last_op).get_parent().expect("op without block");
        if self.blocks[tail].size_out() != 1 {
            return Ok(());
        }
        if self.blocks[tail].get_out(0) != head {
            return Ok(());
        }
        let top = self.blocks[bl].get_block(0);
        let cbranch = match self.block_last_op(top) {
            None => return Ok(()),
            Some(cbranch) => cbranch,
        };
        if self.op(cbranch).code() != OpCode::Cbranch {
            return Ok(());
        }
        if self.op(last_op).is_branch() {
            last_op = match self.op_previous_op(last_op) {
                None => return Ok(()),
                Some(prev) => prev,
            };
        }

        self.block_find_loop_variable(bl, cbranch, head, tail, last_op);
        let (_, iterate_op, _) = self.block_while_do_state(bl);
        let iterate_op = match iterate_op {
            None => return Ok(()),
            Some(iterate_op) => iterate_op,
        };

        if iterate_op != last_op {
            if !allow_op_moves {
                return Ok(());
            }
            self.op_uninsert(iterate_op);
            self.op_insert_after(iterate_op, last_op);
        }

        let tailslot = self.blocks[tail].get_out_rev_index(0);
        let last_op = match self.block_find_initializer(bl, head, tailslot) {
            None => return Ok(()),
            Some(last_op) => last_op,
        };
        let (initialize_op, _, _) = self.block_while_do_state(bl);
        let initialize_op = initialize_op.expect("initializer not recorded");
        if !self.op_is_moveable(initialize_op, last_op) {
            self.block_while_do_set_state(bl, Some(None), None, None);
            return Ok(());
        }
        if initialize_op != last_op {
            if !allow_op_moves {
                return Ok(());
            }
            self.op_uninsert(initialize_op);
            self.op_insert_after(initialize_op, last_op);
        }
        Ok(())
    }

    fn block_while_do_finalize_printing(&mut self, bl: BlockId, glb: &mut Architecture) -> Result<()> {
        self.block_graph_finalize_printing(bl, glb)?;
        let (_, iterate_op, _) = self.block_while_do_state(bl);
        let iterate_op = match iterate_op {
            None => return Ok(()),
            Some(iterate_op) => iterate_op,
        };
        let iterparent = self.op(iterate_op).get_parent().expect("iterate op without block");
        let slot = self.blocks[iterparent].get_out_rev_index(0);
        let tested = self.block_test_terminal(bl, slot);
        self.block_while_do_set_state(bl, None, Some(tested), None);
        if tested.is_none() {
            return Ok(());
        }
        if !self.block_test_iterate_form(bl) {
            self.block_while_do_set_state(bl, None, Some(None), None);
            return Ok(());
        }
        let (initialize_op, _, loop_def) = self.block_while_do_state(bl);
        if initialize_op.is_none() {
            let loop_def = loop_def.expect("whiledo without loop variable");
            let loop_parent = self.op(loop_def).get_parent().expect("loop variable without block");
            self.block_find_initializer(bl, loop_parent, slot);
        }
        let (initialize_op, iterate_op, _) = self.block_while_do_state(bl);
        if initialize_op.is_some() {
            let tested = self.block_test_terminal(bl, 1 - slot);
            self.block_while_do_set_state(bl, Some(tested), None, None);
        }
        self.op_mark_non_printing(iterate_op.expect("iterate op cleared"));
        let (initialize_op, _, _) = self.block_while_do_state(bl);
        if let Some(initialize_op) = initialize_op {
            self.op_mark_non_printing(initialize_op);
        }
        Ok(())
    }

    pub fn block_switch_kind(&self, ind: BlockId) -> BlockKind {
        BlockKind::Switch {
            jump: self.block_get_jumptable(ind),
            caseblocks: Vec::new(),
        }
    }

    pub fn block_switch_add_case(&mut self, bl: BlockId, switchbl: BlockId, casebl: BlockId, gt: u32) -> Result<()> {
        let leaf = self.block_get_front_leaf(casebl).expect("case block without leaf");
        let basicbl = self.blocks[leaf].sub_block(0).expect("case leaf without copied block");
        let inindex = self.blocks[basicbl].get_in_index(switchbl);
        if inindex == -1 {
            return Err(Error::Lowlevel(
                "Case block has become detached from switch".to_string(),
            ));
        }
        let outindex = self.blocks[basicbl].get_in_rev_index(inindex);
        let isexit = if gt != 0 {
            false
        } else {
            self.blocks[casebl].size_out() == 1
        };
        let isdefault = self.blocks[switchbl].is_default_branch(outindex);
        let curcase = CaseOrder {
            block: casebl,
            basicblock: basicbl,
            label: 0,
            depth: 0,
            chain: -1,
            outindex,
            gototype: gt,
            isexit,
            isdefault,
        };
        match &mut self.blocks[bl].kind {
            BlockKind::Switch { caseblocks, .. } => caseblocks.push(curcase),
            _ => panic!("block is not a switch"),
        }
        Ok(())
    }

    pub fn block_grab_case_basic(&mut self, bl: BlockId, switchbl: BlockId, cs: &[BlockId]) -> Result<()> {
        let mut casemap: Vec<i32> = vec![-1; self.blocks[switchbl].size_out() as usize];
        if let BlockKind::Switch { caseblocks, .. } = &mut self.blocks[bl].kind {
            caseblocks.clear();
        }
        for (position, casebl) in cs.iter().enumerate().skip(1) {
            self.block_switch_add_case(bl, switchbl, *casebl, 0)?;
            let outindex = self.blocks[bl].caseblocks()[position - 1].outindex;
            casemap[outindex as usize] = position as i32 - 1;
        }
        let numcases = self.blocks[bl].caseblocks().len();
        for position in 0..numcases {
            let casebl = self.blocks[bl].caseblocks()[position].block;
            if self.blocks[casebl].get_type() == BlockType::Goto {
                let targetbl = self.blocks[casebl].get_goto_target();
                let leaf = self.block_get_front_leaf(targetbl).expect("goto target without leaf");
                let basicbl = self.blocks[leaf].sub_block(0).expect("goto leaf without copied block");
                let inindex = self.blocks[basicbl].get_in_index(switchbl);
                if inindex == -1 {
                    continue;
                }
                let chain = casemap[self.blocks[basicbl].get_in_rev_index(inindex) as usize];
                if let BlockKind::Switch { caseblocks, .. } = &mut self.blocks[bl].kind {
                    caseblocks[position].chain = chain;
                }
            }
        }
        if self.blocks[cs[0]].get_type() == BlockType::MultiGoto {
            let gotoedgeblock = cs[0];
            let numgoto = self.blocks[gotoedgeblock].num_gotos();
            for position in 0..numgoto {
                let target = self.blocks[gotoedgeblock].get_goto(position);
                self.block_switch_add_case(bl, switchbl, target, FlowBlock::F_GOTO_GOTO)?;
            }
        }
        Ok(())
    }

    fn block_switch_finalize_printing(&mut self, bl: BlockId, glb: &mut Architecture) -> Result<()> {
        self.block_graph_finalize_printing(bl, glb)?;
        let (jump, mut caseblocks) = match &mut self.blocks[bl].kind {
            BlockKind::Switch { jump, caseblocks } => (*jump, std::mem::take(caseblocks)),
            _ => panic!("block is not a switch"),
        };
        for position in 0..caseblocks.len() {
            let mut next = caseblocks[position].chain;
            while next != -1 {
                let chained = &mut caseblocks[next as usize];
                if chained.depth != 0 {
                    break;
                }
                chained.depth = -1;
                next = chained.chain;
            }
        }
        let jumpid = jump.expect("switch block without jump table");
        for position in 0..caseblocks.len() {
            let basicblock = caseblocks[position].basicblock;
            let numindices = self.jump_table(jumpid).num_indices_by_block(self, basicblock);
            if numindices > 0 {
                if caseblocks[position].depth == 0 {
                    let indexresult = self.jump_table(jumpid).get_index_by_block(self, basicblock, 0);
                    let ind = match indexresult {
                        Ok(ind) => ind,
                        Err(err) => {
                            self.block_switch_restore_cases(bl, caseblocks);
                            return Err(err);
                        }
                    };
                    let label = self.jump_table(jumpid).get_label_by_index(ind);
                    caseblocks[position].label = label;
                    let mut next = caseblocks[position].chain;
                    let mut depthcount = 1;
                    while next != -1 {
                        let chained = &mut caseblocks[next as usize];
                        if chained.depth > 0 {
                            break;
                        }
                        chained.depth = depthcount;
                        depthcount += 1;
                        chained.label = label;
                        next = chained.chain;
                    }
                }
            } else {
                caseblocks[position].label = 0;
            }
        }
        caseblocks.sort_by(|first, second| {
            ordering_from_less(CaseOrder::compare(first, second), CaseOrder::compare(second, first))
        });
        self.block_switch_restore_cases(bl, caseblocks);
        Ok(())
    }

    fn block_switch_restore_cases(&mut self, bl: BlockId, cases: Vec<CaseOrder>) {
        if let BlockKind::Switch { caseblocks, .. } = &mut self.blocks[bl].kind {
            *caseblocks = cases;
        }
    }

    fn block_switch_jump(&self, bl: BlockId) -> &JumpTable {
        match &self.block(bl).kind {
            BlockKind::Switch { jump, .. } => self.jump_table(jump.expect("switch block without jump table")),
            _ => panic!("block is not a switch"),
        }
    }

    pub fn block_get_num_labels(&self, bl: BlockId, index: i32) -> i32 {
        let basicblock = self.block(bl).caseblocks()[index as usize].basicblock;
        self.block_switch_jump(bl).num_indices_by_block(self, basicblock)
    }

    pub fn block_get_label(&self, bl: BlockId, index: i32, second_index: i32) -> Result<u64> {
        let basicblock = self.block(bl).caseblocks()[index as usize].basicblock;
        let jump = self.block_switch_jump(bl);
        let index = jump.get_index_by_block(self, basicblock, second_index)?;
        Ok(jump.get_label_by_index(index))
    }

    pub fn block_get_switch_type(&mut self, bl: BlockId, glb: &Architecture) -> Result<TypeId> {
        let op = self
            .block_switch_jump(bl)
            .get_indirect_op()
            .expect("switch jump table without indirect op");
        let vn = self.op(op).get_in(0);
        self.vn_get_high_type_read_facing(vn, op, glb)
    }

    pub fn block_get_display_format(&self, bl: BlockId) -> u32 {
        self.block_switch_jump(bl).get_display_format()
    }
}

#[derive(Clone, Debug, Default)]
pub struct BlockMap {
    pub sortlist: Vec<BlockId>,
}

impl BlockMap {
    pub fn new() -> BlockMap {
        BlockMap { sortlist: Vec::new() }
    }

    pub fn resolve_block(&mut self, bt: BlockType, blocks: &mut Arena<BlockId, FlowBlock>) -> Option<BlockId> {
        match bt {
            BlockType::Plain => Some(blocks.alloc(FlowBlock::new(BlockKind::Plain))),
            BlockType::Copy => Some(blocks.alloc(FlowBlock::new_copy(None))),
            BlockType::Graph => Some(blocks.alloc(FlowBlock::new_graph_kind(BlockKind::Graph))),
            _ => None,
        }
    }

    pub fn find_block(list: &[BlockId], ind: i32, blocks: &Arena<BlockId, FlowBlock>) -> Option<BlockId> {
        let mut min: i32 = 0;
        let mut max: i32 = list.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let block = list[mid as usize];
            let index = blocks[block].get_index();
            if index == ind {
                return Some(block);
            }
            if index < ind {
                min = mid + 1;
            } else {
                max = mid - 1;
            }
        }
        None
    }

    pub fn sort_list(&mut self, blocks: &Arena<BlockId, FlowBlock>) {
        self.sortlist.sort_by_key(|block| blocks[*block].get_index());
    }

    pub fn find_level_block(&self, index: i32, blocks: &Arena<BlockId, FlowBlock>) -> Option<BlockId> {
        BlockMap::find_block(&self.sortlist, index, blocks)
    }

    pub fn create_block(&mut self, name: &str, blocks: &mut Arena<BlockId, FlowBlock>) -> Option<BlockId> {
        let bt = FlowBlock::name_to_type(name);
        let bl = self.resolve_block(bt, blocks);
        if let Some(bl) = bl {
            self.sortlist.push(bl);
        }
        bl
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marshal::{XmlDecode, XmlEncode};

    fn indexed_blocks(indices: &[i32]) -> (Arena<BlockId, FlowBlock>, Vec<BlockId>) {
        let mut blocks = Arena::new();
        let ids = indices
            .iter()
            .map(|index| {
                let mut block = FlowBlock::new(BlockKind::Plain);
                block.index = *index;
                blocks.alloc(block)
            })
            .collect();
        (blocks, ids)
    }

    #[test]
    fn type_names_round_trip() {
        assert_eq!(FlowBlock::type_to_name(BlockType::If), "properif");
        assert_eq!(FlowBlock::type_to_name(BlockType::IfNoExit), "ifelse");
        assert_eq!(FlowBlock::type_to_name(BlockType::Ls), "list");
        assert_eq!(FlowBlock::name_to_type("graph"), BlockType::Graph);
        assert_eq!(FlowBlock::name_to_type("copy"), BlockType::Copy);
        assert_eq!(FlowBlock::name_to_type("basic"), BlockType::Plain);
        assert_eq!(FlowBlock::name_to_type("whiledo"), BlockType::Plain);
    }

    #[test]
    fn block_map_sorts_and_finds() {
        let (mut blocks, ids) = indexed_blocks(&[7, 2, 5, 0]);
        let mut resolver = BlockMap::new();
        resolver.sortlist = ids.clone();
        resolver.sort_list(&blocks);
        assert_eq!(resolver.sortlist, vec![ids[3], ids[1], ids[2], ids[0]]);
        assert_eq!(resolver.find_level_block(5, &blocks), Some(ids[2]));
        assert_eq!(resolver.find_level_block(0, &blocks), Some(ids[3]));
        assert_eq!(resolver.find_level_block(3, &blocks), None);
        let created = resolver
            .create_block("graph", &mut blocks)
            .expect("graph block creation failed");
        assert_eq!(blocks[created].get_type(), BlockType::Graph);
        assert_eq!(blocks[created].get_basic_count(), 0);
        let copy = resolver
            .create_block("copy", &mut blocks)
            .expect("copy block creation failed");
        assert_eq!(blocks[copy].get_type(), BlockType::Copy);
        assert_eq!(resolver.sortlist.len(), 6);
    }

    #[test]
    fn block_edge_round_trip() {
        let (blocks, ids) = indexed_blocks(&[3, 9]);
        let edge = BlockEdge::new(ids[1], 0, 4);
        let mut encoder = XmlEncode::new(false);
        edge.encode(&mut encoder, &blocks).expect("edge encoding failed");
        assert_eq!(encoder.as_str(), "<edge end=\"9\" rev=\"4\"/>");
        let mut resolver = BlockMap::new();
        resolver.sortlist = ids.clone();
        resolver.sort_list(&blocks);
        let mut decoder = XmlDecode::new(None, 0);
        decoder
            .ingest_stream(encoder.as_str().as_bytes())
            .expect("edge ingest failed");
        let decoded = BlockEdge::decode(&mut decoder, &resolver, &blocks).expect("edge decoding failed");
        assert_eq!(decoded.point, ids[1]);
        assert_eq!(decoded.reverse_index, 4);
        assert_eq!(decoded.label, 0);
    }

    #[test]
    fn block_edge_decode_unknown_index() {
        let (blocks, ids) = indexed_blocks(&[3]);
        let mut resolver = BlockMap::new();
        resolver.sortlist = ids;
        let mut decoder = XmlDecode::new(None, 0);
        decoder
            .ingest_stream(b"<edge end=\"8\" rev=\"0\"/>")
            .expect("edge ingest failed");
        match BlockEdge::decode(&mut decoder, &resolver, &blocks) {
            Err(Error::Lowlevel(message)) => assert_eq!(message, "Bad serialized edge in block graph"),
            other => panic!("unexpected decode result {:?}", other.map(|edge| edge.reverse_index)),
        }
    }

    #[test]
    fn case_order_compare() {
        let (_, ids) = indexed_blocks(&[0]);
        let make = |label: u64, depth: i32| CaseOrder {
            block: ids[0],
            basicblock: ids[0],
            label,
            depth,
            chain: -1,
            outindex: 0,
            gototype: 0,
            isexit: false,
            isdefault: false,
        };
        assert!(CaseOrder::compare(&make(1, 5), &make(2, 0)));
        assert!(CaseOrder::compare(&make(2, 0), &make(2, 1)));
        assert!(!CaseOrder::compare(&make(2, 1), &make(2, 1)));
    }
}
