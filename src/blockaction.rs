use crate::stdsort::std_sort;
use std::cmp::Ordering;
use std::collections::BTreeMap;

use crate::action::{Action, ActionBase, ActionGroupList};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::block::{BlockId, BlockType};
use crate::define_id;
use crate::error::{Error, Result};
use crate::expression::functional_equality_level;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::oplist::{IntrusiveList, LinkedNode, ListLinks};
use crate::varnode::VarnodeId;

fn ordering_from_less(first_less: bool, second_less: bool) -> Ordering {
    if first_less {
        Ordering::Less
    } else if second_less {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

#[derive(Clone, Debug)]
pub struct FloatingEdge {
    pub top: BlockId,
    pub bottom: BlockId,
}

impl FloatingEdge {
    pub fn new(top: BlockId, bottom: BlockId) -> FloatingEdge {
        FloatingEdge { top, bottom }
    }

    pub fn get_top(&self) -> BlockId {
        self.top
    }

    pub fn get_bottom(&self) -> BlockId {
        self.bottom
    }

    pub fn get_current_edge(&mut self, outedge: &mut i32, graph: BlockId, data: &Funcdata) -> Option<BlockId> {
        while data.block(self.top).get_parent() != Some(graph) {
            self.top = data
                .block(self.top)
                .get_parent()
                .expect("edge end point outside of graph");
        }
        while data.block(self.bottom).get_parent() != Some(graph) {
            self.bottom = data
                .block(self.bottom)
                .get_parent()
                .expect("edge end point outside of graph");
        }
        *outedge = data.block(self.top).get_out_index(self.bottom);
        if *outedge < 0 {
            return None;
        }
        Some(self.top)
    }
}

#[derive(Clone, Debug)]
pub struct LoopBody {
    pub head: BlockId,
    pub tails: Vec<BlockId>,
    pub depth: i32,
    pub uniquecount: i32,
    pub exitblock: Option<BlockId>,
    pub exitedges: Vec<FloatingEdge>,
    pub immed_container: Option<usize>,
}

impl LoopBody {
    pub fn new(head_block: BlockId) -> LoopBody {
        LoopBody {
            head: head_block,
            tails: Vec::new(),
            depth: 0,
            uniquecount: 0,
            exitblock: None,
            exitedges: Vec::new(),
            immed_container: None,
        }
    }

    fn extend_back(body: &mut Vec<BlockId>, curblock: BlockId, data: &mut Funcdata) {
        let sizein = data.block(curblock).size_in();
        for slot in 0..sizein {
            if data.block(curblock).is_goto_in(slot) {
                continue;
            }
            let bl = data.block(curblock).get_in(slot);
            if data.block(bl).is_mark() {
                continue;
            }
            data.block_mut(bl).set_mark();
            body.push(bl);
        }
    }

    pub fn extend_to_container(&self, container: &LoopBody, body: &mut Vec<BlockId>, data: &mut Funcdata) {
        let mut position = 0usize;
        if !data.block(container.head).is_mark() {
            data.block_mut(container.head).set_mark();
            body.push(container.head);
            position = 1;
        }
        for tail in container.tails.iter() {
            if !data.block(*tail).is_mark() {
                data.block_mut(*tail).set_mark();
                body.push(*tail);
            }
        }
        if self.head != container.head {
            LoopBody::extend_back(body, self.head, data);
        }
        while position < body.len() {
            let curblock = body[position];
            position += 1;
            LoopBody::extend_back(body, curblock, data);
        }
    }

    pub fn get_head(&self) -> BlockId {
        self.head
    }

    pub fn update(&mut self, graph: BlockId, data: &Funcdata) -> Option<BlockId> {
        while data.block(self.head).get_parent() != Some(graph) {
            self.head = data.block(self.head).get_parent().expect("loop head outside of graph");
        }
        for slot in 0..self.tails.len() {
            let mut bottom = self.tails[slot];
            while data.block(bottom).get_parent() != Some(graph) {
                bottom = data.block(bottom).get_parent().expect("loop tail outside of graph");
            }
            self.tails[slot] = bottom;
            if bottom != self.head {
                return Some(bottom);
            }
        }
        let head = data.block(self.head);
        for slot in (0..head.size_out()).rev() {
            if head.get_out(slot) == self.head {
                return Some(self.head);
            }
        }
        None
    }

    pub fn add_tail(&mut self, bl: BlockId) {
        self.tails.push(bl);
    }

    pub fn get_exit_block(&self) -> Option<BlockId> {
        self.exitblock
    }

    pub fn find_base(&mut self, body: &mut Vec<BlockId>, data: &mut Funcdata) {
        data.block_mut(self.head).set_mark();
        body.push(self.head);
        for tail in self.tails.iter() {
            if !data.block(*tail).is_mark() {
                data.block_mut(*tail).set_mark();
                body.push(*tail);
            }
        }
        self.uniquecount = body.len() as i32;
        let mut position = 1usize;
        while position < body.len() {
            let curblock = body[position];
            position += 1;
            LoopBody::extend_back(body, curblock, data);
        }
    }

    pub fn extend(&self, body: &mut Vec<BlockId>, data: &mut Funcdata) {
        let mut trial = Vec::new();
        let mut position = 0usize;
        while position < body.len() {
            let bl = body[position];
            position += 1;
            let sizeout = data.block(bl).size_out();
            for slot in 0..sizeout {
                if data.block(bl).is_goto_out(slot) {
                    continue;
                }
                let curbl = data.block(bl).get_out(slot);
                if data.block(curbl).is_mark() {
                    continue;
                }
                if Some(curbl) == self.exitblock {
                    continue;
                }
                let mut count = data.block(curbl).get_visit_count();
                if count == 0 {
                    trial.push(curbl);
                }
                count += 1;
                data.block_mut(curbl).set_visit_count(count);
                if count == data.block(curbl).size_in() {
                    data.block_mut(curbl).set_mark();
                    body.push(curbl);
                }
            }
        }
        for bl in trial {
            data.block_mut(bl).set_visit_count(0);
        }
    }

    pub fn find_exit(&mut self, body: &[BlockId], container: Option<&LoopBody>, data: &mut Funcdata) {
        let mut trialexit = Vec::new();
        for tail in self.tails.iter() {
            let tailblock = data.block(*tail);
            for slot in 0..tailblock.size_out() {
                if tailblock.is_goto_out(slot) {
                    continue;
                }
                let curbl = tailblock.get_out(slot);
                if !data.block(curbl).is_mark() {
                    if container.is_none() {
                        self.exitblock = Some(curbl);
                        return;
                    }
                    trialexit.push(curbl);
                }
            }
        }
        for (position, bl) in body.iter().enumerate() {
            if position > 0 && (position as i32) < self.uniquecount {
                continue;
            }
            let block = data.block(*bl);
            for slot in 0..block.size_out() {
                if block.is_goto_out(slot) {
                    continue;
                }
                let curbl = block.get_out(slot);
                if !data.block(curbl).is_mark() {
                    if container.is_none() {
                        self.exitblock = Some(curbl);
                        return;
                    }
                    trialexit.push(curbl);
                }
            }
        }
        self.exitblock = None;
        if trialexit.is_empty() {
            return;
        }
        if let Some(container) = container {
            let mut extension = Vec::new();
            self.extend_to_container(container, &mut extension, data);
            for bl in trialexit.iter() {
                if data.block(*bl).is_mark() {
                    self.exitblock = Some(*bl);
                    break;
                }
            }
            LoopBody::clear_marks(&extension, data);
        }
    }

    pub fn order_tails(&mut self, data: &Funcdata) {
        if self.tails.len() <= 1 {
            return;
        }
        let exitblock = match self.exitblock {
            None => return,
            Some(exitblock) => exitblock,
        };
        let mut prefindex = 0usize;
        while prefindex < self.tails.len() {
            let trial = data.block(self.tails[prefindex]);
            if (0..trial.size_out()).any(|slot| trial.get_out(slot) == exitblock) {
                break;
            }
            prefindex += 1;
        }
        if prefindex >= self.tails.len() {
            return;
        }
        if prefindex == 0 {
            return;
        }
        self.tails.swap(0, prefindex);
    }

    pub fn label_exit_edges(&mut self, body: &[BlockId], data: &mut Funcdata) {
        let mut toexitblock = Vec::new();
        for curblock in body.iter().skip(self.uniquecount as usize) {
            self.label_block_exits(*curblock, &mut toexitblock, data);
        }
        let head = self.head;
        self.label_block_exits(head, &mut toexitblock, data);
        for position in (0..self.tails.len()).rev() {
            let curblock = self.tails[position];
            if curblock == self.head {
                continue;
            }
            self.label_block_exits(curblock, &mut toexitblock, data);
        }
        let exitblock = self.exitblock;
        for bl in toexitblock {
            self.exitedges
                .push(FloatingEdge::new(bl, exitblock.expect("exit edge without exit block")));
        }
    }

    fn label_block_exits(&mut self, curblock: BlockId, toexitblock: &mut Vec<BlockId>, data: &Funcdata) {
        let block = data.block(curblock);
        for slot in 0..block.size_out() {
            if block.is_goto_out(slot) {
                continue;
            }
            let bl = block.get_out(slot);
            if Some(bl) == self.exitblock {
                toexitblock.push(curblock);
                continue;
            }
            if !data.block(bl).is_mark() {
                self.exitedges.push(FloatingEdge::new(curblock, bl));
            }
        }
    }

    pub fn label_containments(
        loops: &mut [LoopBody],
        index: usize,
        body: &[BlockId],
        looporder: &[usize],
        data: &mut Funcdata,
    ) {
        let mut containlist = Vec::new();
        let head = loops[index].head;
        for curblock in body.iter() {
            if *curblock != head
                && let Some(subloop) = LoopBody::find(loops, *curblock, looporder, data)
            {
                containlist.push(subloop);
                loops[subloop].depth += 1;
            }
        }
        for lb in containlist {
            let replace = match loops[lb].immed_container {
                None => true,
                Some(container) => loops[container].depth < loops[index].depth,
            };
            if replace {
                loops[lb].immed_container = Some(index);
            }
        }
    }

    pub fn emit_likely_edges(&mut self, likely: &mut Vec<FloatingEdge>, graph: BlockId, data: &Funcdata) {
        while data.block(self.head).get_parent() != Some(graph) {
            self.head = data.block(self.head).get_parent().expect("loop head outside of graph");
        }
        if let Some(mut exitblock) = self.exitblock {
            while data.block(exitblock).get_parent() != Some(graph) {
                exitblock = data.block(exitblock).get_parent().expect("loop exit outside of graph");
            }
            self.exitblock = Some(exitblock);
        }
        for slot in 0..self.tails.len() {
            let mut tail = self.tails[slot];
            while data.block(tail).get_parent() != Some(graph) {
                tail = data.block(tail).get_parent().expect("loop tail outside of graph");
            }
            self.tails[slot] = tail;
            if Some(tail) == self.exitblock {
                self.exitblock = None;
            }
        }
        let mut holdin: Option<BlockId> = None;
        let mut holdout: Option<BlockId> = None;
        let count = self.exitedges.len();
        let mut position = 0usize;
        while position < count {
            let mut outedge = 0;
            let inbl = self.exitedges[position].get_current_edge(&mut outedge, graph, data);
            position += 1;
            let inbl = match inbl {
                None => continue,
                Some(inbl) => inbl,
            };
            let outbl = data.block(inbl).get_out(outedge);
            if position == count && Some(outbl) == self.exitblock {
                holdin = Some(inbl);
                holdout = Some(outbl);
                break;
            }
            likely.push(FloatingEdge::new(inbl, outbl));
        }
        for slot in (0..self.tails.len()).rev() {
            if let (Some(holdin), Some(holdout)) = (holdin, holdout)
                && slot == 0
            {
                likely.push(FloatingEdge::new(holdin, holdout));
            }
            let tail = self.tails[slot];
            let tailblock = data.block(tail);
            for outslot in 0..tailblock.size_out() {
                if tailblock.get_out(outslot) == self.head {
                    likely.push(FloatingEdge::new(tail, self.head));
                }
            }
        }
    }

    pub fn set_exit_marks(&mut self, graph: BlockId, data: &mut Funcdata) {
        for position in 0..self.exitedges.len() {
            let mut outedge = 0;
            if let Some(inloop) = self.exitedges[position].get_current_edge(&mut outedge, graph, data) {
                data.block_set_loop_exit(inloop, outedge);
            }
        }
    }

    pub fn clear_exit_marks(&mut self, graph: BlockId, data: &mut Funcdata) {
        for position in 0..self.exitedges.len() {
            let mut outedge = 0;
            if let Some(inloop) = self.exitedges[position].get_current_edge(&mut outedge, graph, data) {
                data.block_clear_loop_exit(inloop, outedge);
            }
        }
    }

    pub fn less_than(&self, op2: &LoopBody) -> bool {
        self.depth > op2.depth
    }

    pub fn merge_identical_heads(loops: &mut [LoopBody], looporder: &mut Vec<usize>) {
        let mut slot = 0usize;
        let mut next = slot + 1;
        let mut curbody = looporder[slot];
        while next < looporder.len() {
            let nextbody = looporder[next];
            next += 1;
            if loops[nextbody].head == loops[curbody].head {
                let tail = loops[nextbody].tails[0];
                loops[curbody].add_tail(tail);
            } else {
                slot += 1;
                looporder[slot] = nextbody;
                curbody = nextbody;
            }
        }
        slot += 1;
        looporder.truncate(slot);
    }

    pub fn compare_ends(loops: &[LoopBody], first: usize, second: usize, data: &Funcdata) -> bool {
        let aindex = data.block(loops[first].head).get_index();
        let bindex = data.block(loops[second].head).get_index();
        if aindex != bindex {
            return aindex < bindex;
        }
        let aindex = data.block(loops[first].tails[0]).get_index();
        let bindex = data.block(loops[second].tails[0]).get_index();
        aindex < bindex
    }

    pub fn compare_head(loops: &[LoopBody], first: usize, looptop: BlockId, data: &Funcdata) -> i32 {
        let aindex = data.block(loops[first].head).get_index();
        let bindex = data.block(looptop).get_index();
        if aindex != bindex {
            return if aindex < bindex { -1 } else { 1 };
        }
        0
    }

    pub fn find(loops: &[LoopBody], looptop: BlockId, looporder: &[usize], data: &Funcdata) -> Option<usize> {
        let mut min: i32 = 0;
        let mut max: i32 = looporder.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let comp = LoopBody::compare_head(loops, looporder[mid as usize], looptop, data);
            if comp == 0 {
                return Some(looporder[mid as usize]);
            }
            if comp < 0 {
                min = mid + 1;
            } else {
                max = mid - 1;
            }
        }
        None
    }

    pub fn clear_marks(body: &[BlockId], data: &mut Funcdata) {
        for bl in body.iter() {
            data.block_mut(*bl).clear_mark();
        }
    }
}

define_id!(BranchId);
define_id!(TraceId);

#[derive(Clone, Debug)]
pub struct BranchPoint {
    pub parent: Option<BranchId>,
    pub pathout: i32,
    pub top: Option<BlockId>,
    pub paths: Vec<TraceId>,
    pub depth: i32,
    pub ismark: bool,
}

impl BranchPoint {
    pub fn new() -> BranchPoint {
        BranchPoint {
            parent: None,
            pathout: -1,
            top: None,
            paths: Vec::new(),
            depth: 0,
            ismark: false,
        }
    }
}

impl Default for BranchPoint {
    fn default() -> BranchPoint {
        BranchPoint::new()
    }
}

#[derive(Clone, Debug)]
pub struct BlockTrace {
    pub flags: u32,
    pub top: BranchId,
    pub pathout: i32,
    pub bottom: Option<BlockId>,
    pub destnode: Option<BlockId>,
    pub edgelump: i32,
    pub activeiter: ListLinks<TraceId>,
    pub derivedbp: Option<BranchId>,
}

impl BlockTrace {
    pub const F_ACTIVE: u32 = 1;
    pub const F_TERMINAL: u32 = 2;

    pub fn new_root(root: BranchId, po: i32, bl: BlockId) -> BlockTrace {
        BlockTrace {
            flags: 0,
            top: root,
            pathout: po,
            bottom: None,
            destnode: Some(bl),
            edgelump: 1,
            activeiter: ListLinks::default(),
            derivedbp: None,
        }
    }

    pub fn is_active(&self) -> bool {
        (self.flags & BlockTrace::F_ACTIVE) != 0
    }

    pub fn is_terminal(&self) -> bool {
        (self.flags & BlockTrace::F_TERMINAL) != 0
    }
}

impl LinkedNode<TraceId> for BlockTrace {
    fn links(&self, _slot: usize) -> &ListLinks<TraceId> {
        &self.activeiter
    }

    fn links_mut(&mut self, _slot: usize) -> &mut ListLinks<TraceId> {
        &mut self.activeiter
    }
}

#[derive(Clone, Debug)]
pub struct BadEdgeScore {
    pub exitproto: BlockId,
    pub trace: TraceId,
    pub distance: i32,
    pub terminal: i32,
    pub siblingedge: i32,
}

impl BadEdgeScore {
    pub fn compare_final(&self, op2: &BadEdgeScore, dag: &TraceDag) -> bool {
        if self.siblingedge != op2.siblingedge {
            return op2.siblingedge < self.siblingedge;
        }
        if self.terminal != op2.terminal {
            return self.terminal < op2.terminal;
        }
        if self.distance != op2.distance {
            return self.distance < op2.distance;
        }
        let depth1 = dag.branches[dag.traces[self.trace].top].depth;
        let depth2 = dag.branches[dag.traces[op2.trace].top].depth;
        depth1 < depth2
    }

    pub fn less_than(&self, op2: &BadEdgeScore, dag: &TraceDag, data: &Funcdata) -> bool {
        let thisind = data.block(self.exitproto).get_index();
        let op2ind = data.block(op2.exitproto).get_index();
        if thisind != op2ind {
            return thisind < op2ind;
        }
        let trace1 = &dag.traces[self.trace];
        let trace2 = &dag.traces[op2.trace];
        let thisind = match dag.branches[trace1.top].top {
            Some(bl) => data.block(bl).get_index(),
            None => -1,
        };
        let op2ind = match dag.branches[trace2.top].top {
            Some(bl) => data.block(bl).get_index(),
            None => -1,
        };
        if thisind != op2ind {
            return thisind < op2ind;
        }
        trace1.pathout < trace2.pathout
    }
}

pub struct TraceDag {
    pub rootlist: Vec<BlockId>,
    pub branches: Arena<BranchId, BranchPoint>,
    pub traces: Arena<TraceId, BlockTrace>,
    pub branchlist: Vec<BranchId>,
    pub activecount: i32,
    pub missedactivecount: i32,
    pub activetrace: IntrusiveList<TraceId>,
    pub current_activeiter: Option<TraceId>,
    pub finishblock: Option<BlockId>,
}

impl TraceDag {
    pub fn new() -> TraceDag {
        TraceDag {
            rootlist: Vec::new(),
            branches: Arena::new(),
            traces: Arena::new(),
            branchlist: Vec::new(),
            activecount: 0,
            missedactivecount: 0,
            activetrace: IntrusiveList::new(0),
            current_activeiter: None,
            finishblock: None,
        }
    }

    pub fn branch_new_from_trace(&mut self, parenttrace: TraceId, data: &Funcdata) -> BranchId {
        let trace = &self.traces[parenttrace];
        let parent = trace.top;
        let branch = BranchPoint {
            parent: Some(parent),
            pathout: trace.pathout,
            top: trace.destnode,
            paths: Vec::new(),
            depth: self.branches[parent].depth + 1,
            ismark: false,
        };
        let bp = self.branches.alloc(branch);
        self.branch_create_traces(bp, data);
        bp
    }

    pub fn branch_create_traces(&mut self, bp: BranchId, data: &Funcdata) {
        let top = self.branches[bp].top.expect("branch point without block");
        let topblock = data.block(top);
        for slot in 0..topblock.size_out() {
            if !topblock.is_loop_dag_out(slot) {
                continue;
            }
            let pathout = self.branches[bp].paths.len() as i32;
            let trace = self.trace_new_edge(bp, pathout, slot, data);
            self.branches[bp].paths.push(trace);
        }
    }

    pub fn branch_mark_path(&mut self, bp: BranchId) {
        let mut cur = Some(bp);
        while let Some(branch) = cur {
            let point = &mut self.branches[branch];
            point.ismark = !point.ismark;
            cur = point.parent;
        }
    }

    pub fn branch_distance(&mut self, bp: BranchId, op2: BranchId) -> i32 {
        let depth = self.branches[bp].depth;
        let op2depth = self.branches[op2].depth;
        let mut cur = Some(op2);
        while let Some(branch) = cur {
            let point = &self.branches[branch];
            if point.ismark {
                return (depth - point.depth) + (op2depth - point.depth);
            }
            cur = point.parent;
        }
        depth + op2depth + 1
    }

    pub fn branch_get_path_start(&self, bp: BranchId, index: i32, data: &Funcdata) -> Option<BlockId> {
        let top = data.block(self.branches[bp].top?);
        let mut res = 0;
        for slot in 0..top.size_out() {
            if !top.is_loop_dag_out(slot) {
                continue;
            }
            if res == index {
                return Some(top.get_out(slot));
            }
            res += 1;
        }
        None
    }

    pub fn trace_new_edge(&mut self, top_branch: BranchId, po: i32, eo: i32, data: &Funcdata) -> TraceId {
        let bottom = self.branches[top_branch].top.expect("branch point without block");
        let destnode = data.block(bottom).get_out(eo);
        self.traces.alloc(BlockTrace {
            flags: 0,
            top: top_branch,
            pathout: po,
            bottom: Some(bottom),
            destnode: Some(destnode),
            edgelump: 1,
            activeiter: ListLinks::default(),
            derivedbp: None,
        })
    }

    pub fn remove_trace(&mut self, trace: TraceId, likelygoto: &mut Vec<FloatingEdge>, data: &mut Funcdata) {
        let (bottom, destnode, edgelump, parentbp, pathout) = {
            let record = &self.traces[trace];
            (
                record.bottom,
                record.destnode,
                record.edgelump,
                record.top,
                record.pathout,
            )
        };
        let destnode = destnode.expect("removed trace without destination");
        likelygoto.push(FloatingEdge::new(
            bottom.expect("removed trace without bottom"),
            destnode,
        ));
        let visits = data.block(destnode).get_visit_count() + edgelump;
        data.block_mut(destnode).set_visit_count(visits);

        if bottom != self.branches[parentbp].top {
            let record = &mut self.traces[trace];
            record.flags |= BlockTrace::F_TERMINAL;
            record.bottom = None;
            record.destnode = None;
            record.edgelump = 0;
            return;
        }
        self.remove_active(trace);
        let size = self.branches[parentbp].paths.len();
        for slot in (pathout as usize + 1)..size {
            let movedtrace = self.branches[parentbp].paths[slot];
            self.traces[movedtrace].pathout -= 1;
            if let Some(derivedbp) = self.traces[movedtrace].derivedbp {
                self.branches[derivedbp].pathout -= 1;
            }
            self.branches[parentbp].paths[slot - 1] = movedtrace;
        }
        self.branches[parentbp].paths.pop();
        self.traces.remove(trace);
    }

    pub fn process_exit_conflict(&mut self, badedgelist: &mut [BadEdgeScore], start: usize, end: usize) {
        let mut start = start;
        while start != end {
            let mut iter = start + 1;
            let startbp = self.traces[badedgelist[start].trace].top;
            if iter != end {
                self.branch_mark_path(startbp);
                loop {
                    let iterbp = self.traces[badedgelist[iter].trace].top;
                    if startbp == iterbp {
                        badedgelist[start].siblingedge += 1;
                        badedgelist[iter].siblingedge += 1;
                    }
                    let dist = self.branch_distance(startbp, iterbp);
                    if badedgelist[start].distance == -1 || badedgelist[start].distance > dist {
                        badedgelist[start].distance = dist;
                    }
                    if badedgelist[iter].distance == -1 || badedgelist[iter].distance > dist {
                        badedgelist[iter].distance = dist;
                    }
                    iter += 1;
                    if iter == end {
                        break;
                    }
                }
                self.branch_mark_path(startbp);
            }
            start += 1;
        }
    }

    pub fn select_bad_edge(&mut self, data: &Funcdata) -> TraceId {
        let mut badedgelist = Vec::new();
        for trace in self.activetrace.iter(&self.traces) {
            let record = &self.traces[trace];
            if record.is_terminal() {
                continue;
            }
            if self.branches[record.top].top.is_none() && record.bottom.is_none() {
                continue;
            }
            let exitproto = record.destnode.expect("active trace without destination");
            badedgelist.push(BadEdgeScore {
                exitproto,
                trace,
                distance: -1,
                siblingedge: 0,
                terminal: if data.block(exitproto).size_out() == 0 { 1 } else { 0 },
            });
        }
        badedgelist.sort_by(|first, second| {
            ordering_from_less(first.less_than(second, self, data), second.less_than(first, self, data))
        });

        let mut iter = 0usize;
        let mut startiter = iter;
        let mut curbl = badedgelist.first().expect("no candidate unstructured edge").exitproto;
        let mut samenodecount = 1;
        iter += 1;
        while iter < badedgelist.len() {
            if curbl == badedgelist[iter].exitproto {
                samenodecount += 1;
                iter += 1;
            } else {
                if samenodecount > 1 {
                    self.process_exit_conflict(&mut badedgelist, startiter, iter);
                }
                curbl = badedgelist[iter].exitproto;
                startiter = iter;
                samenodecount = 1;
                iter += 1;
            }
        }
        if samenodecount > 1 {
            self.process_exit_conflict(&mut badedgelist, startiter, iter);
        }

        let mut maxiter = 0usize;
        for position in 1..badedgelist.len() {
            if badedgelist[maxiter].compare_final(&badedgelist[position], self) {
                maxiter = position;
            }
        }
        badedgelist[maxiter].trace
    }

    pub fn insert_active(&mut self, trace: TraceId) {
        self.activetrace.push_back(&mut self.traces, trace);
        self.traces[trace].flags |= BlockTrace::F_ACTIVE;
        self.activecount += 1;
    }

    pub fn remove_active(&mut self, trace: TraceId) {
        self.activetrace.remove(&mut self.traces, trace);
        self.traces[trace].flags &= !BlockTrace::F_ACTIVE;
        self.activecount -= 1;
    }

    pub fn check_open(&mut self, trace: TraceId, data: &Funcdata) -> bool {
        let record = &self.traces[trace];
        if record.is_terminal() {
            return false;
        }
        let mut isroot = false;
        if self.branches[record.top].depth == 0 {
            if record.bottom.is_none() {
                return true;
            }
            isroot = true;
        }
        let bl = record.destnode.expect("open trace without destination");
        if Some(bl) == self.finishblock && !isroot {
            return false;
        }
        let block = data.block(bl);
        let ignore = record.edgelump + block.get_visit_count();
        let mut count = 0;
        for slot in 0..block.size_in() {
            if block.is_loop_dag_in(slot) {
                count += 1;
                if count > ignore {
                    return false;
                }
            }
        }
        true
    }

    pub fn open_branch(&mut self, parent: TraceId, data: &Funcdata) -> Option<TraceId> {
        let newbranch = self.branch_new_from_trace(parent, data);
        self.traces[parent].derivedbp = Some(newbranch);
        if self.branches[newbranch].paths.is_empty() {
            self.branches.remove(newbranch);
            let record = &mut self.traces[parent];
            record.derivedbp = None;
            record.flags |= BlockTrace::F_TERMINAL;
            record.bottom = None;
            record.destnode = None;
            record.edgelump = 0;
            return Some(parent);
        }
        self.remove_active(parent);
        self.branchlist.push(newbranch);
        let paths = self.branches[newbranch].paths.clone();
        for path in paths.iter() {
            self.insert_active(*path);
        }
        Some(paths[0])
    }

    pub fn check_retirement(&mut self, trace: TraceId, exitblock: &mut Option<BlockId>) -> bool {
        let record = &self.traces[trace];
        if record.pathout != 0 {
            return false;
        }
        let bp = &self.branches[record.top];
        if bp.depth == 0 {
            for path in bp.paths.iter() {
                let curtrace = &self.traces[*path];
                if !curtrace.is_active() {
                    return false;
                }
                if !curtrace.is_terminal() {
                    return false;
                }
            }
            return true;
        }
        let mut outblock: Option<BlockId> = None;
        for path in bp.paths.iter() {
            let curtrace = &self.traces[*path];
            if !curtrace.is_active() {
                return false;
            }
            if curtrace.is_terminal() {
                continue;
            }
            if outblock == curtrace.destnode {
                continue;
            }
            if outblock.is_some() {
                return false;
            }
            outblock = curtrace.destnode;
        }
        *exitblock = outblock;
        true
    }

    pub fn retire_branch(&mut self, bp: BranchId, exitblock: Option<BlockId>) -> Option<TraceId> {
        let mut edgeout_bl: Option<BlockId> = None;
        let mut edgelump_sum = 0;
        let paths = self.branches[bp].paths.clone();
        for curtrace in paths {
            if !self.traces[curtrace].is_terminal() {
                edgelump_sum += self.traces[curtrace].edgelump;
                if edgeout_bl.is_none() {
                    edgeout_bl = self.traces[curtrace].bottom;
                }
            }
            self.remove_active(curtrace);
        }
        if self.branches[bp].depth == 0 {
            return self.activetrace.front();
        }
        if let Some(parent) = self.branches[bp].parent {
            let pathout = self.branches[bp].pathout as usize;
            let parenttrace = self.branches[parent].paths[pathout];
            let record = &mut self.traces[parenttrace];
            record.derivedbp = None;
            match edgeout_bl {
                None => {
                    record.flags |= BlockTrace::F_TERMINAL;
                    record.bottom = None;
                    record.destnode = None;
                    record.edgelump = 0;
                }
                Some(edgeout) => {
                    record.bottom = Some(edgeout);
                    record.destnode = exitblock;
                    record.edgelump = edgelump_sum;
                }
            }
            self.insert_active(parenttrace);
            return Some(parenttrace);
        }
        self.activetrace.front()
    }

    pub fn clear_visit_count(&mut self, likelygoto: &[FloatingEdge], data: &mut Funcdata) {
        for edge in likelygoto.iter() {
            data.block_mut(edge.get_bottom()).set_visit_count(0);
        }
    }

    pub fn add_root(&mut self, root: BlockId) {
        self.rootlist.push(root);
    }

    pub fn initialize(&mut self) {
        let root_branch = self.branches.alloc(BranchPoint::new());
        self.branchlist.push(root_branch);
        let rootlist = self.rootlist.clone();
        for root in rootlist {
            let pathout = self.branches[root_branch].paths.len() as i32;
            let newtrace = self.traces.alloc(BlockTrace::new_root(root_branch, pathout, root));
            self.branches[root_branch].paths.push(newtrace);
            self.insert_active(newtrace);
        }
    }

    pub fn push_branches(&mut self, likelygoto: &mut Vec<FloatingEdge>, data: &mut Funcdata) {
        let mut exitblock: Option<BlockId> = None;
        self.current_activeiter = self.activetrace.front();
        self.missedactivecount = 0;
        while self.activecount > 0 {
            if self.current_activeiter.is_none() {
                self.current_activeiter = self.activetrace.front();
            }
            let curtrace = self.current_activeiter.expect("active trace list is empty");
            if self.missedactivecount >= self.activecount {
                let badtrace = self.select_bad_edge(data);
                self.remove_trace(badtrace, likelygoto, data);
                self.current_activeiter = self.activetrace.front();
                self.missedactivecount = 0;
            } else if self.check_retirement(curtrace, &mut exitblock) {
                let top = self.traces[curtrace].top;
                self.current_activeiter = self.retire_branch(top, exitblock);
                self.missedactivecount = 0;
            } else if self.check_open(curtrace, data) {
                self.current_activeiter = self.open_branch(curtrace, data);
                self.missedactivecount = 0;
            } else {
                self.missedactivecount += 1;
                self.current_activeiter = self.activetrace.next(&self.traces, curtrace);
            }
        }
        self.clear_visit_count(likelygoto, data);
    }

    pub fn set_finish_block(&mut self, bl: BlockId) {
        self.finishblock = Some(bl);
    }
}

impl Default for TraceDag {
    fn default() -> TraceDag {
        TraceDag::new()
    }
}

pub struct CollapseStructure {
    pub finaltrace: bool,
    pub likelylistfull: bool,
    pub likelygoto: Vec<FloatingEdge>,
    pub likelyiter: usize,
    pub loopbody: Vec<LoopBody>,
    pub loopbody_order: Vec<usize>,
    pub loopbodyiter: usize,
    pub graph: BlockId,
    pub dataflow_changecount: i32,
}

impl CollapseStructure {
    pub fn new(group: BlockId) -> CollapseStructure {
        CollapseStructure {
            finaltrace: false,
            likelylistfull: false,
            likelygoto: Vec::new(),
            likelyiter: 0,
            loopbody: Vec::new(),
            loopbody_order: Vec::new(),
            loopbodyiter: 0,
            graph: group,
            dataflow_changecount: 0,
        }
    }

    fn negate(&mut self, bl: BlockId, data: &mut Funcdata) {
        if data.block_negate_condition(bl, true) {
            self.dataflow_changecount += 1;
        }
    }

    pub fn check_switch_skips(
        &mut self,
        switchbl: BlockId,
        exitblock: Option<BlockId>,
        data: &mut Funcdata,
    ) -> Result<bool> {
        let exitblock = match exitblock {
            None => return Ok(true),
            Some(exitblock) => exitblock,
        };
        let sizeout = data.block(switchbl).size_out();
        let mut defaultnottoexit = false;
        let mut anyskiptoexit = false;
        for edgenum in 0..sizeout {
            let block = data.block(switchbl);
            if block.get_out(edgenum) == exitblock {
                if !block.is_default_branch(edgenum) {
                    anyskiptoexit = true;
                }
            } else if block.is_default_branch(edgenum) {
                defaultnottoexit = true;
            }
        }
        if !anyskiptoexit {
            return Ok(true);
        }
        if !defaultnottoexit
            && data.block(switchbl).get_type() == BlockType::MultiGoto
            && data.block(switchbl).has_default_goto()
        {
            defaultnottoexit = true;
        }
        if !defaultnottoexit {
            return Ok(true);
        }
        for edgenum in 0..sizeout {
            let block = data.block(switchbl);
            if block.get_out(edgenum) == exitblock && !block.is_default_branch(edgenum) {
                data.block_set_goto_branch(switchbl, edgenum)?;
            }
        }
        Ok(false)
    }

    pub fn only_reachable_from_root(&mut self, root: BlockId, body: &mut Vec<BlockId>, data: &mut Funcdata) {
        let mut trial = Vec::new();
        let mut position = 0usize;
        data.block_mut(root).set_mark();
        body.push(root);
        while position < body.len() {
            let bl = body[position];
            position += 1;
            let sizeout = data.block(bl).size_out();
            for slot in 0..sizeout {
                let curbl = data.block(bl).get_out(slot);
                if data.block(curbl).is_mark() {
                    continue;
                }
                let mut count = data.block(curbl).get_visit_count();
                if count == 0 {
                    trial.push(curbl);
                }
                count += 1;
                data.block_mut(curbl).set_visit_count(count);
                if count == data.block(curbl).size_in() {
                    data.block_mut(curbl).set_mark();
                    body.push(curbl);
                }
            }
        }
        for bl in trial {
            data.block_mut(bl).set_visit_count(0);
        }
    }

    pub fn mark_exits_as_gotos(&mut self, body: &mut [BlockId], data: &mut Funcdata) -> Result<i32> {
        let mut changecount = 0;
        for bl in body.iter() {
            let sizeout = data.block(*bl).size_out();
            for slot in 0..sizeout {
                let curbl = data.block(*bl).get_out(slot);
                if !data.block(curbl).is_mark() {
                    data.block_set_goto_branch(*bl, slot)?;
                    changecount += 1;
                }
            }
        }
        Ok(changecount)
    }

    pub fn clip_extra_roots(&mut self, data: &mut Funcdata) -> Result<bool> {
        let mut index = 1;
        while index < data.block(self.graph).get_size() {
            let bl = data.block(self.graph).get_block(index);
            index += 1;
            if data.block(bl).size_in() != 0 {
                continue;
            }
            let mut body = Vec::new();
            self.only_reachable_from_root(bl, &mut body, data);
            let count = self.mark_exits_as_gotos(&mut body, data)?;
            LoopBody::clear_marks(&body, data);
            if count != 0 {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn label_loops(&mut self, looporder: &mut Vec<usize>, data: &mut Funcdata) -> Result<()> {
        let list = data.block(self.graph).get_list().to_vec();
        for bl in list {
            let sizein = data.block(bl).size_in();
            for slot in 0..sizein {
                if data.block(bl).is_back_edge_in(slot) {
                    let loopbottom = data.block(bl).get_in(slot);
                    let mut curbody = LoopBody::new(bl);
                    curbody.add_tail(loopbottom);
                    self.loopbody.push(curbody);
                    looporder.push(self.loopbody.len() - 1);
                }
            }
        }
        let loops = &self.loopbody;
        std_sort(looporder, |first, second| {
            LoopBody::compare_ends(loops, *first, *second, data)
        });
        Ok(())
    }

    pub fn order_loop_bodies(&mut self, data: &mut Funcdata) -> Result<()> {
        let mut looporder = Vec::new();
        self.label_loops(&mut looporder, data)?;
        self.loopbody_order = (0..self.loopbody.len()).collect();
        if !self.loopbody.is_empty() {
            let oldsize = looporder.len();
            LoopBody::merge_identical_heads(&mut self.loopbody, &mut looporder);
            if oldsize != looporder.len() {
                self.loopbody_order.retain(|index| looporder.contains(index));
            }
            let order = self.loopbody_order.clone();
            for index in order.iter() {
                let mut body = Vec::new();
                self.loopbody[*index].find_base(&mut body, data);
                LoopBody::label_containments(&mut self.loopbody, *index, &body, &looporder, data);
                LoopBody::clear_marks(&body, data);
            }
            let loops = &self.loopbody;
            self.loopbody_order.sort_by(|first, second| {
                ordering_from_less(
                    loops[*first].less_than(&loops[*second]),
                    loops[*second].less_than(&loops[*first]),
                )
            });
            let order = self.loopbody_order.clone();
            for index in order.iter() {
                let mut body = Vec::new();
                self.loopbody[*index].find_base(&mut body, data);
                let container = self.loopbody[*index]
                    .immed_container
                    .map(|container| self.loopbody[container].clone());
                self.loopbody[*index].find_exit(&body, container.as_ref(), data);
                self.loopbody[*index].order_tails(data);
                self.loopbody[*index].extend(&mut body, data);
                self.loopbody[*index].label_exit_edges(&body, data);
                LoopBody::clear_marks(&body, data);
            }
        }
        self.likelylistfull = false;
        self.loopbodyiter = 0;
        Ok(())
    }

    pub fn update_loop_body(&mut self, data: &mut Funcdata) -> Result<bool> {
        if self.finaltrace {
            return Ok(false);
        }
        let mut loopbottom: Option<BlockId> = None;
        let mut looptop: Option<BlockId> = None;
        while self.loopbodyiter < self.loopbody_order.len() {
            let index = self.loopbody_order[self.loopbodyiter];
            loopbottom = self.loopbody[index].update(self.graph, data);
            if let Some(bottom) = loopbottom {
                let top = self.loopbody[index].get_head();
                looptop = Some(top);
                if bottom == top {
                    self.likelygoto.clear();
                    self.likelygoto.push(FloatingEdge::new(top, top));
                    self.likelyiter = 0;
                    self.likelylistfull = true;
                    return Ok(true);
                }
                if !self.likelylistfull || self.likelyiter < self.likelygoto.len() {
                    break;
                }
            }
            self.loopbodyiter += 1;
            self.likelylistfull = false;
            loopbottom = None;
        }
        if self.likelylistfull && self.likelyiter < self.likelygoto.len() {
            return Ok(true);
        }

        self.likelygoto.clear();
        let mut tracer = TraceDag::new();
        match loopbottom {
            Some(bottom) => {
                tracer.add_root(looptop.expect("loop without head"));
                tracer.set_finish_block(bottom);
                let index = self.loopbody_order[self.loopbodyiter];
                self.loopbody[index].set_exit_marks(self.graph, data);
            }
            None => {
                let mut position = 0;
                while position < data.block(self.graph).get_size() {
                    let bl = data.block(self.graph).get_block(position);
                    if data.block(bl).size_in() == 0 {
                        tracer.add_root(bl);
                    }
                    position += 1;
                }
            }
        }
        tracer.initialize();
        tracer.push_branches(&mut self.likelygoto, data);
        self.likelylistfull = true;
        if loopbottom.is_some() {
            let index = self.loopbody_order[self.loopbodyiter];
            self.loopbody[index].emit_likely_edges(&mut self.likelygoto, self.graph, data);
            self.loopbody[index].clear_exit_marks(self.graph, data);
        } else if self.likelygoto.is_empty() {
            self.finaltrace = true;
            return Ok(false);
        }
        self.likelyiter = 0;
        Ok(true)
    }

    pub fn select_goto(&mut self, data: &mut Funcdata) -> Result<Option<BlockId>> {
        while self.update_loop_body(data)? {
            while self.likelyiter < self.likelygoto.len() {
                let mut outedge = 0;
                let position = self.likelyiter;
                let startbl = self.likelygoto[position].get_current_edge(&mut outedge, self.graph, data);
                self.likelyiter += 1;
                if let Some(startbl) = startbl {
                    data.block_set_goto_branch(startbl, outedge)?;
                    return Ok(Some(startbl));
                }
            }
        }
        if !self.clip_extra_roots(data)? {
            return Err(Error::Lowlevel(
                "Could not finish collapsing block structure".to_string(),
            ));
        }
        Ok(None)
    }

    pub fn rule_block_goto(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let sizeout = data.block(bl).size_out();
        for slot in 0..sizeout {
            if data.block(bl).is_goto_out(slot) {
                if data.block(bl).is_switch_out() {
                    data.block_new_block_multi_goto(self.graph, bl, slot)?;
                    return Ok(true);
                }
                if sizeout == 2 {
                    if !data.block(bl).is_goto_out(1) {
                        self.negate(bl, data);
                    }
                    data.block_new_block_if_goto(self.graph, bl)?;
                    return Ok(true);
                }
                if sizeout == 1 {
                    data.block_new_block_goto(self.graph, bl)?;
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    pub fn rule_block_cat(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 1 {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        if block.size_in() == 1 && data.block(block.get_in(0)).size_out() == 1 {
            return Ok(false);
        }
        let mut outblock = block.get_out(0);
        if outblock == bl {
            return Ok(false);
        }
        if data.block(outblock).size_in() != 1 {
            return Ok(false);
        }
        if !block.is_decision_out(0) {
            return Ok(false);
        }
        if data.block(outblock).is_switch_out() {
            return Ok(false);
        }
        let mut nodes = vec![bl, outblock];
        while data.block(outblock).size_out() == 1 {
            let outbl2 = data.block(outblock).get_out(0);
            if outbl2 == bl {
                break;
            }
            if data.block(outbl2).size_in() != 1 {
                break;
            }
            if !data.block(outblock).is_decision_out(0) {
                break;
            }
            if data.block(outbl2).is_switch_out() {
                break;
            }
            outblock = outbl2;
            nodes.push(outblock);
        }
        data.block_new_block_list(self.graph, &nodes)?;
        Ok(true)
    }

    pub fn rule_block_or(&mut self, bl: BlockId, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 2 {
            return Ok(false);
        }
        if block.is_goto_out(0) || block.is_goto_out(1) {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        for slot in 0..2 {
            let block = data.block(bl);
            let orblock = block.get_out(slot);
            if orblock == bl {
                continue;
            }
            let orb = data.block(orblock);
            if orb.size_in() != 1 {
                continue;
            }
            if orb.size_out() != 2 {
                continue;
            }
            if orb.is_interior_goto_target() {
                continue;
            }
            if orb.is_switch_out() {
                continue;
            }
            if block.is_back_edge_out(slot) {
                continue;
            }
            if data.block_is_complex(orblock, glb) {
                continue;
            }
            let clauseblock = block.get_out(1 - slot);
            if clauseblock == bl {
                continue;
            }
            if clauseblock == orblock {
                continue;
            }
            let mut matched = 0;
            while matched < 2 {
                if clauseblock != orb.get_out(matched) {
                    matched += 1;
                    continue;
                }
                break;
            }
            if matched == 2 {
                continue;
            }
            if orb.get_out(1 - matched) == bl {
                continue;
            }
            if slot == 1 {
                self.negate(bl, data);
            }
            if matched == 0 {
                self.negate(orblock, data);
            }
            data.block_new_block_condition(self.graph, bl, orblock)?;
            return Ok(true);
        }
        Ok(false)
    }

    pub fn rule_block_proper_if(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 2 {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        if block.get_out(0) == bl || block.get_out(1) == bl {
            return Ok(false);
        }
        if block.is_goto_out(0) || block.is_goto_out(1) {
            return Ok(false);
        }
        for slot in 0..2 {
            let block = data.block(bl);
            let clauseblock = block.get_out(slot);
            let clause = data.block(clauseblock);
            if clause.size_in() != 1 {
                continue;
            }
            if clause.size_out() != 1 {
                continue;
            }
            if clause.is_switch_out() {
                continue;
            }
            if !block.is_decision_out(slot) {
                continue;
            }
            if clause.is_goto_out(0) {
                continue;
            }
            let outblock = clause.get_out(0);
            if outblock != block.get_out(1 - slot) {
                continue;
            }
            if slot == 0 {
                self.negate(bl, data);
            }
            data.block_new_block_if(self.graph, bl, clauseblock)?;
            return Ok(true);
        }
        Ok(false)
    }

    pub fn rule_block_if_else(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 2 {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        if !block.is_decision_out(0) || !block.is_decision_out(1) {
            return Ok(false);
        }
        let tc = block.get_true_out();
        let fc = block.get_false_out();
        let tcb = data.block(tc);
        let fcb = data.block(fc);
        if tcb.size_in() != 1 || fcb.size_in() != 1 {
            return Ok(false);
        }
        if tcb.size_out() != 1 || fcb.size_out() != 1 {
            return Ok(false);
        }
        let outblock = tcb.get_out(0);
        if outblock == bl {
            return Ok(false);
        }
        if outblock != fcb.get_out(0) {
            return Ok(false);
        }
        if tcb.is_switch_out() || fcb.is_switch_out() {
            return Ok(false);
        }
        if tcb.is_goto_out(0) || fcb.is_goto_out(0) {
            return Ok(false);
        }
        data.block_new_block_if_else(self.graph, bl, tc, fc)?;
        Ok(true)
    }

    pub fn rule_block_if_no_exit(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 2 {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        if block.get_out(0) == bl || block.get_out(1) == bl {
            return Ok(false);
        }
        if block.is_goto_out(0) || block.is_goto_out(1) {
            return Ok(false);
        }
        for slot in 0..2 {
            let block = data.block(bl);
            let clauseblock = block.get_out(slot);
            let clause = data.block(clauseblock);
            if clause.size_in() != 1 {
                continue;
            }
            if clause.size_out() != 0 {
                continue;
            }
            if clause.is_switch_out() {
                continue;
            }
            if !block.is_decision_out(slot) {
                continue;
            }
            if slot == 0 {
                let otherblock = block.get_out(1);
                let other = data.block(otherblock);
                if other.size_in() == 1 && other.size_out() == 0 && !other.is_switch_out() && block.is_decision_out(1) {
                    self.negate(bl, data);
                    data.block_new_block_if_no_exit(self.graph, bl, clauseblock, otherblock)?;
                    return Ok(true);
                }
            }
            if slot == 0 {
                self.negate(bl, data);
            }
            data.block_new_block_if(self.graph, bl, clauseblock)?;
            return Ok(true);
        }
        Ok(false)
    }

    pub fn rule_block_while_do(&mut self, bl: BlockId, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 2 {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        if block.get_out(0) == bl || block.get_out(1) == bl {
            return Ok(false);
        }
        if block.is_interior_goto_target() {
            return Ok(false);
        }
        if block.is_goto_out(0) || block.is_goto_out(1) {
            return Ok(false);
        }
        for slot in 0..2 {
            let clauseblock = data.block(bl).get_out(slot);
            let clause = data.block(clauseblock);
            if clause.size_in() != 1 {
                continue;
            }
            if clause.size_out() != 1 {
                continue;
            }
            if clause.is_switch_out() {
                continue;
            }
            if clause.get_out(0) != bl {
                continue;
            }
            let overflow = data.block_is_complex(bl, glb);
            if (slot == 0) != overflow {
                self.negate(bl, data);
            }
            let newbl = data.block_new_block_while_do(self.graph, bl, clauseblock)?;
            if overflow {
                data.block_mut(newbl).set_overflow_syntax();
            }
            return Ok(true);
        }
        Ok(false)
    }

    pub fn rule_block_do_while(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 2 {
            return Ok(false);
        }
        if block.is_switch_out() {
            return Ok(false);
        }
        if block.is_goto_out(0) || block.is_goto_out(1) {
            return Ok(false);
        }
        for slot in 0..2 {
            if data.block(bl).get_out(slot) != bl {
                continue;
            }
            if slot == 0 {
                self.negate(bl, data);
            }
            data.block_new_block_do_while(self.graph, bl)?;
            return Ok(true);
        }
        Ok(false)
    }

    pub fn rule_block_inf_loop(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        let block = data.block(bl);
        if block.size_out() != 1 {
            return Ok(false);
        }
        if block.is_goto_out(0) {
            return Ok(false);
        }
        if block.get_out(0) != bl {
            return Ok(false);
        }
        data.block_new_block_inf_loop(self.graph, bl)?;
        Ok(true)
    }

    pub fn rule_block_switch(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        if !data.block(bl).is_switch_out() {
            return Ok(false);
        }
        let mut exitblock: Option<BlockId> = None;
        let sizeout = data.block(bl).size_out();
        for slot in 0..sizeout {
            let curbl = data.block(bl).get_out(slot);
            if curbl == bl {
                exitblock = Some(curbl);
                break;
            }
            if data.block(curbl).size_out() > 1 {
                exitblock = Some(curbl);
                break;
            }
            if data.block(curbl).size_in() > 1 {
                exitblock = Some(curbl);
                break;
            }
        }
        match exitblock {
            None => {
                for slot in 0..sizeout {
                    let curbl = data.block(bl).get_out(slot);
                    let cur = data.block(curbl);
                    if cur.is_goto_in(0) {
                        return Ok(false);
                    }
                    if cur.is_switch_out() {
                        return Ok(false);
                    }
                    if cur.size_out() == 1 {
                        if cur.is_goto_out(0) {
                            return Ok(false);
                        }
                        match exitblock {
                            Some(exit) => {
                                if exit != cur.get_out(0) {
                                    return Ok(false);
                                }
                            }
                            None => exitblock = Some(cur.get_out(0)),
                        }
                    }
                }
            }
            Some(exit) => {
                let exitb = data.block(exit);
                for slot in 0..exitb.size_in() {
                    if exitb.is_goto_in(slot) {
                        return Ok(false);
                    }
                }
                for slot in 0..exitb.size_out() {
                    if exitb.is_goto_out(slot) {
                        return Ok(false);
                    }
                }
                for slot in 0..sizeout {
                    let curbl = data.block(bl).get_out(slot);
                    if curbl == exit {
                        continue;
                    }
                    let cur = data.block(curbl);
                    if cur.size_in() > 1 {
                        return Ok(false);
                    }
                    if cur.is_goto_in(0) {
                        return Ok(false);
                    }
                    if cur.size_out() > 1 {
                        return Ok(false);
                    }
                    if cur.size_out() == 1 {
                        if cur.is_goto_out(0) {
                            return Ok(false);
                        }
                        if cur.get_out(0) != exit {
                            return Ok(false);
                        }
                    }
                    if cur.is_switch_out() {
                        return Ok(false);
                    }
                }
            }
        }

        if !self.check_switch_skips(bl, exitblock, data)? {
            return Ok(true);
        }

        let mut cases = vec![bl];
        for slot in 0..sizeout {
            let curbl = data.block(bl).get_out(slot);
            if Some(curbl) == exitblock {
                continue;
            }
            cases.push(curbl);
        }
        data.block_new_block_switch(self.graph, &cases, exitblock.is_some())?;
        Ok(true)
    }

    pub fn rule_case_fallthru(&mut self, bl: BlockId, data: &mut Funcdata) -> Result<bool> {
        if !data.block(bl).is_switch_out() {
            return Ok(false);
        }
        let sizeout = data.block(bl).size_out();
        let mut nonfallthru = 0;
        let mut fallthru = Vec::new();
        for slot in 0..sizeout {
            let curbl = data.block(bl).get_out(slot);
            if curbl == bl {
                return Ok(false);
            }
            let cur = data.block(curbl);
            if cur.size_in() > 2 || cur.size_out() > 1 {
                nonfallthru += 1;
            } else if cur.size_out() == 1 {
                let target = data.block(cur.get_out(0));
                if target.size_in() == 2 && target.size_out() <= 1 {
                    let inslot = cur.get_out_rev_index(0);
                    if target.get_in(1 - inslot) == bl {
                        fallthru.push(curbl);
                    }
                }
            }
            if nonfallthru > 1 {
                return Ok(false);
            }
        }
        if fallthru.is_empty() {
            return Ok(false);
        }
        for curbl in fallthru {
            data.block_set_goto_branch(curbl, 0)?;
        }
        Ok(true)
    }

    pub fn collapse_internal(
        &mut self,
        targetbl: Option<BlockId>,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<i32> {
        let mut targetbl = targetbl;
        let mut isolated_count;
        loop {
            loop {
                let mut change = false;
                let mut index = 0;
                isolated_count = 0;
                while index < data.block(self.graph).get_size() {
                    let bl = match targetbl {
                        None => {
                            let bl = data.block(self.graph).get_block(index);
                            index += 1;
                            bl
                        }
                        Some(target) => {
                            change = true;
                            targetbl = None;
                            index = data.block(self.graph).get_size();
                            target
                        }
                    };
                    if data.block(bl).size_in() == 0 && data.block(bl).size_out() == 0 {
                        isolated_count += 1;
                        continue;
                    }
                    if self.rule_block_goto(bl, data)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_cat(bl, data)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_proper_if(bl, data)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_if_else(bl, data)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_while_do(bl, data, glb)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_do_while(bl, data)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_inf_loop(bl, data)? {
                        change = true;
                        continue;
                    }
                    if self.rule_block_switch(bl, data)? {
                        change = true;
                        continue;
                    }
                }
                if !change {
                    break;
                }
            }
            let mut fullchange = false;
            let mut index = 0;
            while index < data.block(self.graph).get_size() {
                let bl = data.block(self.graph).get_block(index);
                if self.rule_block_if_no_exit(bl, data)? {
                    fullchange = true;
                    break;
                }
                if self.rule_case_fallthru(bl, data)? {
                    fullchange = true;
                    break;
                }
                index += 1;
            }
            if !fullchange {
                break;
            }
        }
        Ok(isolated_count)
    }

    pub fn collapse_conditions(&mut self, data: &mut Funcdata, glb: &Architecture) -> Result<()> {
        loop {
            let mut change = false;
            let mut index = 0;
            while index < data.block(self.graph).get_size() {
                let bl = data.block(self.graph).get_block(index);
                if self.rule_block_or(bl, data, glb)? {
                    change = true;
                }
                index += 1;
            }
            if !change {
                break;
            }
        }
        Ok(())
    }

    pub fn get_change_count(&self) -> i32 {
        self.dataflow_changecount
    }

    pub fn collapse_all(&mut self, data: &mut Funcdata, glb: &Architecture) -> Result<()> {
        self.finaltrace = false;
        data.block_clear_visit_count(self.graph);
        self.order_loop_bodies(data)?;
        self.collapse_conditions(data, glb)?;
        let mut isolated_count = self.collapse_internal(None, data, glb)?;
        while isolated_count < data.block(self.graph).get_size() {
            let targetbl = self.select_goto(data)?;
            isolated_count = self.collapse_internal(targetbl, data, glb)?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MergePair {
    pub side1_create_index: u32,
    pub side2_create_index: u32,
    pub side1: VarnodeId,
    pub side2: VarnodeId,
}

impl MergePair {
    pub fn new(s1: VarnodeId, s1_create_index: u32, s2: VarnodeId, s2_create_index: u32) -> MergePair {
        MergePair {
            side1_create_index: s1_create_index,
            side2_create_index: s2_create_index,
            side1: s1,
            side2: s2,
        }
    }

    pub fn from_varnodes(s1: VarnodeId, s2: VarnodeId, data: &Funcdata) -> MergePair {
        MergePair::new(s1, data.vn(s1).get_create_index(), s2, data.vn(s2).get_create_index())
    }
}

#[derive(Clone, Debug, Default)]
pub struct ConditionalJoin {
    pub block1: Option<BlockId>,
    pub block2: Option<BlockId>,
    pub exita: Option<BlockId>,
    pub exitb: Option<BlockId>,
    pub a_in1: i32,
    pub a_in2: i32,
    pub b_in1: i32,
    pub b_in2: i32,
    pub cbranch1: Option<OpId>,
    pub cbranch2: Option<OpId>,
    pub joinblock: Option<BlockId>,
    pub mergeneed: BTreeMap<MergePair, Option<VarnodeId>>,
}

impl ConditionalJoin {
    pub fn new() -> ConditionalJoin {
        ConditionalJoin::default()
    }

    pub fn find_dups(&mut self, data: &mut Funcdata) -> bool {
        let block1 = self.block1.expect("conditional join without block1");
        let block2 = self.block2.expect("conditional join without block2");
        let cbranch1 = data.block_last_op(block1).expect("conditional join block without ops");
        self.cbranch1 = Some(cbranch1);
        if data.op(cbranch1).code() != OpCode::Cbranch {
            return false;
        }
        let cbranch2 = data.block_last_op(block2).expect("conditional join block without ops");
        self.cbranch2 = Some(cbranch2);
        if data.op(cbranch2).code() != OpCode::Cbranch {
            return false;
        }
        if data.op(cbranch1).is_boolean_flip() {
            return false;
        }
        if data.op(cbranch2).is_boolean_flip() {
            return false;
        }
        let vn1 = data.op(cbranch1).get_in(1);
        let vn2 = data.op(cbranch2).get_in(1);
        if vn1 == vn2 {
            return true;
        }
        if !data.vn(vn1).is_written() || !data.vn(vn2).is_written() {
            return false;
        }
        if data.vn(vn1).is_spacebase() || data.vn(vn2).is_spacebase() {
            return false;
        }
        let mut buf1: [Option<VarnodeId>; 2] = [None; 2];
        let mut buf2: [Option<VarnodeId>; 2] = [None; 2];
        let res = functional_equality_level(vn1, vn2, &mut buf1, &mut buf2, data);
        if res < 0 {
            return false;
        }
        if res > 1 {
            return false;
        }
        let op1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        if data.op(op1).code() == OpCode::Subpiece {
            return false;
        }
        if data.op(op1).code() == OpCode::Copy {
            return false;
        }
        self.mergeneed.insert(MergePair::from_varnodes(vn1, vn2, data), None);
        true
    }

    pub fn check_exit_block(&mut self, exit: BlockId, in1: i32, in2: i32, data: &mut Funcdata) {
        let ops = data.block(exit).get_op_list().to_vec(&data.obank.ops);
        for op in ops {
            let code = data.op(op).code();
            if code == OpCode::Multiequal {
                let vn1 = data.op(op).get_in(in1);
                let vn2 = data.op(op).get_in(in2);
                if vn1 != vn2 {
                    self.mergeneed.insert(MergePair::from_varnodes(vn1, vn2, data), None);
                }
            } else if code != OpCode::Copy {
                break;
            }
        }
    }

    pub fn cut_down_multiequals(
        &mut self,
        exit: BlockId,
        in1: i32,
        in2: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<()> {
        let (lo, hi) = if in1 > in2 { (in2, in1) } else { (in1, in2) };
        let mut iter = data.block(exit).get_op_list().front();
        while let Some(op) = iter {
            iter = data.block(exit).get_op_list().next(&data.obank.ops, op);
            let code = data.op(op).code();
            if code == OpCode::Multiequal {
                let vn1 = data.op(op).get_in(in1);
                let vn2 = data.op(op).get_in(in2);
                if vn1 == vn2 {
                    data.op_remove_input(op, hi);
                } else {
                    let key = MergePair::from_varnodes(vn1, vn2, data);
                    let subvn = *self.mergeneed.entry(key).or_insert(None);
                    data.op_remove_input(op, hi);
                    data.op_set_input(op, subvn.expect("merge pair without joined varnode"), lo)?;
                }
                if data.op(op).num_input() == 1 {
                    data.op_uninsert(op);
                    data.op_set_opcode(op, OpCode::Copy, glb);
                    data.op_insert_begin(op, exit);
                }
            } else if code != OpCode::Copy {
                break;
            }
        }
        Ok(())
    }

    pub fn setup_multiequals(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let joinblock = self.joinblock.expect("conditional join without join block");
        let cbranch1 = self.cbranch1.expect("conditional join without cbranch");
        let keys: Vec<MergePair> = self.mergeneed.keys().copied().collect();
        for key in keys {
            if self.mergeneed[&key].is_some() {
                continue;
            }
            let vn1 = key.side1;
            let vn2 = key.side2;
            let addr = data.op(cbranch1).get_addr().clone();
            let multi = data.new_op(2, &addr);
            data.op_set_opcode(multi, OpCode::Multiequal, glb);
            let size = data.vn(vn1).get_size();
            let outvn = data.new_unique_out(size, multi, glb)?;
            data.op_set_input(multi, vn1, 0)?;
            data.op_set_input(multi, vn2, 1)?;
            self.mergeneed.insert(key, Some(outvn));
            data.op_insert_end(multi, joinblock);
        }
        Ok(())
    }

    pub fn move_cbranch(&mut self, data: &mut Funcdata) -> Result<()> {
        let cbranch1 = self.cbranch1.expect("conditional join without cbranch");
        let cbranch2 = self.cbranch2.expect("conditional join without cbranch");
        let joinblock = self.joinblock.expect("conditional join without join block");
        let vn1 = data.op(cbranch1).get_in(1);
        let vn2 = data.op(cbranch2).get_in(1);
        data.op_uninsert(cbranch1);
        data.op_insert_end(cbranch1, joinblock);
        let vn = if vn1 != vn2 {
            let key = MergePair::from_varnodes(vn1, vn2, data);
            self.mergeneed
                .entry(key)
                .or_insert(None)
                .expect("merge pair without joined varnode")
        } else {
            vn1
        };
        data.op_set_input(cbranch1, vn, 1)?;
        data.op_destroy(cbranch2)
    }

    pub fn match_blocks(&mut self, b1: BlockId, b2: BlockId, data: &mut Funcdata) -> bool {
        self.block1 = Some(b1);
        self.block2 = Some(b2);
        if b2 == b1 {
            return false;
        }
        if data.block(b1).size_out() != 2 {
            return false;
        }
        if data.block(b2).size_out() != 2 {
            return false;
        }
        let exita = data.block(b1).get_out(0);
        let exitb = data.block(b1).get_out(1);
        self.exita = Some(exita);
        self.exitb = Some(exitb);
        if exita == exitb {
            return false;
        }
        if data.block(b2).get_out(0) != exita {
            return false;
        }
        if data.block(b2).get_out(1) != exitb {
            return false;
        }
        self.a_in2 = data.block(b2).get_out_rev_index(0);
        self.b_in2 = data.block(b2).get_out_rev_index(1);
        self.a_in1 = data.block(b1).get_out_rev_index(0);
        self.b_in1 = data.block(b1).get_out_rev_index(1);

        if !self.find_dups(data) {
            self.clear();
            return false;
        }
        self.check_exit_block(exita, self.a_in1, self.a_in2, data);
        self.check_exit_block(exitb, self.b_in1, self.b_in2, data);
        true
    }

    pub fn execute(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let block1 = self.block1.expect("conditional join without block1");
        let block2 = self.block2.expect("conditional join without block2");
        let exita = self.exita.expect("conditional join without exit");
        let exitb = self.exitb.expect("conditional join without exit");
        let addr = data
            .op(self.cbranch1.expect("conditional join without cbranch"))
            .get_addr()
            .clone();
        let joinblock = data.node_join_create_block(
            block1,
            block2,
            exita,
            exitb,
            self.a_in1 > self.a_in2,
            self.b_in1 > self.b_in2,
            &addr,
            glb,
        )?;
        self.joinblock = Some(joinblock);
        self.setup_multiequals(data, glb)?;
        self.move_cbranch(data)?;
        self.cut_down_multiequals(exita, self.a_in1, self.a_in2, data, glb)?;
        self.cut_down_multiequals(exitb, self.b_in1, self.b_in2, data, glb)?;
        Ok(())
    }

    pub fn clear(&mut self) {
        self.mergeneed.clear();
    }
}

pub struct ActionStructureTransform {
    pub base: ActionBase,
    pub allow_op_moves: bool,
}

impl ActionStructureTransform {
    pub fn new(group: &str, allow_moves: bool) -> ActionStructureTransform {
        ActionStructureTransform {
            base: ActionBase::new(0, "structuretransform", group),
            allow_op_moves: allow_moves,
        }
    }
}

impl Action for ActionStructureTransform {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionStructureTransform::new(
            self.get_group(),
            self.allow_op_moves,
        )))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let structure = data.sblocks;
        data.block_final_transform(structure, self.allow_op_moves, glb)?;
        Ok(0)
    }
}

pub struct ActionNormalizeBranches {
    pub base: ActionBase,
}

impl ActionNormalizeBranches {
    pub fn new(group: &str) -> ActionNormalizeBranches {
        ActionNormalizeBranches {
            base: ActionBase::new(0, "normalizebranches", group),
        }
    }
}

impl Action for ActionNormalizeBranches {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionNormalizeBranches::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let graph = data.bblocks;
        let mut fliplist = Vec::new();
        let mut index = 0;
        while index < data.block(graph).get_size() {
            let bb = data.block(graph).get_block(index);
            index += 1;
            if data.block(bb).size_out() != 2 {
                continue;
            }
            let cbranch = match data.block_last_op(bb) {
                None => continue,
                Some(cbranch) => cbranch,
            };
            if data.op(cbranch).code() != OpCode::Cbranch {
                continue;
            }
            fliplist.clear();
            if data.op_flip_in_place_test(cbranch, &mut fliplist, true) != 0 {
                continue;
            }
            data.op_flip_in_place_execute(&fliplist, glb)?;
            data.block_flip_in_place_execute(bb);
            self.base.count += 1;
        }
        data.clear_dead_ops();
        Ok(0)
    }
}

pub struct ActionPreferComplement {
    pub base: ActionBase,
    pub allow_op_mods: bool,
}

impl ActionPreferComplement {
    pub fn new(group: &str, allow_mods: bool) -> ActionPreferComplement {
        ActionPreferComplement {
            base: ActionBase::new(0, "prefercomplement", group),
            allow_op_mods: allow_mods,
        }
    }
}

impl Action for ActionPreferComplement {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionPreferComplement::new(
            self.get_group(),
            self.allow_op_mods,
        )))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let graph = data.sblocks;
        if data.block(graph).get_size() == 0 {
            return Ok(0);
        }
        if data.block(graph).has_final_transform() {
            return Ok(0);
        }
        let mut vec = vec![graph];
        let mut pos = 0;
        while pos < vec.len() {
            let curbl = vec[pos];
            pos += 1;
            let children = data.block(curbl).get_list().to_vec();
            for childbl in children {
                let bt = data.block(childbl).get_type();
                if bt == BlockType::Copy || bt == BlockType::Basic {
                    continue;
                }
                vec.push(childbl);
            }
            if data.block_prefer_complement(curbl, self.allow_op_mods, glb)? {
                self.base.count += 1;
            }
        }
        data.clear_dead_ops();
        Ok(0)
    }
}

pub struct ActionBlockStructure {
    pub base: ActionBase,
}

impl ActionBlockStructure {
    pub fn new(group: &str) -> ActionBlockStructure {
        ActionBlockStructure {
            base: ActionBase::new(0, "blockstructure", group),
        }
    }
}

impl Action for ActionBlockStructure {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionBlockStructure::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let graph = data.sblocks;
        if data.block(graph).get_size() != 0 {
            return Ok(0);
        }
        data.install_switch_defaults();
        let basic = data.bblocks;
        data.block_build_copy(graph, basic);
        let mut collapse = CollapseStructure::new(graph);
        collapse.collapse_all(data, glb)?;
        self.base.count += collapse.get_change_count();
        Ok(0)
    }
}

pub struct ActionFinalStructure {
    pub base: ActionBase,
}

impl ActionFinalStructure {
    pub fn new(group: &str) -> ActionFinalStructure {
        ActionFinalStructure {
            base: ActionBase::new(0, "finalstructure", group),
        }
    }
}

impl Action for ActionFinalStructure {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionFinalStructure::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let graph = data.sblocks;
        data.block_order_blocks(graph);
        data.block_finalize_printing(graph, glb)?;
        data.block_scope_break(graph, -1, -1);
        data.block_mark_unstructured(graph);
        data.block_mark_label_bump_up(graph, false);
        Ok(0)
    }
}

pub struct ActionReturnSplit {
    pub base: ActionBase,
}

impl ActionReturnSplit {
    pub fn new(group: &str) -> ActionReturnSplit {
        ActionReturnSplit {
            base: ActionBase::new(0, "returnsplit", group),
        }
    }

    pub fn gather_return_gotos(parent: BlockId, vec: &mut Vec<BlockId>, data: &mut Funcdata) {
        for slot in 0..data.block(parent).size_in() {
            let inbl = data.block(parent).get_in(slot);
            let mut bl = data.block(inbl).get_copy_map();
            while let Some(cur) = bl {
                if !data.block(cur).is_mark() {
                    let mut ret: Option<BlockId> = None;
                    let bt = data.block(cur).get_type();
                    if bt == BlockType::Goto {
                        if data.block_goto_prints(cur) {
                            ret = Some(data.block(cur).get_goto_target());
                        }
                    } else if bt == BlockType::IfGoto {
                        ret = Some(data.block(cur).get_goto_target());
                    }
                    if let Some(mut target) = ret {
                        while data.block(target).get_type() != BlockType::Basic {
                            target = data
                                .block(target)
                                .sub_block(0)
                                .expect("goto target without basic block");
                        }
                        if target == parent {
                            data.block_mut(cur).set_mark();
                            vec.push(cur);
                        }
                    }
                }
                bl = data.block(cur).get_parent();
            }
        }
    }

    pub fn is_splittable(basic: BlockId, data: &Funcdata) -> bool {
        for op in data.block(basic).get_op_list().iter(&data.obank.ops) {
            let pcode = data.op(op);
            let opc = pcode.code();
            if opc == OpCode::Multiequal {
                continue;
            }
            if opc == OpCode::Copy || opc == OpCode::Return {
                for slot in 0..pcode.num_input() {
                    let vn = data.vn(pcode.get_in(slot));
                    if vn.is_constant() {
                        continue;
                    }
                    if vn.is_annotation() {
                        continue;
                    }
                    if vn.is_free() {
                        return false;
                    }
                }
                continue;
            }
            return false;
        }
        true
    }
}

impl Action for ActionReturnSplit {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionReturnSplit::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut splitedge: Vec<i32> = Vec::new();
        let mut retnode: Vec<BlockId> = Vec::new();

        if data.block(data.sblocks).get_size() == 0 {
            return Ok(0);
        }
        let returns = data.obank.returnlist.to_vec(&data.obank.ops);
        for op in returns {
            if data.op(op).is_dead() {
                continue;
            }
            let parent = data.op(op).get_parent().expect("RETURN without block");
            if data.block(parent).size_in() <= 1 {
                continue;
            }
            if !ActionReturnSplit::is_splittable(parent, data) {
                continue;
            }
            let mut gotoblocks = Vec::new();
            ActionReturnSplit::gather_return_gotos(parent, &mut gotoblocks, data);
            if gotoblocks.is_empty() {
                continue;
            }

            let mut splitcount = 0;
            for slot in (0..data.block(parent).size_in()).rev() {
                let inbl = data.block(parent).get_in(slot);
                let mut bl = data.block(inbl).get_copy_map();
                while let Some(cur) = bl {
                    if data.block(cur).is_mark() {
                        splitedge.push(slot);
                        retnode.push(parent);
                        bl = None;
                        splitcount += 1;
                    } else {
                        bl = data.block(cur).get_parent();
                    }
                }
            }

            for bl in gotoblocks.iter() {
                data.block_mut(*bl).clear_mark();
            }

            if data.block(parent).size_in() == splitcount {
                splitedge.pop();
                retnode.pop();
            }
        }

        for (edge, node) in splitedge.iter().zip(retnode.iter()) {
            data.node_split(*node, *edge, glb)?;
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionNodeJoin {
    pub base: ActionBase,
}

impl ActionNodeJoin {
    pub fn new(group: &str) -> ActionNodeJoin {
        ActionNodeJoin {
            base: ActionBase::new(0, "nodejoin", group),
        }
    }
}

impl Action for ActionNodeJoin {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionNodeJoin::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let graph = data.bblocks;
        if data.block(graph).get_size() == 0 {
            return Ok(0);
        }
        let mut condjoin = ConditionalJoin::new();
        let mut index = 0;
        while index < data.block(graph).get_size() {
            let bb = data.block(graph).get_block(index);
            index += 1;
            if data.block(bb).size_out() != 2 {
                continue;
            }
            let out1 = data.block(bb).get_out(0);
            let out2 = data.block(bb).get_out(1);
            let (leastout, inslot) = if data.block(out1).size_in() < data.block(out2).size_in() {
                (out1, data.block(bb).get_out_rev_index(0))
            } else {
                (out2, data.block(bb).get_out_rev_index(1))
            };
            if data.block(leastout).size_in() == 1 {
                continue;
            }
            let mut slot = 0;
            while slot < data.block(leastout).size_in() {
                if slot == inslot {
                    slot += 1;
                    continue;
                }
                let bb2 = data.block(leastout).get_in(slot);
                if condjoin.match_blocks(bb, bb2, data) {
                    self.base.count += 1;
                    condjoin.execute(data, glb)?;
                    condjoin.clear();
                    break;
                }
                slot += 1;
            }
        }
        Ok(0)
    }
}
