use std::collections::BTreeMap;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::block::ELEM_EDGE;
use crate::database::{Database, ScopeId, SymbolId, SymbolKind};
use crate::error::{Error, Result};
use crate::fspec::ProtoModel;
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_NAME, Decoder, ElementId, Encoder};

pub const ELEM_CALLGRAPH: ElementId = ElementId::new("callgraph", 226);
pub const ELEM_NODE: ElementId = ElementId::new("node", 227);

#[derive(Clone, Debug, Default)]
pub struct CallGraphEdge {
    pub from: Address,
    pub to: Address,
    pub callsiteaddr: Address,
    pub complement: i32,
    pub flags: u32,
}

impl CallGraphEdge {
    pub const CYCLE: u32 = 1;
    pub const DONTFOLLOW: u32 = 2;

    pub fn is_cycle(&self) -> bool {
        (self.flags & 1) != 0
    }

    pub fn get_call_site_addr(&self) -> &Address {
        &self.callsiteaddr
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_EDGE);
        self.from.encode(encoder)?;
        self.to.encode(encoder)?;
        self.callsiteaddr.encode(encoder)?;
        encoder.close_element(ELEM_EDGE);
        Ok(())
    }

    pub fn decode(decoder: &mut dyn Decoder, graph: &mut CallGraph) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_EDGE)?;
        let fromaddr = Address::decode(decoder)?;
        let toaddr = Address::decode(decoder)?;
        let siteaddr = Address::decode(decoder)?;
        decoder.close_element(elem_id)?;
        if graph.find_node(&fromaddr).is_none() {
            return Err(Error::Lowlevel("Could not find from node".to_string()));
        }
        if graph.find_node(&toaddr).is_none() {
            return Err(Error::Lowlevel("Could not find to node".to_string()));
        }
        graph.add_edge(&fromaddr, &toaddr, &siteaddr);
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct CallGraphNode {
    pub entryaddr: Address,
    pub name: String,
    pub fd: Option<SymbolId>,
    pub inedge: Vec<CallGraphEdge>,
    pub outedge: Vec<CallGraphEdge>,
    pub parentedge: i32,
    pub flags: u32,
}

impl CallGraphNode {
    pub const MARK: u32 = 1;
    pub const ONLYCYCLEIN: u32 = 2;
    pub const CURRENTCYCLE: u32 = 4;
    pub const ENTRYNODE: u32 = 8;

    pub fn new() -> CallGraphNode {
        CallGraphNode {
            parentedge: -1,
            ..CallGraphNode::default()
        }
    }

    pub fn clear_mark(&mut self) {
        self.flags &= !CallGraphNode::MARK;
    }

    pub fn is_mark(&self) -> bool {
        (self.flags & CallGraphNode::MARK) != 0
    }

    pub fn get_addr(&self) -> &Address {
        &self.entryaddr
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_funcdata(&self) -> Option<SymbolId> {
        self.fd
    }

    pub fn num_in_edge(&self) -> i32 {
        self.inedge.len() as i32
    }

    pub fn get_in_edge(&self, index: i32) -> &CallGraphEdge {
        &self.inedge[index as usize]
    }

    pub fn get_in_node(&self, index: i32) -> &Address {
        &self.inedge[index as usize].from
    }

    pub fn num_out_edge(&self) -> i32 {
        self.outedge.len() as i32
    }

    pub fn get_out_edge(&self, index: i32) -> &CallGraphEdge {
        &self.outedge[index as usize]
    }

    pub fn get_out_node(&self, index: i32) -> &Address {
        &self.outedge[index as usize].to
    }

    pub fn set_funcdata(&mut self, fd: &Funcdata) -> Result<()> {
        let symbol = fd.get_symbol();
        if self.fd.is_some() && self.fd != symbol {
            return Err(Error::Lowlevel(
                "Multiple functions at one address in callgraph".to_string(),
            ));
        }
        if *fd.get_address() != self.entryaddr {
            return Err(Error::Lowlevel(
                "Setting function data at wrong address in callgraph".to_string(),
            ));
        }
        self.fd = symbol;
        Ok(())
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_NODE);
        if !self.name.is_empty() {
            encoder.write_string(ATTRIB_NAME, &self.name);
        }
        self.entryaddr.encode(encoder)?;
        encoder.close_element(ELEM_NODE);
        Ok(())
    }

    pub fn decode(decoder: &mut dyn Decoder, graph: &mut CallGraph) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_NODE)?;
        let mut name = String::new();
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_NAME {
                name = decoder.read_string()?;
            }
        }
        let addr = Address::decode(decoder)?;
        decoder.close_element(elem_id)?;
        graph.add_node(&addr, &name);
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct CallGraph {
    pub graph: BTreeMap<Address, CallGraphNode>,
    pub seeds: Vec<Address>,
}

impl CallGraph {
    pub fn new() -> CallGraph {
        CallGraph::default()
    }

    fn node(&self, addr: &Address) -> &CallGraphNode {
        self.graph.get(addr).expect("callgraph node exists")
    }

    fn node_mut(&mut self, addr: &Address) -> &mut CallGraphNode {
        self.graph.get_mut(addr).expect("callgraph node exists")
    }

    fn find_no_entry(&mut self) -> bool {
        let mut lownode: Option<Address> = None;
        let mut allcovered = true;
        let mut newseeds = false;
        let keys: Vec<Address> = self.graph.keys().cloned().collect();
        for key in keys {
            let node = self.node(&key);
            if node.is_mark() {
                continue;
            }
            if node.inedge.is_empty() || (node.flags & CallGraphNode::ONLYCYCLEIN) != 0 {
                self.seeds.push(key.clone());
                self.node_mut(&key).flags |= CallGraphNode::MARK | CallGraphNode::ENTRYNODE;
                newseeds = true;
            } else {
                allcovered = false;
                match &lownode {
                    None => lownode = Some(key.clone()),
                    Some(low) => {
                        if node.num_in_edge() < self.node(low).num_in_edge() {
                            lownode = Some(key.clone());
                        }
                    }
                }
            }
        }
        if !newseeds && !allcovered {
            let low = lownode.expect("uncovered node exists");
            self.seeds.push(low.clone());
            self.node_mut(&low).flags |= CallGraphNode::MARK | CallGraphNode::ENTRYNODE;
        }
        allcovered
    }

    fn snip_cycles(&mut self, node: &Address) {
        let mut stack: Vec<(Address, usize)> = Vec::new();
        self.node_mut(node).flags |= CallGraphNode::CURRENTCYCLE;
        stack.push((node.clone(), 0));
        while let Some((cur, slot)) = stack.last().cloned() {
            if slot >= self.node(&cur).outedge.len() {
                self.node_mut(&cur).flags &= !CallGraphNode::CURRENTCYCLE;
                stack.pop();
            } else {
                stack.last_mut().expect("stack is not empty").1 += 1;
                let edge = self.node(&cur).outedge[slot].clone();
                if (edge.flags & CallGraphEdge::CYCLE) != 0 {
                    continue;
                }
                let next = edge.to.clone();
                let nextflags = self.node(&next).flags;
                if (nextflags & CallGraphNode::CURRENTCYCLE) != 0 {
                    self.snip_edge(&cur, slot);
                    continue;
                } else if (nextflags & CallGraphNode::MARK) != 0 {
                    self.node_mut(&cur).outedge[slot].flags |= CallGraphEdge::DONTFOLLOW;
                    continue;
                }
                let nextnode = self.node_mut(&next);
                nextnode.parentedge = edge.complement;
                nextnode.flags |= CallGraphNode::CURRENTCYCLE | CallGraphNode::MARK;
                stack.push((next, 0));
            }
        }
    }

    fn snip_edge(&mut self, node: &Address, index: usize) {
        let edge = {
            let current = self.node_mut(node);
            current.outedge[index].flags |= CallGraphEdge::CYCLE | CallGraphEdge::DONTFOLLOW;
            current.outedge[index].clone()
        };
        let toi = edge.complement as usize;
        let to = self.node_mut(&edge.to);
        to.inedge[toi].flags |= CallGraphEdge::CYCLE;
        let onlycycle = to
            .inedge
            .iter()
            .all(|inedge| (inedge.flags & CallGraphEdge::CYCLE) != 0);
        if onlycycle {
            to.flags |= CallGraphNode::ONLYCYCLEIN;
        }
    }

    fn clear_marks(&mut self) {
        for node in self.graph.values_mut() {
            node.clear_mark();
        }
    }

    fn insert_blank_edge(&mut self, node: &Address, slot: usize) {
        let current = self.node_mut(node);
        current.outedge.push(CallGraphEdge::default());
        let mut updates: Vec<(Address, usize)> = Vec::new();
        if current.outedge.len() > 1 {
            let mut index = current.outedge.len() as i32 - 2;
            while index >= slot as i32 {
                let position = index as usize;
                current.outedge[position + 1] = current.outedge[position].clone();
                let edge = &current.outedge[position + 1];
                updates.push((edge.to.clone(), edge.complement as usize));
                index -= 1;
            }
        }
        for (nodeout, complement) in updates {
            self.node_mut(&nodeout).inedge[complement].complement += 1;
        }
    }

    pub fn add_node_fd(&mut self, fd: &Funcdata) -> Result<Address> {
        let addr = fd.get_address().clone();
        let symbol = fd.get_symbol();
        let node = self.graph.entry(addr.clone()).or_default();
        if node.fd.is_some() && node.fd != symbol {
            return Err(Error::Lowlevel(format!(
                "Functions with duplicate entry points: {} {}",
                fd.get_name(),
                node.name
            )));
        }
        node.entryaddr = addr.clone();
        node.name = fd.get_display_name().to_string();
        node.fd = symbol;
        Ok(addr)
    }

    pub fn add_node(&mut self, addr: &Address, nm: &str) -> Address {
        let node = self.graph.entry(addr.clone()).or_default();
        node.entryaddr = addr.clone();
        node.name = nm.to_string();
        addr.clone()
    }

    pub fn find_node(&self, addr: &Address) -> Option<&CallGraphNode> {
        self.graph.get(addr)
    }

    pub fn find_node_mut(&mut self, addr: &Address) -> Option<&mut CallGraphNode> {
        self.graph.get_mut(addr)
    }

    pub fn add_edge(&mut self, from: &Address, to: &Address, addr: &Address) {
        let mut slot = 0usize;
        {
            let fromnode = self.node(from);
            let toaddr = &self.node(to).entryaddr;
            while slot < fromnode.outedge.len() {
                let outnode = &fromnode.outedge[slot].to;
                if outnode == to {
                    return;
                }
                if *toaddr < self.node(outnode).entryaddr {
                    break;
                }
                slot += 1;
            }
        }
        self.insert_blank_edge(from, slot);
        let tonode = self.node_mut(to);
        let toi = tonode.inedge.len() as i32;
        tonode.inedge.push(CallGraphEdge {
            from: from.clone(),
            to: to.clone(),
            callsiteaddr: addr.clone(),
            complement: slot as i32,
            flags: 0,
        });
        self.node_mut(from).outedge[slot] = CallGraphEdge {
            from: from.clone(),
            to: to.clone(),
            callsiteaddr: addr.clone(),
            complement: toi,
            flags: 0,
        };
    }

    pub fn delete_in_edge(&mut self, node: &Address, index: i32) {
        let position = index as usize;
        let (fromi, from) = {
            let current = self.node(node);
            (
                current.inedge[position].complement,
                current.inedge[position].from.clone(),
            )
        };
        {
            let current = self.node_mut(node);
            let tosize = current.inedge.len();
            for slot in position + 1..tosize {
                current.inedge[slot - 1] = current.inedge[slot].clone();
                if current.inedge[slot - 1].complement >= fromi {
                    current.inedge[slot - 1].complement -= 1;
                }
            }
            current.inedge.pop();
        }
        let fromnode = self.node_mut(&from);
        let fromsize = fromnode.outedge.len();
        for slot in (fromi + 1) as usize..fromsize {
            fromnode.outedge[slot - 1] = fromnode.outedge[slot].clone();
            if fromnode.outedge[slot - 1].complement >= index {
                fromnode.outedge[slot - 1].complement -= 1;
            }
        }
        fromnode.outedge.pop();
    }

    fn pop_possible(&self, node: &Address, outslot: &mut i32) -> Option<Address> {
        let current = self.node(node);
        if (current.flags & CallGraphNode::ENTRYNODE) != 0 {
            *outslot = current.parentedge;
            return None;
        }
        let edge = &current.inedge[current.parentedge as usize];
        *outslot = edge.complement;
        Some(edge.from.clone())
    }

    fn push_possible(&self, node: Option<&Address>, outslot: i32) -> Option<Address> {
        let Some(node) = node else {
            if outslot < 0 || outslot as usize >= self.seeds.len() {
                return None;
            }
            return Some(self.seeds[outslot as usize].clone());
        };
        let current = self.node(node);
        let mut slot = outslot as usize;
        while slot < current.outedge.len() {
            if (current.outedge[slot].flags & CallGraphEdge::DONTFOLLOW) != 0 {
                slot += 1;
            } else {
                return Some(current.outedge[slot].to.clone());
            }
        }
        None
    }

    pub fn init_leaf_walk(&mut self) -> Option<Address> {
        self.cycle_structure();
        let mut node = self.seeds.first()?.clone();
        while let Some(pushnode) = self.push_possible(Some(&node), 0) {
            node = pushnode;
        }
        Some(node)
    }

    pub fn next_leaf(&mut self, node: &Address) -> Option<Address> {
        let mut outslot: i32 = 0;
        let mut current = self.pop_possible(node, &mut outslot);
        outslot += 1;
        loop {
            let Some(pushnode) = self.push_possible(current.as_ref(), outslot) else {
                break;
            };
            current = Some(pushnode);
            outslot = 0;
        }
        current
    }

    fn cycle_structure(&mut self) {
        if !self.seeds.is_empty() {
            return;
        }
        let mut walked = 0usize;
        loop {
            let allcovered = self.find_no_entry();
            while walked < self.seeds.len() {
                let rootnode = self.seeds[walked].clone();
                self.node_mut(&rootnode).parentedge = walked as i32;
                self.snip_cycles(&rootnode);
                walked += 1;
            }
            if allcovered {
                break;
            }
        }
        self.clear_marks();
    }

    fn iterate_scopes_recursive(&mut self, scope: ScopeId, glb: &mut Architecture) -> Result<()> {
        let symboltab = glb
            .symboltab
            .as_ref()
            .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))?;
        if !symboltab.scope(scope).is_global() {
            return Ok(());
        }
        self.iterate_functions_addr_order(scope, glb)?;
        let children: Vec<ScopeId> = glb
            .symboltab
            .as_ref()
            .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))?
            .scope(scope)
            .children()
            .values()
            .cloned()
            .collect();
        for child in children {
            self.iterate_scopes_recursive(child, glb)?;
        }
        Ok(())
    }

    fn iterate_functions_addr_order(&mut self, scope: ScopeId, glb: &mut Architecture) -> Result<()> {
        let mut functions: Vec<SymbolId> = Vec::new();
        {
            let symboltab = glb
                .symboltab
                .as_ref()
                .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))?;
            let scopedata = symboltab.scope(scope);
            let mut miter = symboltab.scope_begin(scope);
            let menditer = symboltab.scope_end(scope);
            while !miter.equals(&menditer, scopedata) {
                let entry = miter.get(scopedata);
                let sym = symboltab.entry(entry).get_symbol();
                miter.advance(scopedata);
                if matches!(symboltab.symbol(sym).kind, SymbolKind::Function { .. }) {
                    functions.push(sym);
                }
            }
        }
        for sym in functions {
            if let Some(fd) = Database::symbol_get_function(glb, sym)? {
                self.add_node_fd(fd)?;
            }
        }
        Ok(())
    }

    pub fn build_all_nodes(&mut self, glb: &mut Architecture) -> Result<()> {
        let global = glb
            .symboltab
            .as_ref()
            .and_then(|symboltab| symboltab.get_global_scope())
            .ok_or_else(|| Error::Lowlevel("missing global scope".to_string()))?;
        self.iterate_scopes_recursive(global, glb)
    }

    pub fn build_edges(&mut self, fd: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let fdaddr = fd.get_address().clone();
        if self.find_node(&fdaddr).is_none() {
            return Err(Error::Lowlevel("Function is missing from callgraph".to_string()));
        }
        if fd.get_func_proto().get_model_extra_pop(glb) == ProtoModel::EXTRAPOP_UNKNOWN {
            fd.fillin_extrapop(glb)?;
        }
        let numcalls = fd.num_calls();
        for index in 0..numcalls {
            let spec = fd.get_call_specs(index);
            let callspec = fd.call_spec(spec);
            let addr = callspec.get_entry_address().clone();
            let opaddr = fd.op(callspec.get_op()).get_addr().clone();
            if !addr.is_invalid() {
                if self.find_node(&addr).is_none() {
                    let mut name = String::new();
                    glb.name_function(&addr, &mut name);
                    self.add_node(&addr, &name);
                }
                self.add_edge(&fdaddr, &addr, &opaddr);
            }
        }
        Ok(())
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_CALLGRAPH);
        for node in self.graph.values() {
            node.encode(encoder)?;
        }
        for node in self.graph.values() {
            for edge in node.inedge.iter() {
                edge.encode(encoder)?;
            }
        }
        encoder.close_element(ELEM_CALLGRAPH);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CALLGRAPH)?;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_EDGE {
                CallGraphEdge::decode(decoder, self)?;
            } else {
                CallGraphNode::decode(decoder, self)?;
            }
        }
        decoder.close_element(elem_id)
    }
}
