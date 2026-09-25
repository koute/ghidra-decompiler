use std::sync::Arc;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::callgraph::{CallGraph, CallGraphNode};
use ghidra_decompiler::space::{AddrSpace, SpaceRef};

fn ram() -> SpaceRef {
    Arc::new(AddrSpace::new_processor("ram", false, 4, 1, 1, 0, 1, 0))
}

fn addr(space: &SpaceRef, offset: u64) -> Address {
    Address::new(space.clone(), offset)
}

fn build(space: &SpaceRef, nodes: &[u64], edges: &[(u64, u64)]) -> CallGraph {
    let mut graph = CallGraph::new();
    for node in nodes {
        graph.add_node(&addr(space, *node), &format!("func_{node:x}"));
    }
    for (index, (from, to)) in edges.iter().enumerate() {
        graph.add_edge(
            &addr(space, *from),
            &addr(space, *to),
            &addr(space, 0x1000 + index as u64),
        );
    }
    graph
}

fn walk(graph: &mut CallGraph) -> Vec<u64> {
    let mut res = Vec::new();
    let mut node = graph.init_leaf_walk();
    while let Some(current) = node {
        res.push(current.get_offset());
        node = graph.next_leaf(&current);
    }
    res
}

#[test]
fn add_edge_orders_out_edges_and_complements() {
    let space = ram();
    let graph = build(&space, &[0x10, 0x20, 0x30], &[(0x10, 0x30), (0x10, 0x20), (0x10, 0x30)]);
    let nodea = graph.find_node(&addr(&space, 0x10)).expect("node a");
    assert_eq!(nodea.num_out_edge(), 2);
    assert_eq!(nodea.get_out_node(0).get_offset(), 0x20);
    assert_eq!(nodea.get_out_node(1).get_offset(), 0x30);
    assert_eq!(nodea.get_out_edge(0).complement, 0);
    assert_eq!(nodea.get_out_edge(1).complement, 0);
    assert_eq!(nodea.get_out_edge(1).get_call_site_addr().get_offset(), 0x1000);
    let nodeb = graph.find_node(&addr(&space, 0x20)).expect("node b");
    assert_eq!(nodeb.get_in_edge(0).complement, 0);
    let nodec = graph.find_node(&addr(&space, 0x30)).expect("node c");
    assert_eq!(nodec.num_in_edge(), 1);
    assert_eq!(nodec.get_in_edge(0).complement, 1);
}

#[test]
fn delete_in_edge_fixes_complements() {
    let space = ram();
    let mut graph = build(&space, &[0x10, 0x20, 0x30], &[(0x10, 0x20), (0x10, 0x30), (0x20, 0x30)]);
    graph.delete_in_edge(&addr(&space, 0x30), 0);
    let nodea = graph.find_node(&addr(&space, 0x10)).expect("node a");
    assert_eq!(nodea.num_out_edge(), 1);
    assert_eq!(nodea.get_out_node(0).get_offset(), 0x20);
    let nodec = graph.find_node(&addr(&space, 0x30)).expect("node c");
    assert_eq!(nodec.num_in_edge(), 1);
    assert_eq!(nodec.get_in_node(0).get_offset(), 0x20);
    assert_eq!(nodec.get_in_edge(0).complement, 0);
    let nodeb = graph.find_node(&addr(&space, 0x20)).expect("node b");
    assert_eq!(nodeb.get_out_edge(0).complement, 1);
}

#[test]
fn leaf_walk_of_diamond() {
    let space = ram();
    let mut graph = build(
        &space,
        &[0x10, 0x20, 0x30, 0x40],
        &[(0x10, 0x20), (0x10, 0x30), (0x20, 0x40), (0x30, 0x40)],
    );
    assert_eq!(walk(&mut graph), vec![0x40, 0x20, 0x30, 0x10]);
    let nodec = graph.find_node(&addr(&space, 0x30)).expect("node c");
    assert!(!nodec.get_out_edge(0).is_cycle());
}

#[test]
fn leaf_walk_snips_cycle() {
    let space = ram();
    let mut graph = build(&space, &[0x10, 0x20], &[(0x10, 0x20), (0x20, 0x10)]);
    assert_eq!(walk(&mut graph), vec![0x20, 0x10]);
    let nodea = graph.find_node(&addr(&space, 0x10)).expect("node a");
    assert!((nodea.flags & CallGraphNode::ONLYCYCLEIN) != 0);
    assert!(!nodea.is_mark());
    let nodeb = graph.find_node(&addr(&space, 0x20)).expect("node b");
    assert!(nodeb.get_out_edge(0).is_cycle());
}

#[test]
fn leaf_walk_multiple_seeds() {
    let space = ram();
    let mut graph = build(&space, &[0x10, 0x20, 0x30], &[(0x20, 0x30)]);
    assert_eq!(walk(&mut graph), vec![0x10, 0x30, 0x20]);
}
