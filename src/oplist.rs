use crate::arena::{Arena, ArenaId};
use crate::op::OpId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListLinks<Id> {
    pub prev: Option<Id>,
    pub next: Option<Id>,
}

impl<Id> Default for ListLinks<Id> {
    fn default() -> ListLinks<Id> {
        ListLinks { prev: None, next: None }
    }
}

pub trait LinkedNode<Id> {
    fn links(&self, slot: usize) -> &ListLinks<Id>;
    fn links_mut(&mut self, slot: usize) -> &mut ListLinks<Id>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IntrusiveList<Id> {
    head: Option<Id>,
    tail: Option<Id>,
    len: usize,
    slot: usize,
}

pub type OpList = IntrusiveList<OpId>;

impl<Id: ArenaId> IntrusiveList<Id> {
    pub fn new(slot: usize) -> IntrusiveList<Id> {
        IntrusiveList {
            head: None,
            tail: None,
            len: 0,
            slot,
        }
    }

    pub fn slot(&self) -> usize {
        self.slot
    }

    pub fn front(&self) -> Option<Id> {
        self.head
    }

    pub fn back(&self) -> Option<Id> {
        self.tail
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn next<T: LinkedNode<Id>>(&self, nodes: &Arena<Id, T>, id: Id) -> Option<Id> {
        nodes.get(id).links(self.slot).next
    }

    pub fn prev<T: LinkedNode<Id>>(&self, nodes: &Arena<Id, T>, id: Id) -> Option<Id> {
        nodes.get(id).links(self.slot).prev
    }

    pub fn push_back<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, id: Id) {
        self.insert(nodes, None, id);
    }

    pub fn push_front<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, id: Id) {
        let head = self.head;
        self.insert(nodes, head, id);
    }

    pub fn insert_before<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, pos: Id, id: Id) {
        self.insert(nodes, Some(pos), id);
    }

    pub fn insert_after<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, pos: Id, id: Id) {
        let following = nodes.get(pos).links(self.slot).next;
        self.insert(nodes, following, id);
    }

    pub fn insert<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, pos: Option<Id>, id: Id) {
        let slot = self.slot;
        let prev = match pos {
            Some(position) => nodes.get(position).links(slot).prev,
            None => self.tail,
        };
        {
            let links = nodes.get_mut(id).links_mut(slot);
            links.prev = prev;
            links.next = pos;
        }
        match prev {
            Some(previous) => nodes.get_mut(previous).links_mut(slot).next = Some(id),
            None => self.head = Some(id),
        }
        match pos {
            Some(position) => nodes.get_mut(position).links_mut(slot).prev = Some(id),
            None => self.tail = Some(id),
        }
        self.len += 1;
    }

    pub fn remove<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, id: Id) -> Option<Id> {
        let slot = self.slot;
        let ListLinks { prev, next } = *nodes.get(id).links(slot);
        match prev {
            Some(previous) => nodes.get_mut(previous).links_mut(slot).next = next,
            None => {
                debug_assert!(self.head == Some(id), "removing node that is not in the list");
                self.head = next;
            }
        }
        match next {
            Some(following) => nodes.get_mut(following).links_mut(slot).prev = prev,
            None => {
                debug_assert!(self.tail == Some(id), "removing node that is not in the list");
                self.tail = prev;
            }
        }
        *nodes.get_mut(id).links_mut(slot) = ListLinks::default();
        self.len -= 1;
        next
    }

    pub fn splice_range<T: LinkedNode<Id>>(
        &mut self,
        nodes: &mut Arena<Id, T>,
        pos: Option<Id>,
        first: Id,
        end: Option<Id>,
    ) {
        if Some(first) == end || pos == Some(first) {
            return;
        }
        let mut moved = Vec::new();
        let mut current = Some(first);
        while current != end {
            let node = current.expect("splice range end is not after its start");
            if Some(node) == pos {
                return;
            }
            moved.push(node);
            current = nodes.get(node).links(self.slot).next;
        }
        for node in moved.iter() {
            self.remove(nodes, *node);
        }
        for node in moved {
            self.insert(nodes, pos, node);
        }
    }

    pub fn append_all<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>, other: &mut IntrusiveList<Id>) {
        let moved = other.to_vec(nodes);
        for node in moved.iter() {
            other.remove(nodes, *node);
        }
        for node in moved {
            self.push_back(nodes, node);
        }
    }

    pub fn clear<T: LinkedNode<Id>>(&mut self, nodes: &mut Arena<Id, T>) {
        let all = self.to_vec(nodes);
        for node in all {
            if nodes.contains(node) {
                *nodes.get_mut(node).links_mut(self.slot) = ListLinks::default();
            }
        }
        self.head = None;
        self.tail = None;
        self.len = 0;
    }

    pub fn iter<'list, T: LinkedNode<Id>>(&'list self, nodes: &'list Arena<Id, T>) -> ListIter<'list, Id, T> {
        ListIter {
            nodes,
            slot: self.slot,
            front: self.head,
            back: self.tail,
            remaining: self.len,
        }
    }

    pub fn to_vec<T: LinkedNode<Id>>(&self, nodes: &Arena<Id, T>) -> Vec<Id> {
        self.iter(nodes).collect()
    }
}

pub struct ListIter<'list, Id, T> {
    nodes: &'list Arena<Id, T>,
    slot: usize,
    front: Option<Id>,
    back: Option<Id>,
    remaining: usize,
}

impl<Id: ArenaId, T: LinkedNode<Id>> Iterator for ListIter<'_, Id, T> {
    type Item = Id;

    fn next(&mut self) -> Option<Id> {
        if self.remaining == 0 {
            return None;
        }
        let current = self.front?;
        self.front = self.nodes.get(current).links(self.slot).next;
        self.remaining -= 1;
        Some(current)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<Id: ArenaId, T: LinkedNode<Id>> DoubleEndedIterator for ListIter<'_, Id, T> {
    fn next_back(&mut self) -> Option<Id> {
        if self.remaining == 0 {
            return None;
        }
        let current = self.back?;
        self.back = self.nodes.get(current).links(self.slot).prev;
        self.remaining -= 1;
        Some(current)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::define_id;

    define_id!(NodeId);

    #[derive(Default)]
    struct Node {
        links: [ListLinks<NodeId>; 2],
    }

    impl LinkedNode<NodeId> for Node {
        fn links(&self, slot: usize) -> &ListLinks<NodeId> {
            &self.links[slot]
        }

        fn links_mut(&mut self, slot: usize) -> &mut ListLinks<NodeId> {
            &mut self.links[slot]
        }
    }

    fn build(count: usize) -> (Arena<NodeId, Node>, Vec<NodeId>) {
        let mut nodes = Arena::new();
        let ids = (0..count).map(|_| nodes.alloc(Node::default())).collect();
        (nodes, ids)
    }

    fn numbers(list: &IntrusiveList<NodeId>, nodes: &Arena<NodeId, Node>) -> Vec<u32> {
        list.iter(nodes).map(|id| id.0).collect()
    }

    #[test]
    fn push_insert_remove() {
        let (mut nodes, ids) = build(5);
        let mut list = IntrusiveList::new(0);
        list.push_back(&mut nodes, ids[1]);
        list.push_back(&mut nodes, ids[3]);
        list.push_front(&mut nodes, ids[0]);
        list.insert_before(&mut nodes, ids[3], ids[2]);
        list.insert_after(&mut nodes, ids[3], ids[4]);
        assert_eq!(numbers(&list, &nodes), vec![0, 1, 2, 3, 4]);
        assert_eq!(list.len(), 5);
        assert_eq!(list.front(), Some(ids[0]));
        assert_eq!(list.back(), Some(ids[4]));
        assert_eq!(list.next(&nodes, ids[2]), Some(ids[3]));
        assert_eq!(list.prev(&nodes, ids[2]), Some(ids[1]));
        assert_eq!(list.remove(&mut nodes, ids[2]), Some(ids[3]));
        assert_eq!(list.remove(&mut nodes, ids[4]), None);
        assert_eq!(list.remove(&mut nodes, ids[0]), Some(ids[1]));
        assert_eq!(numbers(&list, &nodes), vec![1, 3]);
        assert_eq!(list.iter(&nodes).rev().map(|id| id.0).collect::<Vec<u32>>(), vec![3, 1]);
        assert_eq!(nodes[ids[2]].links[0], ListLinks::default());
    }

    #[test]
    fn independent_slots() {
        let (mut nodes, ids) = build(3);
        let mut forward = IntrusiveList::new(0);
        let mut backward = IntrusiveList::new(1);
        for id in ids.iter() {
            forward.push_back(&mut nodes, *id);
            backward.push_front(&mut nodes, *id);
        }
        assert_eq!(numbers(&forward, &nodes), vec![0, 1, 2]);
        assert_eq!(numbers(&backward, &nodes), vec![2, 1, 0]);
        backward.remove(&mut nodes, ids[1]);
        assert_eq!(numbers(&forward, &nodes), vec![0, 1, 2]);
        assert_eq!(numbers(&backward, &nodes), vec![2, 0]);
    }

    #[test]
    fn splice_within_list() {
        let (mut nodes, ids) = build(6);
        let mut list = IntrusiveList::new(0);
        for id in ids.iter() {
            list.push_back(&mut nodes, *id);
        }
        list.splice_range(&mut nodes, Some(ids[1]), ids[3], Some(ids[5]));
        assert_eq!(numbers(&list, &nodes), vec![0, 3, 4, 1, 2, 5]);
        list.splice_range(&mut nodes, None, ids[0], Some(ids[4]));
        assert_eq!(numbers(&list, &nodes), vec![4, 1, 2, 5, 0, 3]);
        list.splice_range(&mut nodes, Some(ids[2]), ids[2], Some(ids[5]));
        assert_eq!(numbers(&list, &nodes), vec![4, 1, 2, 5, 0, 3]);
        assert_eq!(list.len(), 6);
    }

    #[test]
    fn append_and_clear() {
        let (mut nodes, ids) = build(4);
        let mut first = IntrusiveList::new(0);
        let mut second = IntrusiveList::new(0);
        first.push_back(&mut nodes, ids[0]);
        first.push_back(&mut nodes, ids[1]);
        second.push_back(&mut nodes, ids[2]);
        second.push_back(&mut nodes, ids[3]);
        first.append_all(&mut nodes, &mut second);
        assert_eq!(numbers(&first, &nodes), vec![0, 1, 2, 3]);
        assert!(second.is_empty());
        first.clear(&mut nodes);
        assert!(first.is_empty());
        assert_eq!(first.iter(&nodes).count(), 0);
        assert_eq!(nodes[ids[3]].links[0], ListLinks::default());
    }
}
