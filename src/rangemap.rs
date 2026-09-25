use std::cmp::Ordering;

use crate::address::Address;
use crate::arena::Arena;
use crate::define_id;
use crate::oplist::{IntrusiveList, LinkedNode, ListLinks};

define_id!(RangeRecordId);

pub trait RangeLine: Clone + Ord {
    fn plus_one(&self) -> Self;
    fn minus_one(&self) -> Self;
}

impl RangeLine for u64 {
    fn plus_one(&self) -> u64 {
        self.wrapping_add(1)
    }

    fn minus_one(&self) -> u64 {
        self.wrapping_sub(1)
    }
}

impl RangeLine for Address {
    fn plus_one(&self) -> Address {
        self.add(1)
    }

    fn minus_one(&self) -> Address {
        self.sub(1)
    }
}

pub trait RangeSubsort: Clone + Ord {
    fn from_bool(val: bool) -> Self;
}

pub trait RangeRecord {
    type Line: RangeLine;
    type Subsort: RangeSubsort;
    type Init;

    fn new_record(data: &Self::Init, first: Self::Line, last: Self::Line) -> Self;
    fn get_first(&self) -> Self::Line;
    fn get_last(&self) -> Self::Line;
    fn get_subsort(&self) -> Self::Subsort;
}

#[derive(Clone, Debug)]
pub struct AddrRange<L, S> {
    pub first: L,
    pub last: L,
    pub a: L,
    pub b: L,
    pub subsort: S,
    pub value: RangeRecordId,
}

impl<L: Ord, S: Ord> AddrRange<L, S> {
    fn compare_key(&self, last: &L, subsort: &S) -> Ordering {
        self.last.cmp(last).then_with(|| self.subsort.cmp(subsort))
    }

    pub fn get_value(&self) -> RangeRecordId {
        self.value
    }
}

pub struct RecordNode<R> {
    pub record: R,
    links: [ListLinks<RangeRecordId>; 1],
}

impl<R> LinkedNode<RangeRecordId> for RecordNode<R> {
    fn links(&self, slot: usize) -> &ListLinks<RangeRecordId> {
        &self.links[slot]
    }

    fn links_mut(&mut self, slot: usize) -> &mut ListLinks<RangeRecordId> {
        &mut self.links[slot]
    }
}

pub type PartIterator = usize;

pub struct RangeMap<R: RangeRecord> {
    tree: Vec<AddrRange<R::Line, R::Subsort>>,
    records: Arena<RangeRecordId, RecordNode<R>>,
    record: IntrusiveList<RangeRecordId>,
}

impl<R: RangeRecord> Default for RangeMap<R> {
    fn default() -> RangeMap<R> {
        RangeMap::new()
    }
}

impl<R: RangeRecord> RangeMap<R> {
    pub fn new() -> RangeMap<R> {
        RangeMap {
            tree: Vec::new(),
            records: Arena::new(),
            record: IntrusiveList::new(0),
        }
    }

    fn lower_bound(&self, last: &R::Line, subsort: &R::Subsort) -> usize {
        self.tree
            .partition_point(|range| range.compare_key(last, subsort) == Ordering::Less)
    }

    fn upper_bound(&self, last: &R::Line, subsort: &R::Subsort) -> usize {
        self.tree
            .partition_point(|range| range.compare_key(last, subsort) != Ordering::Greater)
    }

    fn insert_plain(&mut self, range: AddrRange<R::Line, R::Subsort>) -> usize {
        let pos = self.upper_bound(&range.last, &range.subsort);
        self.tree.insert(pos, range);
        pos
    }

    fn insert_hint(&mut self, hint: usize, range: AddrRange<R::Line, R::Subsort>) -> usize {
        let len = self.tree.len();
        let less = |first: &AddrRange<R::Line, R::Subsort>, second: &AddrRange<R::Line, R::Subsort>| {
            first.compare_key(&second.last, &second.subsort) == Ordering::Less
        };
        let pos = if hint == len {
            if len > 0 && !less(&range, &self.tree[len - 1]) {
                len
            } else {
                self.upper_bound(&range.last, &range.subsort)
            }
        } else if !less(&self.tree[hint], &range) {
            if hint == 0 {
                0
            } else if !less(&range, &self.tree[hint - 1]) {
                hint
            } else {
                self.upper_bound(&range.last, &range.subsort)
            }
        } else if hint == len - 1 {
            len
        } else if !less(&self.tree[hint + 1], &range) {
            hint + 1
        } else {
            self.lower_bound(&range.last, &range.subsort)
        };
        self.tree.insert(pos, range);
        pos
    }

    fn zip(&mut self, line: R::Line, mut iter: usize) {
        let first_value = self.tree[iter].first.clone();
        while iter < self.tree.len() && self.tree[iter].last == line {
            self.tree.remove(iter);
        }
        let line = line.plus_one();
        while iter != self.tree.len() && self.tree[iter].first == line {
            self.tree[iter].first = first_value.clone();
            iter += 1;
        }
    }

    fn unzip(&mut self, line: R::Line, mut iter: usize) -> usize {
        let mut hint = iter;
        let mut inserted = 0;
        if self.tree[iter].last == line {
            return inserted;
        }
        let plus1 = line.plus_one();
        while iter != self.tree.len() && self.tree[iter].first <= line {
            let first_value = self.tree[iter].first.clone();
            self.tree[iter].first = plus1.clone();
            let current = &self.tree[iter];
            let newrange = AddrRange {
                first: first_value,
                last: line.clone(),
                a: current.a.clone(),
                b: current.b.clone(),
                subsort: current.subsort.clone(),
                value: current.value,
            };
            let pos = self.insert_hint(hint, newrange);
            inserted += 1;
            if pos <= hint {
                hint += 1;
            }
            if pos <= iter {
                iter += 1;
            }
            iter += 1;
        }
        inserted
    }

    pub fn empty(&self) -> bool {
        self.record.is_empty()
    }

    pub fn clear(&mut self) {
        self.tree.clear();
        self.records.clear();
        self.record = IntrusiveList::new(0);
    }

    pub fn list_ids(&self) -> Vec<RangeRecordId> {
        self.record.to_vec(&self.records)
    }

    pub fn list_front(&self) -> Option<RangeRecordId> {
        self.record.front()
    }

    pub fn list_next(&self, id: RangeRecordId) -> Option<RangeRecordId> {
        self.record.next(&self.records, id)
    }

    pub fn list_iter(&self) -> impl Iterator<Item = (RangeRecordId, &R)> + '_ {
        self.record
            .iter(&self.records)
            .map(move |id| (id, &self.records.get(id).record))
    }

    pub fn record(&self, id: RangeRecordId) -> &R {
        &self.records.get(id).record
    }

    pub fn record_mut(&mut self, id: RangeRecordId) -> &mut R {
        &mut self.records.get_mut(id).record
    }

    pub fn begin(&self) -> PartIterator {
        0
    }

    pub fn end(&self) -> PartIterator {
        self.tree.len()
    }

    pub fn part(&self, iter: PartIterator) -> &R {
        self.record(self.tree[iter].value)
    }

    pub fn get_value_iter(&self, iter: PartIterator) -> RangeRecordId {
        self.tree[iter].value
    }

    pub fn part_range(&self, iter: PartIterator) -> &AddrRange<R::Line, R::Subsort> {
        &self.tree[iter]
    }

    pub fn find(&self, point: &R::Line) -> (PartIterator, PartIterator) {
        let iter1 = self.lower_bound(point, &R::Subsort::from_bool(false));
        if iter1 == self.tree.len() || *point < self.tree[iter1].first {
            return (iter1, iter1);
        }
        let iter2 = self.upper_bound(&self.tree[iter1].last, &R::Subsort::from_bool(true));
        (iter1, iter2)
    }

    pub fn find_subsort(&self, point: &R::Line, sub1: &R::Subsort, sub2: &R::Subsort) -> (PartIterator, PartIterator) {
        let iter1 = self.lower_bound(point, sub1);
        if iter1 == self.tree.len() || *point < self.tree[iter1].first {
            return (iter1, iter1);
        }
        let iter2 = self.upper_bound(&self.tree[iter1].last, sub2);
        (iter1, iter2)
    }

    pub fn find_begin(&self, point: &R::Line) -> PartIterator {
        self.lower_bound(point, &R::Subsort::from_bool(false))
    }

    pub fn find_end(&self, point: &R::Line) -> PartIterator {
        let iter = self.upper_bound(point, &R::Subsort::from_bool(true));
        if iter == self.tree.len() || *point < self.tree[iter].first {
            return iter;
        }
        self.upper_bound(&self.tree[iter].last, &R::Subsort::from_bool(true))
    }

    pub fn find_overlap(&self, point: &R::Line, end: &R::Line) -> PartIterator {
        let iter = self.lower_bound(point, &R::Subsort::from_bool(false));
        if iter == self.tree.len() {
            return iter;
        }
        if self.tree[iter].first <= *end {
            return iter;
        }
        self.tree.len()
    }

    pub fn find_first_after(&self, point: &R::Line) -> PartIterator {
        let mut iter = self.find_end(point);
        while iter != self.tree.len() {
            if *point < self.tree[iter].a {
                return iter;
            }
            iter += 1;
        }
        iter
    }

    pub fn find_last_before(&self, point: &R::Line) -> PartIterator {
        let mut iter = self.find_begin(point);
        while iter != 0 {
            iter -= 1;
            if self.tree[iter].b < *point {
                return iter;
            }
        }
        self.tree.len()
    }

    pub fn insert(&mut self, data: &R::Init, first_2: R::Line, second: R::Line) -> RangeRecordId {
        let mut bound = first_2.clone();
        let mut low = self.lower_bound(&bound, &R::Subsort::from_bool(false));
        if low != self.tree.len() && self.tree[low].first < bound {
            let shift = self.unzip(bound.minus_one(), low);
            low += shift;
        }
        let liter = self.records.alloc(RecordNode {
            record: R::new_record(data, first_2.clone(), second.clone()),
            links: [ListLinks::default()],
        });
        let subsort = self.records.get(liter).record.get_subsort();
        let mut addrrange = AddrRange {
            first: second.clone(),
            last: second.clone(),
            a: first_2.clone(),
            b: second.clone(),
            subsort,
            value: liter,
        };
        let spot = self.lower_bound(&addrrange.last, &addrrange.subsort);
        let position = if spot == self.tree.len() {
            None
        } else {
            Some(self.tree[spot].value)
        };
        self.record.insert(&mut self.records, position, liter);
        while low != self.tree.len() && self.tree[low].first <= second {
            if bound <= self.tree[low].last {
                if bound < self.tree[low].first {
                    addrrange.first = bound.clone();
                    addrrange.last = self.tree[low].first.minus_one();
                    let pos = self.insert_hint(low, addrrange.clone());
                    if pos <= low {
                        low += 1;
                    }
                    bound = self.tree[low].first.clone();
                }
                if self.tree[low].last <= second {
                    addrrange.first = bound.clone();
                    addrrange.last = self.tree[low].last.clone();
                    let pos = self.insert_hint(low, addrrange.clone());
                    if pos <= low {
                        low += 1;
                    }
                    if self.tree[low].last == second {
                        break;
                    }
                    bound = self.tree[low].last.plus_one();
                } else if second < self.tree[low].last {
                    self.unzip(second.clone(), low);
                    break;
                }
            }
            low += 1;
        }
        if bound <= second {
            addrrange.first = bound;
            addrrange.last = second;
            self.insert_plain(addrrange);
        }
        liter
    }

    pub fn erase(&mut self, record: RangeRecordId) {
        let first = self.record(record).get_first();
        let last = self.record(record).get_last();
        let mut leftsew = true;
        let mut rightsew = true;
        let mut rightoverlap = false;
        let mut leftoverlap = false;
        let mut low = self.lower_bound(&first, &R::Subsort::from_bool(false));
        let mut uplow = low;
        let aminus1 = first.minus_one();
        while uplow != 0 {
            uplow -= 1;
            if self.tree[uplow].last != aminus1 {
                break;
            }
            if self.tree[uplow].b == aminus1 {
                leftsew = false;
                break;
            }
        }
        loop {
            if self.tree[low].value == record {
                self.tree.remove(low);
            } else {
                if self.tree[low].a < first {
                    leftoverlap = true;
                } else if self.tree[low].a == first {
                    leftsew = false;
                }
                if last < self.tree[low].b {
                    rightoverlap = true;
                } else if self.tree[low].b == last {
                    rightsew = false;
                }
                low += 1;
            }
            if !(low != self.tree.len() && self.tree[low].first <= last) {
                break;
            }
        }
        if low != self.tree.len() && self.tree[low].a.minus_one() == last {
            rightsew = false;
        }
        if leftsew && leftoverlap {
            let start = self.lower_bound(&aminus1, &R::Subsort::from_bool(false));
            self.zip(aminus1, start);
        }
        if rightsew && rightoverlap {
            let start = self.lower_bound(&last, &R::Subsort::from_bool(false));
            self.zip(last, start);
        }
        self.record.remove(&mut self.records, record);
        self.records.remove(record);
    }

    pub fn erase_part(&mut self, iter: PartIterator) {
        let value = self.get_value_iter(iter);
        self.erase(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct TestSubsort(u32);

    impl RangeSubsort for TestSubsort {
        fn from_bool(val: bool) -> TestSubsort {
            if val { TestSubsort(u32::MAX) } else { TestSubsort(0) }
        }
    }

    struct TestRecord {
        first: u64,
        last: u64,
        tag: u32,
    }

    impl RangeRecord for TestRecord {
        type Line = u64;
        type Subsort = TestSubsort;
        type Init = u32;

        fn new_record(data: &u32, first_2: u64, second: u64) -> TestRecord {
            TestRecord {
                first: first_2,
                last: second,
                tag: *data,
            }
        }

        fn get_first(&self) -> u64 {
            self.first
        }

        fn get_last(&self) -> u64 {
            self.last
        }

        fn get_subsort(&self) -> TestSubsort {
            TestSubsort(self.tag)
        }
    }

    fn tags_at(map: &RangeMap<TestRecord>, point: u64) -> Vec<u32> {
        let (start, stop) = map.find(&point);
        (start..stop).map(|iter| map.part(iter).tag).collect()
    }

    fn parts(map: &RangeMap<TestRecord>) -> Vec<(u64, u64, u32)> {
        (map.begin()..map.end())
            .map(|iter| {
                let range = map.part_range(iter);
                (range.first, range.last, map.part(iter).tag)
            })
            .collect()
    }

    #[test]
    fn overlapping_insert_and_erase() {
        let mut map: RangeMap<TestRecord> = RangeMap::new();
        let first = map.insert(&1, 10, 19);
        let second = map.insert(&2, 15, 24);
        assert_eq!(parts(&map), vec![(10, 14, 1), (15, 19, 1), (15, 19, 2), (20, 24, 2)]);
        assert_eq!(tags_at(&map, 12), vec![1]);
        assert_eq!(tags_at(&map, 17), vec![1, 2]);
        assert_eq!(tags_at(&map, 22), vec![2]);
        assert_eq!(tags_at(&map, 30), Vec::<u32>::new());
        let listed: Vec<u32> = map.list_iter().map(|(_, record)| record.tag).collect();
        assert_eq!(listed, vec![1, 2]);
        map.erase(first);
        assert_eq!(parts(&map), vec![(15, 24, 2)]);
        assert_eq!(tags_at(&map, 17), vec![2]);
        map.erase(second);
        assert!(map.empty());
        assert_eq!(map.end(), 0);
    }

    #[test]
    fn nested_insert_and_queries() {
        let mut map: RangeMap<TestRecord> = RangeMap::new();
        map.insert(&1, 0, 99);
        map.insert(&2, 40, 49);
        assert_eq!(parts(&map), vec![(0, 39, 1), (40, 49, 1), (40, 49, 2), (50, 99, 1)]);
        assert_eq!(tags_at(&map, 45), vec![1, 2]);
        assert_eq!(map.part(map.find_overlap(&45, &46)).tag, 1);
        assert_eq!(map.find_first_after(&45), map.end());
        assert_eq!(map.find_last_before(&45), map.end());
        let listed: Vec<u32> = map.list_iter().map(|(_, record)| record.tag).collect();
        assert_eq!(listed, vec![2, 1]);
    }

    #[test]
    fn disjoint_neighbors() {
        let mut map: RangeMap<TestRecord> = RangeMap::new();
        map.insert(&1, 0, 9);
        map.insert(&2, 20, 29);
        let after = map.find_first_after(&5);
        assert_eq!(map.part(after).tag, 2);
        let before = map.find_last_before(&25);
        assert_eq!(map.part(before).tag, 1);
        assert_eq!(map.find_begin(&15), 1);
        assert_eq!(map.find_end(&5), 1);
    }
}
