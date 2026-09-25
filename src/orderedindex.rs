use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::ops::{Bound, Deref};

const MINIMUM_PREFETCH_LENGTH: usize = 2;
const MAXIMUM_PREFETCH_LENGTH: usize = 16;

#[derive(Debug)]
struct Prefetch<K, V> {
    version: u64,
    start: Option<K>,
    entries: VecDeque<(K, V)>,
    complete: bool,
    length: usize,
}

#[derive(Debug)]
pub struct OrderedIndex<K, V> {
    map: BTreeMap<K, V>,
    version: u64,
    prefetch: RefCell<Prefetch<K, V>>,
}

impl<K: Ord + Copy, V: Copy> Default for OrderedIndex<K, V> {
    fn default() -> OrderedIndex<K, V> {
        OrderedIndex {
            map: BTreeMap::new(),
            version: 0,
            prefetch: RefCell::new(Prefetch {
                version: u64::MAX,
                start: None,
                entries: VecDeque::new(),
                complete: false,
                length: MINIMUM_PREFETCH_LENGTH,
            }),
        }
    }
}

impl<K: Ord + Copy, V: Copy> Deref for OrderedIndex<K, V> {
    type Target = BTreeMap<K, V>;

    fn deref(&self) -> &BTreeMap<K, V> {
        &self.map
    }
}

impl<K: Ord + Copy, V: Copy> OrderedIndex<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.version = self.version.wrapping_add(1);
        self.map.insert(key, value)
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.version = self.version.wrapping_add(1);
        self.map.remove(key)
    }

    pub fn clear(&mut self) {
        self.version = self.version.wrapping_add(1);
        self.map.clear();
    }

    pub fn entry_from(&self, key: &K) -> Option<(K, V, Option<K>)> {
        let mut prefetch = self.prefetch.borrow_mut();
        let reusable = prefetch.version == self.version && prefetch.start.is_some_and(|start| start <= *key);
        if reusable {
            while prefetch.entries.front().is_some_and(|(found, _)| found < key) {
                prefetch.entries.pop_front();
            }
            prefetch.start = Some(*key);
            if let Some(answer) = Self::buffered_answer(&prefetch) {
                return answer;
            }
        }
        prefetch.length = if reusable {
            (prefetch.length * 2).min(MAXIMUM_PREFETCH_LENGTH)
        } else {
            MINIMUM_PREFETCH_LENGTH
        };
        let length = prefetch.length;
        prefetch.version = self.version;
        prefetch.start = Some(*key);
        prefetch.entries.clear();
        for (found, value) in self.map.range((Bound::Included(key), Bound::Unbounded)).take(length) {
            prefetch.entries.push_back((*found, *value));
        }
        prefetch.complete = prefetch.entries.len() < length;
        Self::buffered_answer(&prefetch).unwrap_or(None)
    }

    fn buffered_answer(prefetch: &Prefetch<K, V>) -> Option<Option<(K, V, Option<K>)>> {
        match (prefetch.entries.front(), prefetch.entries.get(1)) {
            (Some((current, value)), Some((next, _))) => Some(Some((*current, *value, Some(*next)))),
            (Some((current, value)), None) if prefetch.complete => Some(Some((*current, *value, None))),
            (None, _) if prefetch.complete => Some(None),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expected_entry(map: &BTreeMap<u32, u32>, key: u32) -> Option<(u32, u32, Option<u32>)> {
        let mut range = map.range(key..);
        let (found, value) = range.next()?;
        Some((*found, *value, range.next().map(|(next, _)| *next)))
    }

    #[test]
    fn entry_from_interleaved_mutation() {
        let mut index: OrderedIndex<u32, u32> = OrderedIndex::default();
        let mut reference: BTreeMap<u32, u32> = BTreeMap::new();
        let mut state: u64 = 0x9e3779b97f4a7c15;
        let mut cursor = 0u32;
        for step in 0..200_000u32 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let key = (state % 512) as u32;
            match state >> 60 {
                0..=3 => {
                    assert_eq!(index.insert(key, step), reference.insert(key, step));
                }
                4..=6 => {
                    assert_eq!(index.remove(&key), reference.remove(&key));
                }
                7 => cursor = key,
                8 if step % 1000 == 0 => {
                    index.clear();
                    reference.clear();
                }
                _ => {
                    let actual = index.entry_from(&cursor);
                    assert_eq!(actual, expected_entry(&reference, cursor));
                    cursor = match actual {
                        Some((_, _, Some(next))) => next,
                        _ => 0,
                    };
                }
            }
        }
    }
}
