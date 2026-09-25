use std::fmt;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

pub trait ArenaId: Copy + Ord + fmt::Debug {
    fn from_index(index: usize) -> Self;
    fn index(self) -> usize;
}

#[macro_export]
macro_rules! define_id {
    ($name:ident) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u32);

        impl $crate::arena::ArenaId for $name {
            fn from_index(index: usize) -> $name {
                $name(u32::try_from(index).expect("arena index exceeds u32 range"))
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

pub struct Arena<Id, T> {
    slots: Vec<Option<T>>,
    live: usize,
    marker: PhantomData<Id>,
}

impl<Id: ArenaId, T> Default for Arena<Id, T> {
    fn default() -> Arena<Id, T> {
        Arena::new()
    }
}

impl<Id: ArenaId, T: Clone> Clone for Arena<Id, T> {
    fn clone(&self) -> Arena<Id, T> {
        Arena {
            slots: self.slots.clone(),
            live: self.live,
            marker: PhantomData,
        }
    }
}

impl<Id: ArenaId, T: fmt::Debug> fmt::Debug for Arena<Id, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

impl<Id: ArenaId, T> Arena<Id, T> {
    pub fn new() -> Arena<Id, T> {
        Arena {
            slots: Vec::new(),
            live: 0,
            marker: PhantomData,
        }
    }

    pub fn alloc(&mut self, value: T) -> Id {
        let id = Id::from_index(self.slots.len());
        self.slots.push(Some(value));
        self.live += 1;
        id
    }

    pub fn alloc_with(&mut self, build: impl FnOnce(Id) -> T) -> Id {
        let id = Id::from_index(self.slots.len());
        let value = build(id);
        self.slots.push(Some(value));
        self.live += 1;
        id
    }

    pub fn next_id(&self) -> Id {
        Id::from_index(self.slots.len())
    }

    pub fn contains(&self, id: Id) -> bool {
        matches!(self.slots.get(id.index()), Some(Some(_)))
    }

    pub fn get(&self, id: Id) -> &T {
        match self.slots.get(id.index()) {
            Some(Some(value)) => value,
            _ => panic!("stale or invalid arena id {:?}", id),
        }
    }

    pub fn get_mut(&mut self, id: Id) -> &mut T {
        match self.slots.get_mut(id.index()) {
            Some(Some(value)) => value,
            _ => panic!("stale or invalid arena id {:?}", id),
        }
    }

    pub fn try_get(&self, id: Id) -> Option<&T> {
        self.slots.get(id.index()).and_then(|slot| slot.as_ref())
    }

    pub fn try_get_mut(&mut self, id: Id) -> Option<&mut T> {
        self.slots.get_mut(id.index()).and_then(|slot| slot.as_mut())
    }

    pub fn get2_mut(&mut self, first: Id, second: Id) -> (&mut T, &mut T) {
        let first_index = first.index();
        let second_index = second.index();
        assert!(first_index != second_index, "get2_mut with identical ids {:?}", first);
        let (low, high, swapped) = if first_index < second_index {
            (first_index, second_index, false)
        } else {
            (second_index, first_index, true)
        };
        let (head, tail) = self.slots.split_at_mut(high);
        let low_value = head[low]
            .as_mut()
            .unwrap_or_else(|| panic!("stale or invalid arena id {:?}", Id::from_index(low)));
        let high_value = tail[0]
            .as_mut()
            .unwrap_or_else(|| panic!("stale or invalid arena id {:?}", Id::from_index(high)));
        if swapped {
            (high_value, low_value)
        } else {
            (low_value, high_value)
        }
    }

    pub fn remove(&mut self, id: Id) -> T {
        let value = self
            .slots
            .get_mut(id.index())
            .and_then(|slot| slot.take())
            .unwrap_or_else(|| panic!("stale or invalid arena id {:?}", id));
        self.live -= 1;
        value
    }

    pub fn clear(&mut self) {
        for slot in self.slots.iter_mut() {
            *slot = None;
        }
        self.live = 0;
    }

    pub fn len(&self) -> usize {
        self.live
    }

    pub fn is_empty(&self) -> bool {
        self.live == 0
    }

    pub fn capacity_ids(&self) -> usize {
        self.slots.len()
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (Id, &T)> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(index, slot)| slot.as_ref().map(|value| (Id::from_index(index), value)))
    }

    pub fn iter_mut(&mut self) -> impl DoubleEndedIterator<Item = (Id, &mut T)> {
        self.slots
            .iter_mut()
            .enumerate()
            .filter_map(|(index, slot)| slot.as_mut().map(|value| (Id::from_index(index), value)))
    }

    pub fn ids(&self) -> Vec<Id> {
        self.iter().map(|(id, _)| id).collect()
    }
}

impl<Id: ArenaId, T> Index<Id> for Arena<Id, T> {
    type Output = T;

    fn index(&self, id: Id) -> &T {
        self.get(id)
    }
}

impl<Id: ArenaId, T> IndexMut<Id> for Arena<Id, T> {
    fn index_mut(&mut self, id: Id) -> &mut T {
        self.get_mut(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    define_id!(TestId);

    #[test]
    fn alloc_and_access() {
        let mut arena: Arena<TestId, String> = Arena::new();
        let first = arena.alloc("first".to_string());
        let second = arena.alloc_with(|id| format!("id{}", id.0));
        assert_eq!(first, TestId(0));
        assert_eq!(second, TestId(1));
        assert_eq!(arena[first], "first");
        assert_eq!(arena.get(second), "id1");
        arena[first].push('!');
        assert_eq!(arena[first], "first!");
        assert_eq!(arena.len(), 2);
        assert_eq!(arena.next_id(), TestId(2));
        assert!(first < second);
    }

    #[test]
    fn removal_never_reuses_slots() {
        let mut arena: Arena<TestId, i32> = Arena::new();
        let first = arena.alloc(10);
        let second = arena.alloc(20);
        assert_eq!(arena.remove(first), 10);
        assert!(!arena.contains(first));
        assert!(arena.try_get(first).is_none());
        let third = arena.alloc(30);
        assert_eq!(third, TestId(2));
        assert_eq!(arena.len(), 2);
        let live: Vec<(TestId, i32)> = arena.iter().map(|(id, value)| (id, *value)).collect();
        assert_eq!(live, vec![(second, 20), (third, 30)]);
        assert_eq!(arena.ids(), vec![second, third]);
        arena.clear();
        assert!(arena.is_empty());
        assert_eq!(arena.alloc(40), TestId(3));
        assert_eq!(arena.capacity_ids(), 4);
    }

    #[test]
    #[should_panic(expected = "stale or invalid arena id")]
    fn stale_id_panics() {
        let mut arena: Arena<TestId, i32> = Arena::new();
        let first = arena.alloc(1);
        arena.remove(first);
        let _value = arena.get(first);
    }

    #[test]
    fn two_mutable_borrows() {
        let mut arena: Arena<TestId, i32> = Arena::new();
        let first = arena.alloc(1);
        let second = arena.alloc(2);
        {
            let (high, low) = arena.get2_mut(second, first);
            *high += 10;
            *low += 100;
        }
        assert_eq!(arena[first], 101);
        assert_eq!(arena[second], 12);
        for (_, value) in arena.iter_mut() {
            *value *= 2;
        }
        assert_eq!(arena[first], 202);
    }
}
