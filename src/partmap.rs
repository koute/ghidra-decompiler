use std::collections::BTreeMap;
use std::ops::Bound;

#[derive(Clone, Debug, Default)]
pub struct PartMap<L: Ord + Clone, V: Clone + Default> {
    database: BTreeMap<L, V>,
    defaultvalue: V,
}

#[derive(Clone, Debug)]
pub struct PartBounds<L> {
    pub before: Option<L>,
    pub after: Option<L>,
    pub valid: i32,
}

impl<L: Ord + Clone, V: Clone + Default> PartMap<L, V> {
    pub fn new() -> PartMap<L, V> {
        PartMap {
            database: BTreeMap::new(),
            defaultvalue: V::default(),
        }
    }

    pub fn duplicate(&self, copy: impl Fn(&V) -> V) -> PartMap<L, V> {
        PartMap {
            database: self
                .database
                .iter()
                .map(|(key, value)| (key.clone(), copy(value)))
                .collect(),
            defaultvalue: copy(&self.defaultvalue),
        }
    }

    fn last_at_or_before(&self, pnt: &L) -> Option<&L> {
        self.database
            .range((Bound::Unbounded, Bound::Included(pnt)))
            .next_back()
            .map(|(key, _)| key)
    }

    pub fn get_value(&self, pnt: &L) -> &V {
        match self
            .database
            .range((Bound::Unbounded, Bound::Included(pnt)))
            .next_back()
        {
            Some((_, value)) => value,
            None => &self.defaultvalue,
        }
    }

    pub fn get_value_mut(&mut self, pnt: &L) -> &mut V {
        match self.last_at_or_before(pnt).cloned() {
            Some(key) => self.database.get_mut(&key).expect("partition key exists"),
            None => &mut self.defaultvalue,
        }
    }

    pub fn get_partition_key(&self, pnt: &L) -> Option<L> {
        self.last_at_or_before(pnt).cloned()
    }

    pub fn get_by_key(&self, key: Option<&L>) -> &V {
        match key {
            Some(key) => self.database.get(key).unwrap_or(&self.defaultvalue),
            None => &self.defaultvalue,
        }
    }

    pub fn bounds(&self, pnt: &L) -> (&V, PartBounds<L>) {
        if self.database.is_empty() {
            return (
                &self.defaultvalue,
                PartBounds {
                    before: None,
                    after: None,
                    valid: 3,
                },
            );
        }
        let after = self
            .database
            .range((Bound::Excluded(pnt), Bound::Unbounded))
            .next()
            .map(|(key, _)| key.clone());
        if let Some((before_key, value)) = self
            .database
            .range((Bound::Unbounded, Bound::Included(pnt)))
            .next_back()
        {
            let valid = if after.is_none() { 2 } else { 0 };
            return (
                value,
                PartBounds {
                    before: Some(before_key.clone()),
                    after,
                    valid,
                },
            );
        }
        (
            &self.defaultvalue,
            PartBounds {
                before: None,
                after,
                valid: 1,
            },
        )
    }

    pub fn split(&mut self, pnt: &L) -> &mut V {
        let previous = self.last_at_or_before(pnt).cloned();
        match previous {
            Some(key) if key == *pnt => self.database.get_mut(pnt).expect("partition key exists"),
            Some(key) => {
                let copy = self.database.get(&key).expect("partition key exists").clone();
                self.database.insert(pnt.clone(), copy);
                self.database.get_mut(pnt).expect("partition key exists")
            }
            None => {
                let copy = self.defaultvalue.clone();
                self.database.insert(pnt.clone(), copy);
                self.database.get_mut(pnt).expect("partition key exists")
            }
        }
    }

    pub fn default_value(&self) -> &V {
        &self.defaultvalue
    }

    pub fn default_value_mut(&mut self) -> &mut V {
        &mut self.defaultvalue
    }

    pub fn clear_range(&mut self, pnt1: &L, pnt2: &L) -> &mut V {
        self.split(pnt1);
        self.split(pnt2);
        if pnt1 < pnt2 {
            let doomed: Vec<L> = self
                .database
                .range((Bound::Excluded(pnt1), Bound::Excluded(pnt2)))
                .map(|(key, _)| key.clone())
                .collect();
            for key in doomed {
                self.database.remove(&key);
            }
        }
        self.database.get_mut(pnt1).expect("partition key exists")
    }

    pub fn iter(&self) -> impl Iterator<Item = (&L, &V)> {
        self.database.iter()
    }

    pub fn keys_from(&self, pnt: &L) -> Vec<L> {
        self.database
            .range((Bound::Included(pnt), Bound::Unbounded))
            .map(|(key, _)| key.clone())
            .collect()
    }

    pub fn get_mut(&mut self, key: &L) -> Option<&mut V> {
        self.database.get_mut(key)
    }

    pub fn clear(&mut self) {
        self.database.clear();
    }

    pub fn empty(&self) -> bool {
        self.database.is_empty()
    }
}
