use crate::{Arena, BTreeMap, BTreeSet, SetArena};
use arbitrary::{Arbitrary, Result, Unstructured};

impl<'a, K: Arbitrary<'a> + Ord, V: Arbitrary<'a>> BTreeMap<K, V> {
    /// TODO FITZGEN
    pub fn arbitrary(arena: &mut Arena<K, V>, u: &mut Unstructured<'a>) -> Result<Self> {
        let mut map = BTreeMap::new(arena);
        for x in u.arbitrary_iter()? {
            let (k, v) = x?;
            map.insert(arena, k, v);
        }
        Ok(map)
    }

    /// TODO FITZGEN
    pub fn arbitrary_take_rest(arena: &mut Arena<K, V>, u: Unstructured<'a>) -> Result<Self> {
        let mut map = BTreeMap::new(arena);
        for x in u.arbitrary_take_rest_iter()? {
            let (k, v) = x?;
            map.insert(arena, k, v);
        }
        Ok(map)
    }

    /// TODO FITZGEN
    #[inline]
    pub fn arbitrary_size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a> + Ord> BTreeSet<A> {
    /// TODO FITZGEN
    pub fn arbitrary(arena: &mut SetArena<A>, u: &mut Unstructured<'a>) -> Result<Self> {
        let mut set = BTreeSet::new(arena);
        for a in u.arbitrary_iter()? {
            let a = a?;
            set.insert(arena, a);
        }
        Ok(set)
    }

    /// TODO FITZGEN
    pub fn arbitrary_take_rest(arena: &mut SetArena<A>, u: Unstructured<'a>) -> Result<Self> {
        let mut set = BTreeSet::new(arena);
        for a in u.arbitrary_take_rest_iter()? {
            let a = a?;
            set.insert(arena, a);
        }
        Ok(set)
    }

    /// TODO FITZGEN
    #[inline]
    pub fn arbitrary_size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}
