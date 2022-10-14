use crate::{Arena, BTreeMap, BTreeSet, SetArena};
use arbitrary::{Arbitrary, Result, Unstructured};

impl<'a, 'arena, K: Arbitrary<'a> + Ord, V: Arbitrary<'a>> BTreeMap<'arena, K, V> {
    /// Like `Arbitrary::arbitrary` but with an `Arena` parameter.
    pub fn arbitrary(
        arena: &'arena Arena<K, V>,
        u: &mut Unstructured<'a>,
    ) -> Result<BTreeMap<'arena, K, V>> {
        let mut map = BTreeMap::new(arena);
        for x in u.arbitrary_iter()? {
            let (k, v) = x?;
            map.insert(k, v);
        }
        Ok(map)
    }

    /// Like `Arbitrary::arbitrary_take_rest` but with an `Arena` parameter.
    pub fn arbitrary_take_rest(
        arena: &'arena Arena<K, V>,
        u: Unstructured<'a>,
    ) -> Result<BTreeMap<'arena, K, V>> {
        let mut map = BTreeMap::new(arena);
        for x in u.arbitrary_take_rest_iter()? {
            let (k, v) = x?;
            map.insert(k, v);
        }
        Ok(map)
    }
}

impl<'a, 'arena, A: Arbitrary<'a> + Ord> BTreeSet<'arena, A> {
    /// Like `Arbitrary::arbitrary` but with a `SetArena` parameter.
    pub fn arbitrary(
        arena: &'arena SetArena<A>,
        u: &mut Unstructured<'a>,
    ) -> Result<BTreeSet<'arena, A>> {
        let mut set = BTreeSet::new(arena);
        for x in u.arbitrary_iter()? {
            set.insert(x?);
        }
        Ok(set)
    }

    /// Like `Arbitrary::arbitrary_take_rest` but with a `SetArena` parameter.
    fn arbitrary_take_rest(
        arena: &'arena SetArena<A>,
        u: Unstructured<'a>,
    ) -> Result<BTreeSet<'arena, A>> {
        let mut set = BTreeSet::new(arena);
        for x in u.arbitrary_take_rest_iter()? {
            set.insert(x?);
        }
        Ok(set)
    }
}
