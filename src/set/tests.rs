use super::super::testing::crash_test::{CrashTestDummy, Panic};
use super::super::testing::rng::DeterministicRng;
use super::*;
use crate::SetArena;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Bound::{Excluded, Included};
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn test_clone_eq() {
    let arena = SetArena::new();
    let mut m = BTreeSet::new(&arena);

    m.insert(1);
    m.insert(2);

    assert_eq!(m.clone(), m);
}

#[test]
fn test_iter_min_max() {
    let arena = SetArena::new();
    let mut a = BTreeSet::new(&arena);
    assert_eq!(a.iter().min(), None);
    assert_eq!(a.iter().max(), None);
    assert_eq!(a.range(..).min(), None);
    assert_eq!(a.range(..).max(), None);
    a.insert(1);
    a.insert(2);
    assert_eq!(a.iter().min(), Some(&1));
    assert_eq!(a.iter().max(), Some(&2));
    assert_eq!(a.range(..).min(), Some(&1));
    assert_eq!(a.range(..).max(), Some(&2));
}

fn check<F>(a: &[i32], b: &[i32], expected: &[i32], f: F)
where
    F: for<'arena> FnOnce(
        &BTreeSet<'arena, i32>,
        &BTreeSet<'arena, i32>,
        &mut dyn FnMut(&i32) -> bool,
    ) -> bool,
{
    let arena = SetArena::new();
    let mut set_a = BTreeSet::new(&arena);
    let arena = SetArena::new();
    let mut set_b = BTreeSet::new(&arena);

    for x in a {
        assert!(set_a.insert(*x))
    }
    for y in b {
        assert!(set_b.insert(*y))
    }

    let mut i = 0;
    f(&set_a, &set_b, &mut |&x| {
        if i < expected.len() {
            assert_eq!(x, expected[i]);
        }
        i += 1;
        true
    });
    assert_eq!(i, expected.len());
}

#[test]
fn test_retain() {
    let arena = SetArena::new();
    let mut set = BTreeSet::from_iter(&arena, [1, 2, 3, 4, 5, 6]);
    set.retain(|&k| k % 2 == 0);
    assert_eq!(set.len(), 3);
    assert!(set.contains(&2));
    assert!(set.contains(&4));
    assert!(set.contains(&6));
}

#[test]
fn test_drain_filter() {
    let arena = SetArena::new();
    let mut x = BTreeSet::from_iter(&arena, [1]);
    let arena = SetArena::new();
    let mut y = BTreeSet::from_iter(&arena, [1]);

    x.drain_filter(|_| true);
    y.drain_filter(|_| false);
    assert_eq!(x.len(), 0);
    assert_eq!(y.len(), 1);
}

#[test]
fn test_drain_filter_drop_panic_leak() {
    let a = CrashTestDummy::new(0);
    let b = CrashTestDummy::new(1);
    let c = CrashTestDummy::new(2);
    let arena = SetArena::new();
    let mut set = BTreeSet::new(&arena);
    set.insert(a.spawn(Panic::Never));
    set.insert(b.spawn(Panic::InDrop));
    set.insert(c.spawn(Panic::Never));

    catch_unwind(move || drop(set.drain_filter(|dummy| dummy.query(true)))).ok();

    assert_eq!(a.queried(), 1);
    assert_eq!(b.queried(), 1);
    assert_eq!(c.queried(), 0);
    assert_eq!(a.dropped(), 1);
    assert_eq!(b.dropped(), 1);
    assert_eq!(c.dropped(), 1);
}

#[test]
fn test_drain_filter_pred_panic_leak() {
    let a = CrashTestDummy::new(0);
    let b = CrashTestDummy::new(1);
    let c = CrashTestDummy::new(2);
    let arena = SetArena::new();
    let mut set = BTreeSet::new(&arena);
    set.insert(a.spawn(Panic::Never));
    set.insert(b.spawn(Panic::InQuery));
    set.insert(c.spawn(Panic::InQuery));

    catch_unwind(AssertUnwindSafe(|| {
        drop(set.drain_filter(|dummy| dummy.query(true)))
    }))
    .ok();

    assert_eq!(a.queried(), 1);
    assert_eq!(b.queried(), 1);
    assert_eq!(c.queried(), 0);
    assert_eq!(a.dropped(), 1);
    assert_eq!(b.dropped(), 0);
    assert_eq!(c.dropped(), 0);
    assert_eq!(set.len(), 2);
    // assert_eq!(set.first().unwrap().id(), 1);
    // assert_eq!(set.last().unwrap().id(), 2);
}

#[test]
fn test_clear() {
    let arena = SetArena::new();
    let mut x = BTreeSet::new(&arena);
    x.insert(1);

    x.clear();
    assert!(x.is_empty());
}
#[test]
fn test_remove() {
    let arena = SetArena::new();
    let mut x = BTreeSet::new(&arena);
    assert!(x.is_empty());

    x.insert(1);
    x.insert(2);
    x.insert(3);
    x.insert(4);

    assert_eq!(x.remove(&2), true);
    assert_eq!(x.remove(&0), false);
    assert_eq!(x.remove(&5), false);
    assert_eq!(x.remove(&1), true);
    assert_eq!(x.remove(&2), false);
    assert_eq!(x.remove(&3), true);
    assert_eq!(x.remove(&4), true);
    assert_eq!(x.remove(&4), false);
    assert!(x.is_empty());
}

#[test]
fn test_zip() {
    let arena = SetArena::new();
    let mut x = BTreeSet::new(&arena);
    x.insert(5);
    x.insert(12);
    x.insert(11);

    let arena = SetArena::new();
    let mut y = BTreeSet::new(&arena);
    y.insert("foo");
    y.insert("bar");

    let x = x;
    let y = y;
    let mut z = x.iter().zip(&y);

    assert_eq!(z.next().unwrap(), (&5, &("bar")));
    assert_eq!(z.next().unwrap(), (&11, &("foo")));
    assert!(z.next().is_none());
}

#[test]
fn test_from_iter() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];

    let arena = SetArena::new();
    let set = BTreeSet::from_iter(&arena, xs.iter());

    for x in &xs {
        assert!(set.contains(x));
    }
}

#[test]
fn test_show() {
    let arena = SetArena::new();
    let mut set = BTreeSet::new(&arena);
    let arena = SetArena::new();
    let empty = BTreeSet::<i32>::new(&arena);

    set.insert(1);
    set.insert(2);

    let set_str = format!("{set:?}");

    assert_eq!(set_str, "{1, 2}");
    assert_eq!(format!("{empty:?}"), "{}");
}

#[test]
fn test_extend_ref() {
    let arena = SetArena::new();
    let mut a = BTreeSet::new(&arena);
    a.insert(1);

    a.extend(&[2, 3, 4]);

    assert_eq!(a.len(), 4);
    assert!(a.contains(&1));
    assert!(a.contains(&2));
    assert!(a.contains(&3));
    assert!(a.contains(&4));

    let arena = SetArena::new();
    let mut b = BTreeSet::new(&arena);
    b.insert(5);
    b.insert(6);

    a.extend(&b);

    assert_eq!(a.len(), 6);
    assert!(a.contains(&1));
    assert!(a.contains(&2));
    assert!(a.contains(&3));
    assert!(a.contains(&4));
    assert!(a.contains(&5));
    assert!(a.contains(&6));
}

#[test]
fn test_recovery() {
    #[derive(Debug)]
    struct Foo(&'static str, i32);

    impl PartialEq for Foo {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl Eq for Foo {}

    impl PartialOrd for Foo {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.0.partial_cmp(&other.0)
        }
    }

    impl Ord for Foo {
        fn cmp(&self, other: &Self) -> Ordering {
            self.0.cmp(&other.0)
        }
    }

    let arena = SetArena::new();
    let mut s = BTreeSet::new(&arena);
    assert_eq!(s.replace(Foo("a", 1)), None);
    assert_eq!(s.len(), 1);
    assert_eq!(s.replace(Foo("a", 2)), Some(Foo("a", 1)));
    assert_eq!(s.len(), 1);

    {
        let mut it = s.iter();
        assert_eq!(it.next(), Some(&Foo("a", 2)));
        assert_eq!(it.next(), None);
    }

    assert_eq!(s.get(&Foo("a", 1)), Some(&Foo("a", 2)));
    assert_eq!(s.take(&Foo("a", 1)), Some(Foo("a", 2)));
    assert_eq!(s.len(), 0);

    assert_eq!(s.get(&Foo("a", 1)), None);
    assert_eq!(s.take(&Foo("a", 1)), None);

    assert_eq!(s.iter().next(), None);
}

#[allow(dead_code)]
// Check that the member-like functions conditionally provided by #[derive()]
// are not overridden by genuine member functions with a different signature.
fn assert_derives() {
    fn hash<'arena, T: Hash, H: Hasher>(v: BTreeSet<'arena, T>, state: &mut H) {
        v.hash(state);
        // Tested much more thoroughly outside the crate in btree_set_hash.rs
    }
    fn eq<'arena, T: PartialEq>(v: BTreeSet<'arena, T>) {
        let _ = v.eq(&v);
    }
    fn ne<'arena, T: PartialEq>(v: BTreeSet<'arena, T>) {
        let _ = v.ne(&v);
    }
    fn cmp<'arena, T: Ord>(v: BTreeSet<'arena, T>) {
        let _ = v.cmp(&v);
    }
    fn min<'arena, T: Ord>(v: BTreeSet<'arena, T>, w: BTreeSet<'arena, T>) {
        let _ = v.min(w);
    }
    fn max<'arena, T: Ord>(v: BTreeSet<'arena, T>, w: BTreeSet<'arena, T>) {
        let _ = v.max(w);
    }
    fn clamp<'arena, T: Ord>(
        v: BTreeSet<'arena, T>,
        w: BTreeSet<'arena, T>,
        x: BTreeSet<'arena, T>,
    ) {
        let _ = v.clamp(w, x);
    }
    fn partial_cmp<'arena, T: PartialOrd>(v: &BTreeSet<'arena, T>) {
        let _ = v.partial_cmp(&v);
    }
}

#[test]
fn test_ord_absence() {
    fn set<'arena, K>(mut set: BTreeSet<'arena, K>) {
        let _ = set.is_empty();
        let _ = set.len();
        set.clear();
        let _ = set.iter();
        let _ = set.into_iter();
    }

    fn set_debug<'arena, K: Debug>(set: BTreeSet<'arena, K>) {
        format!("{set:?}");
        format!("{:?}", set.iter());
        format!("{:?}", set.into_iter());
    }

    fn set_clone<'arena, K: Clone>(mut set: BTreeSet<'arena, K>) {
        set.clone_from(&set.clone());
    }

    #[derive(Debug, Clone)]
    struct NonOrd;
    let arena = SetArena::new();
    set(BTreeSet::<NonOrd>::new(&arena));
    set_debug(BTreeSet::<NonOrd>::new(&arena));
    set_clone(BTreeSet::<NonOrd>::new(&arena));
}

#[test]
fn test_append() {
    let arena = SetArena::new();
    let mut a = BTreeSet::new(&arena);
    a.insert(1);
    a.insert(2);
    a.insert(3);

    let mut b = BTreeSet::new(&arena);
    b.insert(3);
    b.insert(4);
    b.insert(5);

    a.append(&mut b);

    assert_eq!(a.len(), 5);
    assert_eq!(b.len(), 0);

    assert_eq!(a.contains(&1), true);
    assert_eq!(a.contains(&2), true);
    assert_eq!(a.contains(&3), true);
    assert_eq!(a.contains(&4), true);
    assert_eq!(a.contains(&5), true);
}

// Unlike the function with the same name in map/tests, returns no values.
// Which also means it returns different predetermined pseudo-random keys,
// and the test cases using this function explore slightly different trees.
fn rand_data(len: usize) -> Vec<u32> {
    let mut rng = DeterministicRng::new();
    Vec::from_iter((0..len).map(|_| rng.next()))
}

#[test]
fn from_array() {
    let arena = SetArena::new();
    let set = BTreeSet::from_iter(&arena, [1, 2, 3, 4]);
    let unordered_duplicates = BTreeSet::from_iter(&arena, [4, 1, 4, 3, 2]);
    assert_eq!(set, unordered_duplicates);
}

#[should_panic(expected = "range start is greater than range end in BTree{Set,Map}")]
#[test]
fn test_range_panic_1() {
    let arena = SetArena::new();
    let mut set = BTreeSet::new(&arena);
    set.insert(3);
    set.insert(5);
    set.insert(8);

    let _invalid_range = set.range((Included(&8), Included(&3)));
}

#[should_panic(expected = "range start and end are equal and excluded in BTree{Set,Map}")]
#[test]
fn test_range_panic_2() {
    let arena = SetArena::new();
    let mut set = BTreeSet::new(&arena);
    set.insert(3);
    set.insert(5);
    set.insert(8);

    let _invalid_range = set.range((Excluded(&5), Excluded(&5)));
}
