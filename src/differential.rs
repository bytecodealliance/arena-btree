use crate::{Arena, BTreeMap as ArenaBTreeMap, BTreeSet as ArenaBTreeSet};
use arbitrary::Arbitrary;
use std::{
    collections::{BTreeMap as StdBTreeMap, BTreeSet as StdBTreeSet, HashSet},
    error::Error,
    mem,
    ops::{Bound, Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive},
};

#[derive(Arbitrary, Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key(u8);

#[derive(Arbitrary, Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Value(u8);

#[derive(Arbitrary, Clone, Debug)]
pub enum MapOperation {
    // Append {
    //     other_map: Vec<(Key, Value)>,
    // },
    Clear,
    ContainsKey {
        key: Key,
    },
    Get {
        key: Key,
    },
    GetKeyValue {
        key: Key,
    },
    IntoKeys,
    IntoValues,
    IsEmpty,
    Iter,
    IterMut {
        new_values: Vec<Value>,
    },
    Keys,
    Len,
    Range {
        bounds: RangeBounds,
    },
    RangeMut {
        bounds: RangeBounds,
        new_values: Vec<Value>,
    },
    Remove {
        key: Key,
    },
    RemoveEntry {
        key: Key,
    },
    Retain {
        predicate: Predicate,
    },
    Values,
    ValuesMut {
        new_values: Vec<Value>,
    },
}

#[derive(Arbitrary, Clone, Debug)]
pub enum RangeBounds {
    Range(Range<Key>),
    RangeFrom(RangeFrom<Key>),
    RangeTo(RangeTo<Key>),
    RangeInclusive(RangeInclusive<Key>),
    RangeToInclusive(RangeToInclusive<Key>),
    Bounds(Bound<Key>, Bound<Key>),
}

#[derive(Arbitrary, Clone, Debug)]
pub enum Predicate {
    Evens,
    Odds,
    Member(HashSet<Key>),
    NotMember(HashSet<Key>),
}

impl Predicate {
    fn into_fn(self) -> Box<dyn FnMut(&Key, &mut Value) -> bool> {
        match self {
            Self::Evens => Box::new(|_, v| v.0 % 2 == 0),
            Self::Odds => Box::new(|_, v| v.0 % 2 == 1),
            Self::Member(keys) => Box::new(move |k, _| keys.contains(k)),
            Self::NotMember(keys) => Box::new(move |k, _| !keys.contains(k)),
        }
    }
}

fn assert_std_arena_maps_equal(
    arena: &Arena<Key, Value>,
    std_map: &StdBTreeMap<Key, Value>,
    arena_map: &ArenaBTreeMap<Key, Value>,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let mut std_entries = std_map.iter().peekable();
    let mut arena_entries = arena_map.iter(arena).peekable();
    let mut errors = vec![];

    loop {
        match (std_entries.peek(), arena_entries.peek()) {
            (None, None) => break,
            (Some((std_key, std_val)), Some((arena_key, arena_val))) => {
                if std_key == arena_key {
                    let (std_key, std_val) = std_entries.next().unwrap();
                    let (arena_key, arena_val) = arena_entries.next().unwrap();
                    if std_val == arena_val {
                        continue;
                    } else {
                        errors.push(format!(
                            "std map and arena map disagree on value for key {std_key:?}: std's \
                             value is {std_val:?} but arena's value is {arena_val:?}"
                        ));
                    }
                } else if std_key < arena_key {
                    let (std_key, std_val) = std_entries.next().unwrap();
                    errors.push(format!(
                        "arena map is missing entry that std map has: {std_key:?} -> {std_val:?}"
                    ));
                } else {
                    let (arena_key, arena_val) = arena_entries.next().unwrap();
                    errors.push(format!(
                        "arena map has extra entry that std map doesn't have: {arena_key:?} -> {arena_val:?}"
                    ));
                }
            }
            (Some((std_key, std_val)), None) => {
                let (std_key, std_val) = std_entries.next().unwrap();
                errors.push(format!(
                    "arena map is missing entry that std map has: {std_key:?} -> {std_val:?}"
                ));
            }
            (None, Some((arena_key, arena_val))) => {
                let (arena_key, arena_val) = arena_entries.next().unwrap();
                errors.push(format!(
                "arena map has extra entry that std map doesn't have: {arena_key:?} -> {arena_val:?}"
            ));
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "Found {} differential error(s)!\n\n* {}",
            errors.len(),
            errors.join("\n* ")
        )
        .into())
    }
}

macro_rules! ensure_eq {
    ($lhs:expr, $rhs:expr) => {
        let lhs = &$lhs;
        let rhs = &$rhs;
        if lhs != rhs {
            let file = file!();
            let line = line!();
            let column = column!();
            return Err(format!(
                "{file}:{line}:{column}: error: `{}` is not equal to `{}`: {lhs:?} != {rhs:?}",
                stringify!($lhs),
                stringify!($rhs)
            )
            .into());
        }
    };
}

pub fn differential_test_map(
    initial_map: Vec<(Key, Value)>,
    operations: Vec<MapOperation>,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    use MapOperation::*;

    let mut std_map = StdBTreeMap::from_iter(initial_map.iter().cloned());
    let mut arena = Arena::new();
    let mut arena_map = ArenaBTreeMap::from_iter(&mut arena, initial_map);
    assert_std_arena_maps_equal(&arena, &std_map, &arena_map)?;

    for op in operations {
        match op {
            // Append { other_map } => {
            //     std_map.append(&mut other_map.iter().cloned().collect::<StdBTreeMap<_, _>>());
            //     arena_map.append(&mut other_map.into_iter().collect::<ArenaBTreeMap<_, _>>());
            // }
            Clear => {
                std_map.clear();
                arena_map.clear(&mut arena);
            }
            ContainsKey { key } => {
                ensure_eq!(
                    std_map.contains_key(&key),
                    arena_map.contains_key(&arena, &key)
                );
            }
            Get { key } => {
                ensure_eq!(std_map.get(&key), arena_map.get(&arena, &key));
            }
            GetKeyValue { key } => {
                ensure_eq!(std_map.get(&key), arena_map.get(&arena, &key));
            }
            IntoKeys => {
                let std_keys = mem::take(&mut std_map).into_keys().collect::<Vec<_>>();
                let arena_keys = mem::replace(&mut arena_map, ArenaBTreeMap::new(&arena))
                    .into_keys(&mut arena)
                    .collect::<Vec<_>>();
                ensure_eq!(std_keys, arena_keys);
            }
            IntoValues => {
                let std_values = mem::take(&mut std_map).into_values().collect::<Vec<_>>();
                let arena_values = mem::replace(&mut arena_map, ArenaBTreeMap::new(&arena))
                    .into_values(&mut arena)
                    .collect::<Vec<_>>();
                ensure_eq!(std_values, arena_values);
            }
            IsEmpty => {
                ensure_eq!(std_map.is_empty(), arena_map.is_empty());
            }
            Iter => {
                let std_entries = std_map.iter().collect::<Vec<_>>();
                let arena_entries = arena_map.iter(&arena).collect::<Vec<_>>();
                ensure_eq!(std_entries, arena_entries);
            }
            IterMut { new_values } => {
                let mut new_values = new_values.into_iter();
                let mut std_entries = std_map.iter_mut();
                let mut arena_entries = arena_map.iter_mut(&mut arena);
                for ((std_key, std_val), (arena_key, arena_val)) in
                    std_entries.by_ref().zip(arena_entries.by_ref())
                {
                    ensure_eq!(std_key, arena_key);
                    ensure_eq!(std_val, arena_val);
                    if let Some(new_val) = new_values.next() {
                        *std_val = new_val;
                        *arena_val = new_val;
                    }
                }
                ensure_eq!(std_entries.next(), arena_entries.next());
            }
            Keys => {
                let std_keys = std_map.keys().collect::<Vec<_>>();
                let arena_keys = arena_map.keys(&arena).collect::<Vec<_>>();
                ensure_eq!(std_keys, arena_keys);
            }
            Len => {
                ensure_eq!(std_map.len(), arena_map.len());
            }
            Range { bounds } => {
                let (std_range, arena_range) = match bounds {
                    RangeBounds::Range(r) => (std_map.range(r.clone()), arena_map.range(&arena, r)),
                    RangeBounds::RangeFrom(r) => {
                        (std_map.range(r.clone()), arena_map.range(&arena, r))
                    }
                    RangeBounds::RangeTo(r) => {
                        (std_map.range(r.clone()), arena_map.range(&arena, r))
                    }
                    RangeBounds::RangeInclusive(r) => {
                        (std_map.range(r.clone()), arena_map.range(&arena, r))
                    }
                    RangeBounds::RangeToInclusive(r) => {
                        (std_map.range(r.clone()), arena_map.range(&arena, r))
                    }
                    RangeBounds::Bounds(mut from, mut to) => {
                        match (&mut from, &mut to) {
                            (
                                Bound::Included(from) | Bound::Excluded(from),
                                Bound::Included(to) | Bound::Excluded(to),
                            ) => {
                                if from == to {
                                    continue;
                                } else if from > to {
                                    mem::swap(from, to);
                                }
                            }
                            _ => {}
                        }
                        (
                            std_map.range((from, to)),
                            arena_map.range(&arena, (from, to)),
                        )
                    }
                };
                let std_range = std_range.collect::<Vec<_>>();
                let arena_range = arena_range.collect::<Vec<_>>();
                ensure_eq!(std_range, arena_range);
            }
            RangeMut { bounds, new_values } => {
                let (mut std_range, mut arena_range) = match bounds {
                    RangeBounds::Range(r) => {
                        (std_map.range_mut(r.clone()), arena_map.range_mut(&arena, r))
                    }
                    RangeBounds::RangeFrom(r) => {
                        (std_map.range_mut(r.clone()), arena_map.range_mut(&arena, r))
                    }
                    RangeBounds::RangeTo(r) => {
                        (std_map.range_mut(r.clone()), arena_map.range_mut(&arena, r))
                    }
                    RangeBounds::RangeInclusive(r) => {
                        (std_map.range_mut(r.clone()), arena_map.range_mut(&arena, r))
                    }
                    RangeBounds::RangeToInclusive(r) => {
                        (std_map.range_mut(r.clone()), arena_map.range_mut(&arena, r))
                    }
                    RangeBounds::Bounds(mut from, mut to) => {
                        match (&mut from, &mut to) {
                            (
                                Bound::Included(from) | Bound::Excluded(from),
                                Bound::Included(to) | Bound::Excluded(to),
                            ) => {
                                if from == to {
                                    continue;
                                } else if from > to {
                                    mem::swap(from, to);
                                }
                            }
                            _ => {}
                        }
                        (
                            std_map.range_mut((from, to)),
                            arena_map.range_mut(&arena, (from, to)),
                        )
                    }
                };
                let mut new_values = new_values.into_iter();
                for ((std_key, std_val), (arena_key, arena_val)) in
                    std_range.by_ref().zip(arena_range.by_ref())
                {
                    ensure_eq!(std_key, arena_key);
                    ensure_eq!(std_val, arena_val);
                    if let Some(new_val) = new_values.next() {
                        *std_val = new_val;
                        *arena_val = new_val;
                    }
                }
            }
            Remove { key } => {
                ensure_eq!(std_map.remove(&key), arena_map.remove(&mut arena, &key));
            }
            RemoveEntry { key } => {
                ensure_eq!(
                    std_map.remove_entry(&key),
                    arena_map.remove_entry(&mut arena, &key)
                );
            }
            Retain { predicate } => {
                let mut predicate = predicate.into_fn();
                std_map.retain(&mut predicate);
                arena_map.retain(&mut arena, &mut predicate);
            }
            Values => {
                let std_values = std_map.values().collect::<Vec<_>>();
                let arena_values = arena_map.values(&arena).collect::<Vec<_>>();
                ensure_eq!(std_values, arena_values);
            }
            ValuesMut { new_values } => {
                let mut new_values = new_values.into_iter();
                let mut std_values = std_map.values_mut();
                let mut arena_values = arena_map.values_mut(&arena);
                for (std_val, arena_val) in std_values.by_ref().zip(arena_values.by_ref()) {
                    ensure_eq!(std_val, arena_val);
                    if let Some(new_val) = new_values.next() {
                        *std_val = new_val;
                        *arena_val = new_val;
                    }
                }
                ensure_eq!(std_values.next(), arena_values.next());
            }
        }
        assert_std_arena_maps_equal(&arena, &std_map, &arena_map)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use arbitrary::Unstructured;
    use rand::prelude::*;

    #[test]
    fn differential_map() -> Result<(), Box<dyn Error + Send + Sync>> {
        let mut buf = vec![];
        let mut rng = rand::thread_rng();

        for input_size in vec![2, 8, 32, 128, 512, 2048] {
            for _ in 0..2_000 {
                buf.resize(input_size, 0);
                rng.fill(&mut buf[..]);

                let mut u = Unstructured::new(&buf);

                let initial_map = match Vec::<(Key, Value)>::arbitrary(&mut u) {
                    Ok(x) => x,
                    Err(_) => continue,
                };

                let operations = match Vec::<MapOperation>::arbitrary_take_rest(u) {
                    Ok(x) => x,
                    Err(_) => continue,
                };

                differential_test_map(initial_map, operations)?;
            }
        }

        Ok(())
    }

    #[test]
    fn arena_map_has_extra_trailing_entry() {
        let std_map = vec![(Key(5), Value(10))].into_iter().collect();
        let mut arena = Arena::new();
        let arena_map =
            ArenaBTreeMap::from_iter(&mut arena, [(Key(5), Value(10)), (Key(7), Value(14))]);
        let err = assert_std_arena_maps_equal(&arena, &std_map, &arena_map).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Found 1 differential error(s)!\n\n* arena map has extra entry that std map doesn't have: Key(7) -> Value(14)"
        );
    }

    #[test]
    fn arena_map_has_extra_preceding_entry() {
        let std_map = vec![(Key(5), Value(10))].into_iter().collect();
        let mut arena = Arena::new();
        let arena_map =
            ArenaBTreeMap::from_iter(&mut arena, [(Key(3), Value(6)), (Key(5), Value(10))]);
        let err = assert_std_arena_maps_equal(&arena, &std_map, &arena_map).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Found 1 differential error(s)!\n\n* arena map has extra entry that std map doesn't have: Key(3) -> Value(6)"
        );
    }

    #[test]
    fn arena_map_has_missing_trailing_entry() {
        let std_map = vec![(Key(5), Value(10)), (Key(7), Value(14))]
            .into_iter()
            .collect();
        let mut arena = Arena::new();
        let arena_map = ArenaBTreeMap::from_iter(&mut arena, [(Key(5), Value(10))]);
        let err = assert_std_arena_maps_equal(&arena, &std_map, &arena_map).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Found 1 differential error(s)!\n\n* arena map is missing entry that std map has: Key(7) -> Value(14)"
        );
    }

    #[test]
    fn arena_map_has_missing_preceding_entry() {
        let std_map = vec![(Key(3), Value(6)), (Key(5), Value(10))]
            .into_iter()
            .collect();
        let mut arena = Arena::new();
        let arena_map = ArenaBTreeMap::from_iter(&mut arena, [(Key(5), Value(10))]);
        let err = assert_std_arena_maps_equal(&arena, &std_map, &arena_map).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Found 1 differential error(s)!\n\n* arena map is missing entry that std map has: Key(3) -> Value(6)"
        );
    }

    #[test]
    fn maps_equal() {
        let std_map = vec![(Key(3), Value(6)), (Key(5), Value(10)), (Key(7), Value(14))]
            .into_iter()
            .collect();
        let mut arena = Arena::new();
        let arena_map = ArenaBTreeMap::from_iter(
            &mut arena,
            [(Key(3), Value(6)), (Key(5), Value(10)), (Key(7), Value(14))],
        );
        assert_std_arena_maps_equal(&arena, &std_map, &arena_map).unwrap();
    }

    #[test]
    fn multiple_differences() {
        let std_map = vec![
            (Key(3), Value(6)),
            (Key(5), Value(10)),
            (Key(100), Value(200)),
        ]
        .into_iter()
        .collect();
        let mut arena = Arena::new();
        let arena_map = ArenaBTreeMap::from_iter(
            &mut arena,
            [
                (Key(5), Value(10)),
                (Key(7), Value(14)),
                (Key(100), Value(200)),
            ],
        );
        let err = assert_std_arena_maps_equal(&arena, &std_map, &arena_map).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Found 2 differential error(s)!\n\n\
             * arena map is missing entry that std map has: Key(3) -> Value(6)\n\
             * arena map has extra entry that std map doesn't have: Key(7) -> Value(14)"
        );
    }
}
