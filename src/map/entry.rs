use core::fmt::{self, Debug};
use core::marker::PhantomData;
use core::mem;

use crate::alloc::Arena;

use super::super::borrow::DormantMutRef;
use super::super::node::{marker, Handle, NodeRef};
use super::BTreeMap;

use Entry::*;

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`BTreeMap`].
///
/// [`entry`]: BTreeMap::entry
pub enum Entry<'a, 'arena, K: 'a + 'arena, V: 'a + 'arena> {
    /// A vacant entry.
    Vacant(VacantEntry<'a, 'arena, K, V>),

    /// An occupied entry.
    Occupied(OccupiedEntry<'a, 'arena, K, V>),
}

impl<K: Debug + Ord, V: Debug> Debug for Entry<'_, '_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

/// A view into a vacant entry in a `BTreeMap`.
/// It is part of the [`Entry`] enum.

pub struct VacantEntry<'a, 'arena, K, V> {
    pub(super) key: K,
    /// `None` for a (empty) map without root
    pub(super) handle: Option<Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge>>,
    pub(super) dormant_map: DormantMutRef<'a, BTreeMap<'arena, K, V>>,
    pub(super) arena: &'arena Arena<K, V>,

    // Be invariant in `K` and `V`
    pub(super) _marker: PhantomData<&'a mut (K, V)>,
}

impl<K: Debug + Ord, V> Debug for VacantEntry<'_, '_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

/// A view into an occupied entry in a `BTreeMap`.
/// It is part of the [`Entry`] enum.

pub struct OccupiedEntry<'a, 'arena, K, V> {
    pub(super) handle: Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::KV>,
    pub(super) dormant_map: DormantMutRef<'a, BTreeMap<'arena, K, V>>,
    pub(super) arena: &'arena Arena<K, V>,

    // Be invariant in `K` and `V`
    pub(super) _marker: PhantomData<&'a mut (K, V)>,
}

impl<K: Debug + Ord, V: Debug> Debug for OccupiedEntry<'_, '_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<'a, 'arena, K: Ord, V> Entry<'a, 'arena, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, String> = BTreeMap::new(&arena);
    /// let s = "hoho".to_string();
    ///
    /// map.entry("poneyland").or_insert_with(|| s);
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    ///
    /// map.entry("poneyland").or_insert_with_key(|key| key.chars().count());
    ///
    /// assert_eq!(map["poneyland"], 9);
    /// ```
    #[inline]
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Occupied(mut entry) => {
                f(entry.get_mut());
                Occupied(entry)
            }
            Vacant(entry) => Vacant(entry),
        }
    }
}

impl<'a, 'arena, K: Ord, V: Default> Entry<'a, 'arena, K, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, Option<usize>> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// ```
    pub fn or_default(self) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<'a, 'arena, K: Ord, V> VacantEntry<'a, 'arena, K, V> {
    /// Gets a reference to the key that would be used when inserting a value
    /// through the VacantEntry.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, u32> = BTreeMap::new(&arena);
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    pub fn insert(mut self, value: V) -> &'a mut V {
        let out_ptr = match self.handle {
            None => {
                // SAFETY: There is no tree yet so no reference to it exists.
                let map = unsafe { self.dormant_map.awaken() };
                let mut root = NodeRef::new_leaf(&mut self.arena);
                let val_ptr = root.borrow_mut().push(self.key, value) as *mut V;
                map.root = Some(root.forget_type());
                map.length = 1;
                val_ptr
            }
            Some(handle) => match handle.insert_recursing(self.key, value, &mut self.arena) {
                (None, val_ptr) => {
                    // SAFETY: We have consumed self.handle.
                    let map = unsafe { self.dormant_map.awaken() };
                    map.length += 1;
                    val_ptr
                }
                (Some(ins), val_ptr) => {
                    drop(ins.left);
                    // SAFETY: We have consumed self.handle and dropped the
                    // remaining reference to the tree, ins.left.
                    let map = unsafe { self.dormant_map.awaken() };
                    let root = map.root.as_mut().unwrap(); // same as ins.left
                    root.push_internal_level(self.arena)
                        .push(ins.kv.0, ins.kv.1, ins.right);
                    map.length += 1;
                    val_ptr
                }
            },
        };
        // Now that we have finished growing the tree using borrowed references,
        // dereference the pointer to a part of it, that we picked up along the way.
        unsafe { &mut *out_ptr }
    }
}

impl<'a, 'arena, K: Ord, V> OccupiedEntry<'a, 'arena, K, V> {
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[must_use]
    pub fn key(&self) -> &K {
        self.handle.reborrow().into_kv().0
    }

    /// Take ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// // If now try to get the value, it will panic:
    /// // println!("{}", map["poneyland"]);
    /// ```
    pub fn remove_entry(self) -> (K, V) {
        self.remove_kv()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    #[must_use]
    pub fn get(&self) -> &V {
        self.handle.reborrow().into_kv().1
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` that may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: OccupiedEntry::into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    pub fn get_mut(&mut self) -> &mut V {
        self.handle.kv_mut().1
    }

    /// Converts the entry into a mutable reference to its value.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: OccupiedEntry::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_mut(self) -> &'a mut V {
        self.handle.into_val_mut()
    }

    /// Sets the value of the entry with the `OccupiedEntry`'s key,
    /// and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Takes the value of the entry out of the map, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap, map::Entry};
    ///
    /// let arena = Arena::new();
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    /// // If we try to get "poneyland"'s value, it'll panic:
    /// // println!("{}", map["poneyland"]);
    /// ```
    pub fn remove(self) -> V {
        self.remove_kv().1
    }

    // Body of `remove_entry`, probably separate because the name reflects the returned pair.
    pub(super) fn remove_kv(mut self) -> (K, V) {
        let mut emptied_internal_root = false;
        let (old_kv, _) = self
            .handle
            .remove_kv_tracking(|_alloc| emptied_internal_root = true, self.arena);
        // SAFETY: we consumed the intermediate root borrow, `self.handle`.
        let map = unsafe { self.dormant_map.awaken() };
        map.length -= 1;
        if emptied_internal_root {
            let root = map.root.as_mut().unwrap();
            root.pop_internal_level(self.arena);
        }
        old_kv
    }
}
