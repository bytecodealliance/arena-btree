use super::borrow::DormantMutRef;
use super::dedup_sorted_iter::DedupSortedIter;
use super::navigate::{LazyLeafRange, LeafRange};
use super::node::{self, marker, ForceResult::*, Handle, NodeRef, Root};
use super::search::SearchResult::*;
use super::set_val::SetValZST;
use crate::arena::Arena;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::{self, Debug};
use core::hash::{Hash, Hasher};
use core::iter::{FromIterator, FusedIterator};
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop};
use core::ops::{Index, RangeBounds};
use core::ptr;

mod entry;
pub use entry::{Entry, OccupiedEntry, VacantEntry};

use Entry::*;

/// Minimum number of elements in a node that is not a root.
/// We might temporarily have fewer elements during methods.
pub(super) const MIN_LEN: usize = node::MIN_LEN_AFTER_SPLIT;

// A tree in a `BTreeMap` is a tree in the `node` module with additional invariants:
// - Keys must appear in ascending order (according to the key's type).
// - Every non-leaf node contains at least 1 element (has at least 2 children).
// - Every non-root node contains at least MIN_LEN elements.
//
// An empty map is represented either by the absence of a root node or by a
// root node that is an empty leaf.

/// An ordered map based on a [B-Tree].
///
/// B-Trees represent a fundamental compromise between cache-efficiency and actually minimizing
/// the amount of work performed in a search. In theory, a binary search tree (BST) is the optimal
/// choice for a sorted map, as a perfectly balanced BST performs the theoretical minimum amount of
/// comparisons necessary to find an element (log<sub>2</sub>n). However, in practice the way this
/// is done is *very* inefficient for modern computer architectures. In particular, every element
/// is stored in its own individually heap-allocated node. This means that every single insertion
/// triggers a heap-allocation, and every single comparison should be a cache-miss. Since these
/// are both notably expensive things to do in practice, we are forced to at very least reconsider
/// the BST strategy.
///
/// A B-Tree instead makes each node contain B-1 to 2B-1 elements in a contiguous array. By doing
/// this, we reduce the number of allocations by a factor of B, and improve cache efficiency in
/// searches. However, this does mean that searches will have to do *more* comparisons on average.
/// The precise number of comparisons depends on the node search strategy used. For optimal cache
/// efficiency, one could search the nodes linearly. For optimal comparisons, one could search
/// the node using binary search. As a compromise, one could also perform a linear search
/// that initially only checks every i<sup>th</sup> element for some choice of i.
///
/// Currently, our implementation simply performs naive linear search. This provides excellent
/// performance on *small* nodes of elements which are cheap to compare. However in the future we
/// would like to further explore choosing the optimal search strategy based on the choice of B,
/// and possibly other factors. Using linear search, searching for a random element is expected
/// to take B * log(n) comparisons, which is generally worse than a BST. In practice,
/// however, performance is excellent.
///
/// It is a logic error for a key to be modified in such a way that the key's ordering relative to
/// any other key, as determined by the [`Ord`] trait, changes while it is in the map. This is
/// normally only possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
/// The behavior resulting from such a logic error is not specified, but will be encapsulated to the
/// `BTreeMap` that observed the logic error and not result in undefined behavior. This could
/// include panics, incorrect results, aborts, memory leaks, and non-termination.
///
/// Iterators obtained from functions such as [`BTreeMap::iter`], [`BTreeMap::values`], or
/// [`BTreeMap::keys`] produce their items in order by key, and take worst-case logarithmic and
/// amortized constant time per item returned.
///
/// [B-Tree]: https://en.wikipedia.org/wiki/B-tree
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
///
/// # Examples
///
/// ```
/// use arena_btree::{Arena, BTreeMap};
///
/// // type inference lets us omit an explicit type signature (which
/// // would be `BTreeMap<&str, &str>` in this example).
/// let mut arena = Arena::new();
/// let mut movie_reviews = BTreeMap::new(&arena);
///
/// // review some movies.
/// movie_reviews.insert(&mut arena, "Office Space",       "Deals with real issues in the workplace.");
/// movie_reviews.insert(&mut arena, "Pulp Fiction",       "Masterpiece.");
/// movie_reviews.insert(&mut arena, "The Godfather",      "Very enjoyable.");
/// movie_reviews.insert(&mut arena, "The Blues Brothers", "Eye lyked it a lot.");
///
/// // check for a specific one.
/// if !movie_reviews.contains_key(&arena, "Les Misérables") {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              movie_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// movie_reviews.remove(&mut arena, "The Blues Brothers");
///
/// // look up the values associated with some keys.
/// let to_find = ["Up!", "Office Space"];
/// for movie in &to_find {
///     match movie_reviews.get(&arena, movie) {
///        Some(review) => println!("{movie}: {review}"),
///        None => println!("{movie} is unreviewed.")
///     }
/// }
///
/// // iterate over everything.
/// for (movie, review) in movie_reviews.iter(&arena) {
///     println!("{movie}: \"{review}\"");
/// }
///
/// // Drop the map entries and return them to the arena's free list.
/// movie_reviews.drop(&mut arena);
/// ```
///
/// A `BTreeMap` with a known list of items can be initialized from an array:
///
/// ```
/// use arena_btree::{Arena, BTreeMap};
///
/// let mut arena = Arena::new();
/// let solar_distance = BTreeMap::from_iter(
///     &mut arena,
///     [
///         ("Mercury", 0.4),
///         ("Venus", 0.7),
///         ("Earth", 1.0),
///         ("Mars", 1.5),
///     ]
/// );
///
/// // Drop the map entries and return them to the arena's free list.
/// solar_distance.drop(&mut arena);
/// ```
///
/// `BTreeMap` implements an [`Entry API`], which allows for complex
/// methods of getting, setting, updating and removing keys and their values:
///
/// [`Entry API`]: BTreeMap::entry
///
/// ```
/// use arena_btree::{Arena, BTreeMap};
///
/// // type inference lets us omit an explicit type signature (which
/// // would be `BTreeMap<&str, u8>` in this example).
/// let mut arena = Arena::new();
/// let mut player_stats = BTreeMap::new(&arena);
///
/// fn random_stat_buff() -> u8 {
///     // could actually return some random value here - let's just return
///     // some fixed value for now
///     42
/// }
///
/// // insert a key only if it doesn't already exist
/// player_stats.entry(&mut arena, "health").or_insert(100);
///
/// // insert a key using a function that provides a new value only if it
/// // doesn't already exist
/// player_stats.entry(&mut arena, "defence").or_insert_with(random_stat_buff);
///
/// // update a key, guarding against the key possibly not being set
/// let stat = player_stats.entry(&mut arena, "attack").or_insert(100);
/// *stat += random_stat_buff();
///
/// // modify an entry before an insert with in-place mutation
/// player_stats.entry(&mut arena, "mana").and_modify(|mana| *mana += 200).or_insert(100);
///
/// // Drop the map entries and return them to the arena's free list.
/// player_stats.drop(&mut arena);
/// ```
///
/// Because the entries in the map live in an external arena, dropping the map
/// does not drop the entries or return their slots to the arena's free
/// list. You must manually call [`my_map.drop(&mut
/// arena)`][crate::BTreeMap::drop] to drop the entries and return them to the
/// arena's free list. See the documentation for
/// [`BTreeMap::drop`][crate::BTreeMap::drop] for more details.
///
/// ```
/// use arena_btree::{Arena, BTreeMap};
///
/// let mut arena = Arena::new();
/// let mut map = BTreeMap::new(&arena);
///
/// map.insert(&mut arena, "a", vec![1, 2, 3]);
/// map.insert(&mut arena, "b", vec![4, 5, 6]);
/// map.insert(&mut arena, "c", vec![7, 8, 9]);
///
/// // Free the heap allocations associated with each `Vec` value and return
/// // the entry slots to the arena's free list.
/// map.drop(&mut arena);
/// ```
///
/// Finally, using a `BTreeMap` with the wrong arena will panic:
///
/// ```should_panic
/// use arena_btree::{Arena, BTreeMap};
///
/// let mut a = Arena::new();
/// let mut b = Arena::new();
///
/// // Create a map associated with arena `a`.
/// let mut map = BTreeMap::new(&a);
///
/// // Inserting with `a` works fine.
/// map.insert(&mut a, "okay", 1);
///
/// // But trying to insert with `b` will panic!
/// map.insert(&mut b, "uh oh!", 2);
/// ```
pub struct BTreeMap<K, V> {
    root: Option<Root<K, V>>,
    length: usize,

    // The id of the arena that this map's nodes are stored in. Public APIs must
    // assert that the given arena's id matches this id, and from then on can
    // use unchecked indexing into the arena, knowing that it has the
    // appropriate length.
    arena_id: usize,

    #[cfg(debug_assertions)]
    dropped: bool,

    // For dropck; the `Box` avoids making the `Unpin` impl more strict than before
    _marker: PhantomData<Box<(K, V)>>,
}

// FIXME: This implementation is "wrong", but changing it would be a breaking change.
// (The bounds of the automatic `UnwindSafe` implementation have been like this since Rust 1.50.)
// Maybe we can fix it nonetheless with a crater run, or if the `UnwindSafe`
// traits are deprecated, or disarmed (no longer causing hard errors) in the future.

impl<K, V> core::panic::UnwindSafe for BTreeMap<K, V>
where
    K: core::panic::RefUnwindSafe,
    V: core::panic::RefUnwindSafe,
{
}

impl<K: Clone, V: Clone> BTreeMap<K, V> {
    /// TODO FITZGEN
    pub fn clone(&self, arena: &mut Arena<K, V>) -> BTreeMap<K, V> {
        assert_eq!(arena.id(), self.arena_id);

        fn clone_subtree<'a, K: Clone, V: Clone>(
            node: NodeRef<marker::Immut<'a>, K, V, marker::LeafOrInternal>,
            arena: &mut Arena<K, V>,
        ) -> BTreeMap<K, V>
        where
            K: 'a,
            V: 'a,
        {
            // Guard to ensure we run `Drop`s on the tree elements if cloning
            // panics.
            struct Guard<'a, K, V>(&'a mut Arena<K, V>, ManuallyDrop<BTreeMap<K, V>>);
            impl<'a, K, V> Drop for Guard<'a, K, V> {
                fn drop(&mut self) {
                    unsafe {
                        let tree = std::ptr::read(&mut *self.1);
                        tree.drop(self.0);
                    }
                }
            }
            impl<'a, K, V> Guard<'a, K, V> {
                fn finish(mut self) -> BTreeMap<K, V> {
                    unsafe {
                        let tree = std::ptr::read(&mut *self.1);
                        mem::forget(self);
                        tree
                    }
                }
            }

            match node.force() {
                Leaf(leaf) => {
                    let out_tree = BTreeMap {
                        root: Some(Root::new(arena)),
                        length: 0,
                        arena_id: arena.id(),
                        _marker: PhantomData,
                        #[cfg(debug_assertions)]
                        dropped: false,
                    };
                    let mut out_tree = Guard(arena, ManuallyDrop::new(out_tree));

                    {
                        let mut in_edge = leaf.first_edge(out_tree.0);
                        while let Ok(kv) = in_edge.right_kv(out_tree.0) {
                            let (k, v) = kv.into_kv(out_tree.0);
                            in_edge = kv.right_edge(out_tree.0);

                            {
                                let root = out_tree.1.root.as_mut().unwrap(); // unwrap succeeds because we just wrapped
                                let mut out_node = match root.borrow_mut().force() {
                                    Leaf(leaf) => leaf,
                                    Internal(_) => unreachable!(),
                                };
                                out_node.push(k.clone(), v.clone(), out_tree.0);
                            }
                            out_tree.1.length += 1;
                        }
                    }

                    out_tree.finish()
                }
                Internal(internal) => {
                    let out_tree = clone_subtree(internal.first_edge(&arena).descend(arena), arena);
                    let mut out_tree = Guard(arena, ManuallyDrop::new(out_tree));

                    {
                        let out_root = out_tree.1.root.as_mut().unwrap();
                        let mut out_node = out_root.push_internal_level(out_tree.0);
                        let (out_node_id, out_node_height) = out_node.into_raw_parts();
                        let mut in_edge = internal.first_edge(out_tree.0);
                        while let Ok(kv) = in_edge.right_kv(out_tree.0) {
                            let (k, v) = kv.into_kv(out_tree.0);
                            in_edge = kv.right_edge(out_tree.0);

                            let k = (*k).clone();
                            let v = (*v).clone();
                            let subtree = clone_subtree(in_edge.descend(out_tree.0), out_tree.0);

                            // We can't destructure subtree directly
                            // because BTreeMap implements Drop
                            let (subroot, sublength) = unsafe {
                                let mut subtree = ManuallyDrop::new(subtree);
                                let root = ptr::read(&subtree.root);
                                let length = subtree.length;
                                (root, length)
                            };

                            // Recreate the `out_node` each iteration of the
                            // loop to avoid holding a mutable borrow of
                            // `out_tree.1` across the loop, preventing the
                            // length update below from passing the borrow
                            // checker.
                            let mut out_node: NodeRef<marker::Mut<'_>, K, V, marker::Internal> =
                                unsafe { NodeRef::from_raw_parts(out_node_id, out_node_height) };
                            out_node.push(
                                k,
                                v,
                                subroot.unwrap_or_else(|| Root::new(out_tree.0)),
                                out_tree.0,
                            );
                            out_tree.1.length += 1 + sublength;
                        }
                    }

                    out_tree.finish()
                }
            }
        }

        if self.is_empty() {
            BTreeMap::new(arena)
        } else {
            clone_subtree(
                // unwrap succeeds because not empty
                self.root.as_ref().unwrap().reborrow(),
                arena,
            )
        }
    }
}

impl<Q: ?Sized, K> super::Recover<Q, K, SetValZST> for BTreeMap<K, SetValZST>
where
    K: Borrow<Q> + Ord,
    Q: Ord,
{
    fn get(&self, key: &Q, arena: &Arena<K, SetValZST>) -> Option<&K> {
        let root_node = self.root.as_ref()?.reborrow();
        match root_node.search_tree(key, arena) {
            Found(handle) => Some(handle.into_kv(arena).0),
            GoDown(_) => None,
        }
    }

    fn take(&mut self, key: &Q, arena: &mut Arena<K, SetValZST>) -> Option<K> {
        let (map, dormant_map) = DormantMutRef::new(self);
        let root_node = map.root.as_mut()?.borrow_mut();
        match root_node.search_tree(key, arena) {
            Found(handle) => Some(
                OccupiedEntry {
                    handle,
                    dormant_map,
                    arena,
                    _marker: PhantomData,
                }
                .remove_kv()
                .0,
            ),
            GoDown(_) => None,
        }
    }

    fn replace(&mut self, key: K, arena: &mut Arena<K, SetValZST>) -> Option<K> {
        let (map, dormant_map) = DormantMutRef::new(self);
        let root_node = map
            .root
            .get_or_insert_with(|| Root::new(arena))
            .borrow_mut();
        match root_node.search_tree::<K>(&key, arena) {
            Found(mut kv) => Some(mem::replace(kv.key_mut(arena), key)),
            GoDown(handle) => {
                VacantEntry {
                    key,
                    handle: Some(handle),
                    dormant_map,
                    arena,
                    _marker: PhantomData,
                }
                .insert(SetValZST::default());
                None
            }
        }
    }
}

/// An iterator over the entries of a `BTreeMap`.
///
/// This `struct` is created by the [`iter`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`iter`]: BTreeMap::iter
#[must_use = "iterators are lazy and do nothing unless consumed"]

pub struct Iter<'a, K: 'a, V: 'a> {
    range: LazyLeafRange<marker::Immut<'a>, K, V>,
    length: usize,
    arena: &'a Arena<K, V>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the entries of a `BTreeMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: BTreeMap::iter_mut

pub struct IterMut<'a, K: 'a, V: 'a> {
    range: LazyLeafRange<marker::ValMut<'a>, K, V>,
    length: usize,
    arena: &'a Arena<K, V>,

    // Be invariant in `K` and `V`
    _marker: PhantomData<&'a mut (K, V)>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for IterMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IterMut").finish()
    }
}

/// An owning iterator over the entries of a `BTreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`BTreeMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<'a, K, V> {
    range: LazyLeafRange<marker::Dying, K, V>,
    length: usize,
    arena: &'a mut Arena<K, V>,
}

impl<'a, K, V> Debug for IntoIter<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntoIter").finish()
    }
}

/// An iterator over the keys of a `BTreeMap`.
///
/// This `struct` is created by the [`keys`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`keys`]: BTreeMap::keys
#[must_use = "iterators are lazy and do nothing unless consumed"]

pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<K: fmt::Debug, V> fmt::Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the values of a `BTreeMap`.
///
/// This `struct` is created by the [`values`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`values`]: BTreeMap::values
#[must_use = "iterators are lazy and do nothing unless consumed"]

pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<K, V: fmt::Debug> fmt::Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the values of a `BTreeMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: BTreeMap::values_mut
#[must_use = "iterators are lazy and do nothing unless consumed"]

pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

impl<K, V: fmt::Debug> fmt::Debug for ValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(_, val)| val))
            .finish()
    }
}

/// An owning iterator over the keys of a `BTreeMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`BTreeMap`].
/// See its documentation for more.
///
/// [`into_keys`]: BTreeMap::into_keys
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoKeys<'a, K, V> {
    inner: IntoIter<'a, K, V>,
}

impl<'a, K, V> fmt::Debug for IntoKeys<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntoKeys").finish()
    }
}

/// An owning iterator over the values of a `BTreeMap`.
///
/// This `struct` is created by the [`into_values`] method on [`BTreeMap`].
/// See its documentation for more.
///
/// [`into_values`]: BTreeMap::into_values
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoValues<'a, K, V> {
    inner: IntoIter<'a, K, V>,
}

impl<'a, K, V> fmt::Debug for IntoValues<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntoValues").finish()
    }
}

/// An iterator over a sub-range of entries in a `BTreeMap`.
///
/// This `struct` is created by the [`range`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`range`]: BTreeMap::range
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Range<'a, K: 'a, V: 'a> {
    inner: LeafRange<marker::Immut<'a>, K, V>,
    arena: &'a Arena<K, V>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Range<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over a sub-range of entries in a `BTreeMap`.
///
/// This `struct` is created by the [`range_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`range_mut`]: BTreeMap::range_mut
#[must_use = "iterators are lazy and do nothing unless consumed"]

pub struct RangeMut<'a, K: 'a, V: 'a> {
    inner: LeafRange<marker::ValMut<'a>, K, V>,
    arena: &'a Arena<K, V>,

    // Be invariant in `K` and `V`
    _marker: PhantomData<&'a mut (K, V)>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for RangeMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RangeMut").finish()
    }
}

impl<K, V> BTreeMap<K, V> {
    /// Makes a new, empty `BTreeMap`.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(&mut arena, 1, "a");
    ///
    /// map.drop(&mut arena);
    /// ```
    #[must_use]
    pub fn new(arena: &Arena<K, V>) -> BTreeMap<K, V> {
        BTreeMap {
            root: None,
            length: 0,
            arena_id: arena.id(),
            _marker: PhantomData,
            #[cfg(debug_assertions)]
            dropped: false,
        }
    }

    /// Clears the map, removing all elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// a.insert(&mut arena, 1, "a");
    /// a.clear(&mut arena);
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self, arena: &mut Arena<K, V>) {
        assert_eq!(arena.id(), self.arena_id);
        BTreeMap {
            root: mem::replace(&mut self.root, None),
            length: mem::replace(&mut self.length, 0),
            arena_id: self.arena_id,
            _marker: PhantomData,
            #[cfg(debug_assertions)]
            dropped: false,
        }
        .drop(arena);
    }
}

#[cfg(debug_assertions)]
impl<K, V> Drop for BTreeMap<K, V> {
    fn drop(&mut self) {
        debug_assert!(
            self.dropped || self.is_empty() || std::thread::panicking(),
            "`arena_btree::BTreeMap` will leak entries if you don't explicitly call
             `my_map.drop(&mut arena)`! If you are okay with leaking, then call
             `my_map.forget()` instead."
        );
    }
}

impl<K, V> BTreeMap<K, V> {
    /// Drop the entries in this map and return their slots to the arena's free
    /// list.
    ///
    /// Because the entries live external to this map, in the arena,
    /// `drop(my_map)` cannot call `drop` on each of the map's entries or return
    /// their slots to the arena's free list. Instead you must call this method.
    ///
    /// Failure to call this method will leak any resources that `K` and `V`
    /// manage (such as the underlying heap allocation for a `Vec`) as well as
    /// leak arena slots since the slots won't be returned to the arena's free
    /// list.
    ///
    /// Leaking can be acceptable in some situations, particularly if `K` and
    /// `V` have trivial `Drop` implementations (as determined by
    /// [`std::mem::needs_drop`][std::mem::needs_drop] returning
    /// `false`). Perhaps you do not intend to use the associated arena again
    /// and returning the map's entry slots to the arena's free list is simply
    /// wasted effort? In these scenarios, call
    /// [`my_map.forget()`][crate::BTreeMap::forget] instead of
    /// `my_map.drop(&mut arena)`.
    ///
    /// # Example
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    ///
    /// map.insert(&mut arena, "a", vec![1, 2, 3]);
    /// map.insert(&mut arena, "b", vec![4, 5, 6]);
    /// map.insert(&mut arena, "c", vec![7, 8, 9]);
    ///
    /// // Free the heap allocations associated with each `Vec` value and return
    /// // the entry slots to the arena's free list.
    /// map.drop(&mut arena);
    /// ```
    pub fn drop(mut self, arena: &mut Arena<K, V>) {
        assert_eq!(arena.id(), self.arena_id);

        #[cfg(debug_assertions)]
        {
            self.dropped = true;
        }

        drop(self.into_iter(arena));
    }

    /// Leak this map and its entries' slots in the arena.
    pub fn forget(self) {
        mem::forget(self)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 1, "a");
    /// assert_eq!(map.get(&arena, &1), Some(&"a"));
    /// assert_eq!(map.get(&arena, &2), None);
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn get<Q: ?Sized>(&self, arena: &Arena<K, V>, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        let root_node = self.root.as_ref()?.reborrow();
        match root_node.search_tree(key, arena) {
            Found(handle) => Some(handle.into_kv(arena).1),
            GoDown(_) => None,
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 1, "a");
    /// assert_eq!(map.get_key_value(&arena, &1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&arena, &2), None);
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn get_key_value<Q: ?Sized>(&self, arena: &Arena<K, V>, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        let root_node = self.root.as_ref()?.reborrow();
        match root_node.search_tree(k, arena) {
            Found(handle) => Some(handle.into_kv(arena)),
            GoDown(_) => None,
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 1, "a");
    /// assert_eq!(map.contains_key(&arena, &1), true);
    /// assert_eq!(map.contains_key(&arena, &2), false);
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, arena: &Arena<K, V>, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        self.get(arena, key).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 1, "a");
    /// if let Some(x) = map.get_mut(&arena, &1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.get(&arena, &1), Some(&"b"));
    ///
    /// map.drop(&mut arena);
    /// ```
    // See `get` for implementation notes, this is basically a copy-paste with mut's added
    pub fn get_mut<Q: ?Sized>(&mut self, arena: &Arena<K, V>, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        let root_node = self.root.as_mut()?.borrow_mut();
        match root_node.search_tree(key, arena) {
            Found(handle) => Some(handle.into_val_mut(arena)),
            GoDown(_) => None,
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// assert_eq!(map.insert(&mut arena, 37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(&mut arena, 37, "b");
    /// assert_eq!(map.insert(&mut arena, 37, "c"), Some("b"));
    /// assert_eq!(map.get(&arena, &37), Some(&"c"));
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn insert(&mut self, arena: &mut Arena<K, V>, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        match self.entry(arena, key) {
            Occupied(mut entry) => Some(entry.insert(value)),
            Vacant(entry) => {
                entry.insert(value);
                None
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 1, "a");
    /// assert_eq!(map.remove(&mut arena, &1), Some("a"));
    /// assert_eq!(map.remove(&mut arena, &1), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, arena: &mut Arena<K, V>, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.remove_entry(arena, key).map(|(_, v)| v)
    }

    /// Removes a key from the map, returning the stored key and value if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 1, "a");
    /// assert_eq!(map.remove_entry(&mut arena, &1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&mut arena, &1), None);
    /// ```
    pub fn remove_entry<Q: ?Sized>(&mut self, arena: &mut Arena<K, V>, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        let (map, dormant_map) = DormantMutRef::new(self);
        let root_node = map.root.as_mut()?.borrow_mut();
        match root_node.search_tree(key, arena) {
            Found(handle) => Some(
                OccupiedEntry {
                    handle,
                    dormant_map,
                    arena,
                    _marker: PhantomData,
                }
                .remove_entry(),
            ),
            GoDown(_) => None,
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map: BTreeMap<i32, i32> = BTreeMap::from_iter(&mut arena, (0..8).map(|x| (x, x*10)));
    /// // Keep only the elements with even-numbered keys.
    /// map.retain(&mut arena, |&k, _| k % 2 == 0);
    /// assert!(map.into_iter(&mut arena).eq(vec![(0, 0), (2, 20), (4, 40), (6, 60)]));
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, arena: &mut Arena<K, V>, mut f: F)
    where
        K: Ord,
        F: FnMut(&K, &mut V) -> bool,
    {
        assert_eq!(arena.id(), self.arena_id);
        self.drain_filter(arena, |k, v| !f(k, v));
    }

    pub(crate) fn drain_filter<'a, F>(
        &'a mut self,
        arena: &'a mut Arena<K, V>,
        pred: F,
    ) -> DrainFilter<'a, K, V, F>
    where
        K: Ord,
        F: FnMut(&K, &mut V) -> bool,
    {
        assert_eq!(arena.id(), self.arena_id);
        let inner = self.drain_filter_inner(arena);
        DrainFilter { pred, inner }
    }

    pub(super) fn drain_filter_inner<'a>(
        &'a mut self,
        arena: &'a mut Arena<K, V>,
    ) -> DrainFilterInner<'a, K, V>
    where
        K: Ord,
    {
        if let Some(root) = self.root.as_mut() {
            let (root, dormant_root) = DormantMutRef::new(root);
            let front = root.borrow_mut().first_leaf_edge(arena);
            DrainFilterInner {
                length: &mut self.length,
                dormant_root: Some(dormant_root),
                cur_leaf_edge: Some(front),
                arena,
            }
        } else {
            DrainFilterInner {
                length: &mut self.length,
                dormant_root: None,
                cur_leaf_edge: None,
                arena,
            }
        }
    }

    // /// Moves all elements from `other` into `self`, leaving `other` empty.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// use arena_btree::BTreeMap;
    // ///
    // /// let mut a = BTreeMap::new();
    // /// a.insert(1, "a");
    // /// a.insert(2, "b");
    // /// a.insert(3, "c");
    // ///
    // /// let mut b = BTreeMap::new();
    // /// b.insert(3, "d");
    // /// b.insert(4, "e");
    // /// b.insert(5, "f");
    // ///
    // /// a.append(&mut b);
    // ///
    // /// assert_eq!(a.len(), 5);
    // /// assert_eq!(b.len(), 0);
    // ///
    // /// assert_eq!(a[&1], "a");
    // /// assert_eq!(a[&2], "b");
    // /// assert_eq!(a[&3], "d");
    // /// assert_eq!(a[&4], "e");
    // /// assert_eq!(a[&5], "f");
    // /// ```
    // pub fn append(&mut self, arena: &mut Arena<K, V>, other: &mut Self)
    // where
    //     K: Ord,
    // {
    //     assert_eq!(arena.id(), self.arena_id);
    //     assert_eq!(arena.id(), other.arena_id);

    //     // Do we have to append anything at all?
    //     if other.is_empty() {
    //         return;
    //     }

    //     // We can just swap `self` and `other` if `self` is empty.
    //     if self.is_empty() {
    //         mem::swap(self, other);
    //         return;
    //     }

    //     let self_iter = mem::replace(self, Self::new(arena)).into_iter(arena);
    //     let other_iter = mem::replace(other, Self::new(arena)).into_iter(arena);
    //     let root = self.root.get_or_insert_with(|| Root::new(arena));
    //     root.append_from_sorted_iters(self_iter, other_iter, &mut self.length, arena);
    // }

    /// Constructs a double-ended iterator over a sub-range of elements in the map.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    /// use std::ops::Bound::Included;
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 3, "a");
    /// map.insert(&mut arena, 5, "b");
    /// map.insert(&mut arena, 8, "c");
    /// for (&key, &value) in map.range(&arena, (Included(&4), Included(&8))) {
    ///     println!("{key}: {value}");
    /// }
    /// assert_eq!(Some((&5, &"b")), map.range(&arena, 4..).next());
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn range<'a, T: ?Sized, R>(&'a self, arena: &'a Arena<K, V>, range: R) -> Range<'a, K, V>
    where
        T: Ord,
        K: Borrow<T> + Ord,
        R: RangeBounds<T>,
    {
        assert_eq!(arena.id(), self.arena_id);
        if let Some(root) = &self.root {
            Range {
                inner: root.reborrow().range_search(range, arena),
                arena,
            }
        } else {
            Range {
                inner: LeafRange::none(),
                arena,
            }
        }
    }

    /// Constructs a mutable double-ended iterator over a sub-range of elements in the map.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map: BTreeMap<&str, i32> = BTreeMap::from_iter(
    ///     &mut arena,
    ///     [("Alice", 0), ("Bob", 0), ("Carol", 0), ("Cheryl", 0)],
    /// );
    /// for (_, balance) in map.range_mut(&arena, "B".."Cheryl") {
    ///     *balance += 100;
    /// }
    /// for (name, balance) in map.into_iter(&mut arena) {
    ///     println!("{name} => {balance}");
    /// }
    /// ```
    pub fn range_mut<'a, T: ?Sized, R>(
        &'a mut self,
        arena: &'a Arena<K, V>,
        range: R,
    ) -> RangeMut<'a, K, V>
    where
        T: Ord,
        K: Borrow<T> + Ord,
        R: RangeBounds<T>,
    {
        assert_eq!(arena.id(), self.arena_id);
        if let Some(root) = &mut self.root {
            RangeMut {
                inner: root.borrow_valmut().range_search(range, arena),
                arena,
                _marker: PhantomData,
            }
        } else {
            RangeMut {
                inner: LeafRange::none(),
                arena,
                _marker: PhantomData,
            }
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut count: BTreeMap<&str, usize> = BTreeMap::new(&arena);
    ///
    /// // count the number of occurrences of letters in the vec
    /// for x in ["a", "b", "a", "c", "a", "b"] {
    ///     count.entry(&mut arena, x).and_modify(|curr| *curr += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(count.get(&arena, "a"), Some(&3));
    /// assert_eq!(count.get(&arena, "b"), Some(&2));
    /// assert_eq!(count.get(&arena, "c"), Some(&1));
    ///
    /// count.drop(&mut arena);
    /// ```
    pub fn entry<'a>(&'a mut self, arena: &'a mut Arena<K, V>, key: K) -> Entry<'a, K, V>
    where
        K: Ord,
    {
        assert_eq!(arena.id(), self.arena_id);
        let (map, dormant_map) = DormantMutRef::new(self);
        match map.root {
            None => Vacant(VacantEntry {
                key,
                handle: None,
                dormant_map,
                arena,
                _marker: PhantomData,
            }),
            Some(ref mut root) => match root.borrow_mut().search_tree(&key, arena) {
                Found(handle) => Occupied(OccupiedEntry {
                    handle,
                    dormant_map,
                    arena,
                    _marker: PhantomData,
                }),
                GoDown(handle) => Vacant(VacantEntry {
                    key,
                    handle: Some(handle),
                    dormant_map,
                    arena,
                    _marker: PhantomData,
                }),
            },
        }
    }

    // /// Splits the collection into two at the given key. Returns everything after the given key,
    // /// including the key.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// use arena_btree::BTreeMap;
    // ///
    // /// let mut a = BTreeMap::new();
    // /// a.insert(1, "a");
    // /// a.insert(2, "b");
    // /// a.insert(3, "c");
    // /// a.insert(17, "d");
    // /// a.insert(41, "e");
    // ///
    // /// let b = a.split_off(&3);
    // ///
    // /// assert_eq!(a.len(), 2);
    // /// assert_eq!(b.len(), 3);
    // ///
    // /// assert_eq!(a[&1], "a");
    // /// assert_eq!(a[&2], "b");
    // ///
    // /// assert_eq!(b[&3], "c");
    // /// assert_eq!(b[&17], "d");
    // /// assert_eq!(b[&41], "e");
    // /// ```
    // pub fn split_off<Q: ?Sized + Ord>(&mut self, key: &Q) -> Self
    // where
    //     K: Borrow<Q> + Ord,
    // {
    //     todo!("FITZGEN: will need to manage the arena here");

    //     if self.is_empty() {
    //         return Self::new();
    //     }

    //     let total_num = self.len();
    //     let left_root = self.root.as_mut().unwrap(); // unwrap succeeds because not empty

    //     let right_root = left_root.split_off(key, &mut self.alloc);

    //     let (new_left_len, right_len) = Root::calc_split_length(total_num, &left_root, &right_root);
    //     self.length = new_left_len;

    //     BTreeMap {
    //         root: Some(right_root),
    //         length: right_len,
    //         alloc: todo!("FITZGEN"), // self.alloc.clone(),
    //         _marker: PhantomData,
    //     }
    // }

    /// Creates a consuming iterator visiting all the keys, in sorted order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// a.insert(&mut arena, 2, "b");
    /// a.insert(&mut arena, 1, "a");
    ///
    /// let keys: Vec<i32> = a.into_keys(&mut arena).collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    #[inline]
    pub fn into_keys<'a>(self, arena: &'a mut Arena<K, V>) -> IntoKeys<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        IntoKeys {
            inner: self.into_iter(arena),
        }
    }

    /// Creates a consuming iterator visiting all the values, in order by key.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// a.insert(&mut arena, 1, "hello");
    /// a.insert(&mut arena, 2, "goodbye");
    ///
    /// let values: Vec<&str> = a.into_values(&mut arena).collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    /// ```
    #[inline]
    pub fn into_values<'a>(self, arena: &'a mut Arena<K, V>) -> IntoValues<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        IntoValues {
            inner: self.into_iter(arena),
        }
    }

    /// Makes a `BTreeMap` from a sorted iterator.
    pub(crate) fn bulk_build_from_sorted_iter<I>(iter: I, arena: &mut Arena<K, V>) -> Self
    where
        K: Ord,
        I: IntoIterator<Item = (K, V)>,
    {
        let mut root = Root::new(arena);
        let mut length = 0;
        root.bulk_push(DedupSortedIter::new(iter.into_iter()), &mut length, arena);
        BTreeMap {
            root: Some(root),
            length,
            arena_id: arena.id(),
            _marker: PhantomData,
            #[cfg(debug_assertions)]
            dropped: false,
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.length == 0 {
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.range.next_unchecked(self.arena) })
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }

    fn last(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.length == 0 {
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.range.next_back_unchecked(self.arena) })
        }
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.length
    }
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter {
            range: self.range.clone(),
            length: self.length,
            arena: self.arena,
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.length == 0 {
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.range.next_unchecked(self.arena) })
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }

    fn last(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.length == 0 {
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.range.next_back_unchecked(self.arena) })
        }
    }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    fn len(&self) -> usize {
        self.length
    }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<'a, K, V> IterMut<'a, K, V> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            range: self.range.reborrow(),
            length: self.length,
            arena: self.arena,
        }
    }
}

impl<K, V> BTreeMap<K, V> {
    /// TODO FITZGEN
    pub fn into_iter<'a>(self, arena: &'a mut Arena<K, V>) -> IntoIter<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        let mut me = ManuallyDrop::new(self);
        if let Some(root) = me.root.take() {
            let full_range = root.into_dying().full_range();

            IntoIter {
                range: full_range,
                length: me.length,
                arena,
            }
        } else {
            IntoIter {
                range: LazyLeafRange::none(),
                length: 0,
                arena,
            }
        }
    }
}

impl<'a, K, V> Drop for IntoIter<'a, K, V> {
    fn drop(&mut self) {
        struct DropGuard<'a, 'b, K, V>(&'a mut IntoIter<'b, K, V>);

        impl<'a, 'b, K, V> Drop for DropGuard<'a, 'b, K, V> {
            fn drop(&mut self) {
                // Continue the same loop we perform below. This only runs when unwinding, so we
                // don't have to care about panics this time (they'll abort).
                while let Some(kv) = self.0.dying_next() {
                    // SAFETY: we consume the dying handle immediately.
                    unsafe { kv.drop_key_val(&self.0.arena) };
                }
            }
        }

        while let Some(kv) = self.dying_next() {
            let guard = DropGuard(self);
            // SAFETY: we don't touch the tree before consuming the dying handle.
            unsafe { kv.drop_key_val(&guard.0.arena) };
            mem::forget(guard);
        }
    }
}

impl<'a, K, V> IntoIter<'a, K, V> {
    /// Core of a `next` method returning a dying KV handle,
    /// invalidated by further calls to this function and some others.
    fn dying_next(
        &mut self,
    ) -> Option<Handle<NodeRef<marker::Dying, K, V, marker::LeafOrInternal>, marker::KV>> {
        if self.length == 0 {
            self.range.deallocating_end(&mut self.arena);
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.range.deallocating_next_unchecked(&mut self.arena) })
        }
    }

    /// Core of a `next_back` method returning a dying KV handle,
    /// invalidated by further calls to this function and some others.
    fn dying_next_back(
        &mut self,
    ) -> Option<Handle<NodeRef<marker::Dying, K, V, marker::LeafOrInternal>, marker::KV>> {
        if self.length == 0 {
            self.range.deallocating_end(&mut self.arena);
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.range.deallocating_next_back_unchecked(&mut self.arena) })
        }
    }
}

impl<'a, K, V> Iterator for IntoIter<'a, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        // SAFETY: we consume the dying handle immediately.
        self.dying_next()
            .map(unsafe { |kv| kv.into_key_val(&self.arena) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }
}

impl<'a, K, V> DoubleEndedIterator for IntoIter<'a, K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        // SAFETY: we consume the dying handle immediately.
        self.dying_next_back()
            .map(unsafe { |kv| kv.into_key_val(&self.arena) })
    }
}

impl<'a, K, V> ExactSizeIterator for IntoIter<'a, K, V> {
    fn len(&self) -> usize {
        self.length
    }
}

impl<'a, K, V> FusedIterator for IntoIter<'a, K, V> {}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<&'a K> {
        self.next_back()
    }

    fn min(mut self) -> Option<&'a K> {
        self.next()
    }

    fn max(mut self) -> Option<&'a K> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<&'a V> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

/// An iterator produced by calling `drain_filter` on BTreeMap.
pub(crate) struct DrainFilter<'a, K, V, F>
where
    F: 'a + FnMut(&K, &mut V) -> bool,
{
    pred: F,
    inner: DrainFilterInner<'a, K, V>,
}

/// Most of the implementation of DrainFilter are generic over the type
/// of the predicate, thus also serving for BTreeSet::DrainFilter.
pub(super) struct DrainFilterInner<'a, K, V> {
    /// Reference to the length field in the borrowed map, updated live.
    length: &'a mut usize,

    /// Buried reference to the root field in the borrowed map.
    /// Wrapped in `Option` to allow drop handler to `take` it.
    dormant_root: Option<DormantMutRef<'a, Root<K, V>>>,

    /// Contains a leaf edge preceding the next element to be returned, or the last leaf edge.
    /// Empty if the map has no root, if iteration went beyond the last leaf edge,
    /// or if a panic occurred in the predicate.
    cur_leaf_edge: Option<Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge>>,

    arena: &'a mut Arena<K, V>,
}

impl<K, V, F> Drop for DrainFilter<'_, K, V, F>
where
    F: FnMut(&K, &mut V) -> bool,
{
    fn drop(&mut self) {
        struct Guard<'a, 'b, K, V, F>(&'a mut DrainFilter<'b, K, V, F>)
        where
            F: FnMut(&K, &mut V) -> bool;
        impl<'a, 'b, K, V, F> Drop for Guard<'a, 'b, K, V, F>
        where
            F: FnMut(&K, &mut V) -> bool,
        {
            fn drop(&mut self) {
                self.0.for_each(|x| {
                    drop(x);
                });
            }
        }

        let g = Guard(self);
        g.0.for_each(|x| {
            drop(x);
        });
    }
}

impl<K, V, F> fmt::Debug for DrainFilter<'_, K, V, F>
where
    K: fmt::Debug,
    V: fmt::Debug,
    F: FnMut(&K, &mut V) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("DrainFilter").finish()
    }
}

impl<K, V, F> Iterator for DrainFilter<'_, K, V, F>
where
    F: FnMut(&K, &mut V) -> bool,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next(&mut self.pred)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DrainFilterInner<'a, K, V> {
    /// Allow Debug implementations to predict the next element.
    pub(super) fn peek(&self) -> Option<(&K, &V)> {
        let edge = self.cur_leaf_edge.as_ref()?;
        edge.reborrow()
            .next_kv(self.arena)
            .ok()
            .map(|h| h.into_kv(self.arena))
    }

    /// Implementation of a typical `DrainFilter::next` method, given the predicate.
    pub(super) fn next<F>(&mut self, pred: &mut F) -> Option<(K, V)>
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        while let Ok(mut kv) = self.cur_leaf_edge.take()?.next_kv(self.arena) {
            let (k, v) = kv.kv_mut(self.arena);
            if pred(k, v) {
                *self.length -= 1;
                let (kv, pos) = kv.remove_kv_tracking(
                    |arena| {
                        // SAFETY: we will touch the root in a way that will not
                        // invalidate the position returned.
                        let root = unsafe { self.dormant_root.take().unwrap().awaken() };
                        root.pop_internal_level(arena);
                        self.dormant_root = Some(DormantMutRef::new(root).1);
                    },
                    self.arena,
                );
                self.cur_leaf_edge = Some(pos);
                return Some(kv);
            }
            self.cur_leaf_edge = Some(kv.next_leaf_edge(self.arena));
        }
        None
    }

    /// Implementation of a typical `DrainFilter::size_hint` method.
    pub(super) fn size_hint(&self) -> (usize, Option<usize>) {
        // In most of the btree iterators, `self.length` is the number of elements
        // yet to be visited. Here, it includes elements that were visited and that
        // the predicate decided not to drain. Making this upper bound more tight
        // during iteration would require an extra field.
        (0, Some(*self.length))
    }
}

impl<K, V, F> FusedIterator for DrainFilter<'_, K, V, F> where F: FnMut(&K, &mut V) -> bool {}

impl<'a, K, V> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.inner.next_checked(self.arena)
    }

    fn last(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<&'a mut V> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for ValuesMut<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a mut V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

impl<'a, K, V> Iterator for IntoKeys<'a, K, V> {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<K> {
        self.next_back()
    }

    fn min(mut self) -> Option<K> {
        self.next()
    }

    fn max(mut self) -> Option<K> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IntoKeys<'a, K, V> {
    fn next_back(&mut self) -> Option<K> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<'a, K, V> ExactSizeIterator for IntoKeys<'a, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K, V> FusedIterator for IntoKeys<'a, K, V> {}

impl<'a, K, V> Iterator for IntoValues<'a, K, V> {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<V> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IntoValues<'a, K, V> {
    fn next_back(&mut self) -> Option<V> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<'a, K, V> ExactSizeIterator for IntoValues<'a, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K, V> FusedIterator for IntoValues<'a, K, V> {}

impl<'a, K, V> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        self.inner.next_back_checked(self.arena)
    }
}

impl<K, V> FusedIterator for Range<'_, K, V> {}

impl<K, V> Clone for Range<'_, K, V> {
    fn clone(&self) -> Self {
        Range {
            inner: self.inner.clone(),
            arena: self.arena,
        }
    }
}

impl<'a, K, V> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.inner.next_checked(self.arena)
    }

    fn last(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for RangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.inner.next_back_checked(self.arena)
    }
}

impl<K, V> FusedIterator for RangeMut<'_, K, V> {}

impl<K: Ord, V> BTreeMap<K, V> {
    /// TODO FTIZGEN
    pub fn from_iter<T>(arena: &mut Arena<K, V>, iter: T) -> BTreeMap<K, V>
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let mut inputs: Vec<_> = iter.into_iter().collect();

        if inputs.is_empty() {
            return BTreeMap::new(arena);
        }

        // use stable sort to preserve the insertion order.
        inputs.sort_by(|a, b| a.0.cmp(&b.0));
        BTreeMap::bulk_build_from_sorted_iter(inputs, arena)
    }
}

impl<K: Ord, V> BTreeMap<K, V> {
    /// TODO FITZGEN
    #[inline]
    pub fn extend<T>(&mut self, arena: &mut Arena<K, V>, iter: T)
    where
        T: IntoIterator<Item = (K, V)>,
    {
        iter.into_iter().for_each(move |(k, v)| {
            self.insert(arena, k, v);
        });
    }
}

impl<K: Hash, V: Hash> BTreeMap<K, V> {
    /// TODO FITZGEN
    pub fn hash<H: Hasher>(&self, arena: &Arena<K, V>, state: &mut H) {
        self.len().hash(state);
        for elt in self.iter(arena) {
            elt.hash(state);
        }
    }
}

impl<K: PartialEq, V: PartialEq> BTreeMap<K, V> {
    /// TODO FITZGEN
    pub fn eq(&self, arena: &Arena<K, V>, other: &BTreeMap<K, V>) -> bool {
        self.len() == other.len() && self.iter(arena).zip(other.iter(arena)).all(|(a, b)| a == b)
    }

    /// TODO FITZGEN
    pub fn ne(&self, arena: &Arena<K, V>, other: &BTreeMap<K, V>) -> bool {
        !self.eq(arena, other)
    }
}

impl<K: PartialOrd, V: PartialOrd> BTreeMap<K, V> {
    /// TODO FITZGEN
    #[inline]
    pub fn partial_cmp(&self, arena: &Arena<K, V>, other: &BTreeMap<K, V>) -> Option<Ordering> {
        self.iter(arena).partial_cmp(other.iter(arena))
    }
}

impl<K: Ord, V: Ord> BTreeMap<K, V> {
    /// TODO FITZGEN
    #[inline]
    pub fn cmp(&self, arena: &Arena<K, V>, other: &BTreeMap<K, V>) -> Ordering {
        self.iter(arena).cmp(other.iter(arena))
    }
}

impl<K, V> Debug for BTreeMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BTreeMap").finish()
    }
}

// impl<K, Q: ?Sized, V> Index<&Q> for BTreeMap<K, V>
// where
//     K: Borrow<Q> + Ord,
//     Q: Ord,
// {
//     type Output = V;
//     /// Returns a reference to the value corresponding to the supplied key.
//     ///
//     /// # Panics
//     ///
//     /// Panics if the key is not present in the `BTreeMap`.
//     #[inline]
//     fn index(&self, key: &Q) -> &V {
//         self.get(key).expect("no entry found for key")
//     }
// }

// impl<K: Ord, V, const N: usize> From<[(K, V); N]> for BTreeMap<K, V> {
//     /// Converts a `[(K, V); N]` into a `BTreeMap<(K, V)>`.
//     ///
//     /// ```
//     /// use arena_btree::BTreeMap;
//     ///
//     /// let map1 = BTreeMap::from([(1, 2), (3, 4)]);
//     /// let map2: BTreeMap<_, _> = [(1, 2), (3, 4)].into();
//     /// assert_eq!(map1, map2);
//     /// ```
//     fn from(mut arr: [(K, V); N]) -> Self {
//         if N == 0 {
//             return BTreeMap::new();
//         }

//         // use stable sort to preserve the insertion order.
//         arr.sort_by(|a, b| a.0.cmp(&b.0));
//         BTreeMap::bulk_build_from_sorted_iter(arr, Arena::default())
//     }
// }

impl<K, V> BTreeMap<K, V> {
    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::new(&arena);
    /// map.insert(&mut arena, 3, "c");
    /// map.insert(&mut arena, 2, "b");
    /// map.insert(&mut arena, 1, "a");
    ///
    /// for (key, value) in map.iter(&arena) {
    ///     println!("{key}: {value}");
    /// }
    ///
    /// let (first_key, first_value) = map.iter(&arena).next().unwrap();
    /// assert_eq!((*first_key, *first_value), (1, "a"));
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn iter<'a>(&'a self, arena: &'a Arena<K, V>) -> Iter<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);

        if let Some(root) = &self.root {
            let full_range = root.reborrow().full_range();

            Iter {
                range: full_range,
                length: self.length,
                arena,
            }
        } else {
            Iter {
                range: LazyLeafRange::none(),
                length: 0,
                arena,
            }
        }
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut map = BTreeMap::from_iter(&mut arena, [
    ///    ("a", 1),
    ///    ("b", 2),
    ///    ("c", 3),
    /// ]);
    ///
    /// // add 10 to the value if the key isn't "a"
    /// for (key, value) in map.iter_mut(&arena) {
    ///     if key != &"a" {
    ///         *value += 10;
    ///     }
    /// }
    ///
    /// map.drop(&mut arena);
    /// ```
    pub fn iter_mut<'a>(&'a mut self, arena: &'a Arena<K, V>) -> IterMut<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        if let Some(root) = &mut self.root {
            let full_range = root.borrow_valmut().full_range();

            IterMut {
                range: full_range,
                length: self.length,
                arena,
                _marker: PhantomData,
            }
        } else {
            IterMut {
                range: LazyLeafRange::none(),
                length: 0,
                arena,
                _marker: PhantomData,
            }
        }
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// a.insert(&mut arena, 2, "b");
    /// a.insert(&mut arena, 1, "a");
    ///
    /// let keys: Vec<_> = a.keys(&arena).cloned().collect();
    /// assert_eq!(keys, [1, 2]);
    ///
    /// a.drop(&mut arena);
    /// ```
    pub fn keys<'a>(&'a self, arena: &'a Arena<K, V>) -> Keys<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        Keys {
            inner: self.iter(arena),
        }
    }

    /// Gets an iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// a.insert(&mut arena, 1, "hello");
    /// a.insert(&mut arena, 2, "goodbye");
    ///
    /// let values: Vec<&str> = a.values(&arena).cloned().collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    ///
    /// a.drop(&mut arena);
    /// ```
    pub fn values<'a>(&'a self, arena: &'a Arena<K, V>) -> Values<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        Values {
            inner: self.iter(arena),
        }
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// a.insert(&mut arena, 1, String::from("hello"));
    /// a.insert(&mut arena, 2, String::from("goodbye"));
    ///
    /// for value in a.values_mut(&arena) {
    ///     value.push_str("!");
    /// }
    ///
    /// let values: Vec<String> = a.values(&arena).cloned().collect();
    /// assert_eq!(values, [String::from("hello!"),
    ///                     String::from("goodbye!")]);
    ///
    /// a.drop(&mut arena);
    /// ```
    pub fn values_mut<'a>(&'a mut self, arena: &'a Arena<K, V>) -> ValuesMut<'a, K, V> {
        assert_eq!(arena.id(), self.arena_id);
        ValuesMut {
            inner: self.iter_mut(arena),
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena,BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// assert_eq!(a.len(), 0);
    /// a.insert(&mut arena, 1, "a");
    /// assert_eq!(a.len(), 1);
    ///
    /// a.drop(&mut arena);
    /// ```
    #[must_use]
    pub const fn len(&self) -> usize {
        self.length
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arena_btree::{Arena, BTreeMap};
    ///
    /// let mut arena = Arena::new();
    /// let mut a = BTreeMap::new(&arena);
    /// assert!(a.is_empty());
    /// a.insert(&mut arena, 1, "a");
    /// assert!(!a.is_empty());
    ///
    /// a.drop(&mut arena);
    /// ```
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests;
