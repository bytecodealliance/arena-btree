//! Implementation of arenas and ids pointing into them.

use crate::node::{InternalNode, LeafNode};
use std::{
    alloc::Layout,
    cell::UnsafeCell,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

/// An arena containing BTree nodes.
pub struct Arena<K, V> {
    leaf_nodes: InnerArena<LeafNode<K, V>>,
    internal_nodes: InnerArena<InternalNode<K, V>>,
    // TODO FITZGEN: arena id
}

unsafe impl<K: Send, V: Send> Send for Arena<K, V> {}
unsafe impl<K, V> Sync for Arena<K, V> {}

impl<K, V> Default for Arena<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Arena<K, V> {
    /// Construct a new arena.
    pub const fn new() -> Self {
        Arena {
            leaf_nodes: InnerArena::new(),
            internal_nodes: InnerArena::new(),
        }
    }

    pub(crate) fn allocate_leaf_node(&mut self) -> Id<LeafNode<K, V>> {
        self.leaf_nodes.allocate()
    }

    /// Get a pointer to the leaf node associated with the given `id`.
    ///
    /// # Safety
    ///
    /// The leaf node associated with the given `id` must be allocated.
    ///
    /// Does not check that `id` is from this arena, so if it is from a
    /// different arena, this could lead to use-after-free and
    /// out-of-bounds-access bugs!
    ///
    /// Does not check borrows!
    pub(crate) unsafe fn leaf_node(&self, id: Id<LeafNode<K, V>>) -> *mut LeafNode<K, V> {
        self.leaf_nodes.get(id)
    }

    pub(crate) unsafe fn deallocate_leaf_node(&mut self, id: Id<LeafNode<K, V>>) {
        self.leaf_nodes.deallocate(id);
    }

    pub(crate) fn allocate_internal_node(&mut self) -> Id<InternalNode<K, V>> {
        self.internal_nodes.allocate()
    }

    /// Get a pointer to the leaf node associated with the given `id`.
    ///
    /// # Safety
    ///
    /// The leaf node associated with the given `id` must be allocated.
    ///
    /// Does not check that `id` is from this arena, so if it is from a
    /// different arena, this could lead to use-after-free and
    /// out-of-bounds-access bugs!
    ///
    /// Does not check borrows!
    pub(crate) unsafe fn internal_node(
        &self,
        id: Id<InternalNode<K, V>>,
    ) -> *mut InternalNode<K, V> {
        self.internal_nodes.get(id)
    }

    pub(crate) unsafe fn deallocate_internal_node(&mut self, id: Id<InternalNode<K, V>>) {
        self.internal_nodes.deallocate(id);
    }

    pub(crate) fn has_empty_capacity(&self) -> bool {
        self.leaf_nodes.capacity() == 0 && self.internal_nodes.capacity() == 0
    }
}

#[derive(Copy, Clone)]
struct Free {
    next_free: OptionNonMaxU32,
}

union MaybeFree<T> {
    free: Free,
    allocated: ManuallyDrop<MaybeUninit<UnsafeCell<T>>>,
}

/// An identifier of an entry in an arena.
///
/// This is equivalent to a pointer, and suffers from some of the same footguns:
/// use-after-free bugs. The arena doesn't have a bit for each element to track
/// whether it is free or not, let alone a way to determine if this was the
/// *same* allocation as when the id was handed out or whether it was freed and
/// then re-allocated as an unrelated thing. Therefore, extreme care must be
/// taken to avoid these bugs!
pub(crate) struct Id<T> {
    index: NonMaxU32,
    _phantom: PhantomData<*mut T>,

    #[cfg(debug_assertions)]
    arena_id: usize,
}

impl<T> Id<T> {
    pub(crate) fn eq(&self, other: Self) -> bool {
        debug_assert_eq!(self.arena_id, other.arena_id);
        self.index == other.index
    }
}

impl<T> Copy for Id<T> {}
impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// An arena for values of type `T`.
///
/// Uses simple and fast free list allocation.
struct InnerArena<T> {
    /// The arena items.
    ///
    /// Each free entry points to the next free entry, if any, forming a free
    /// list.
    ///
    /// Invariant: `self.items` can only grow in size, never shrink.
    ///
    /// Invariant: all free list indices are always within bounds.
    ///
    /// These two invariants allow us to omit bounds checks.
    items: Vec<MaybeFree<T>>,

    /// The head of the free list.
    first_free: OptionNonMaxU32,

    #[cfg(debug_assertions)]
    arena_id: Option<usize>,
}

unsafe impl<T> Sync for InnerArena<T> {}
unsafe impl<T> Send for InnerArena<T> {}

impl<T> Default for InnerArena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> InnerArena<T> {
    const fn new() -> Self {
        InnerArena {
            items: vec![],
            first_free: OptionNonMaxU32::none(),

            #[cfg(debug_assertions)]
            arena_id: None,
        }
    }

    fn allocate(&mut self) -> Id<T> {
        #[cfg(debug_assertions)]
        if self.arena_id.is_none() {
            static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);
            self.arena_id = Some(ID_COUNTER.fetch_add(1, Ordering::SeqCst));
        }

        match self.first_free.inflate() {
            Some(index) => {
                let len = self.items.len();

                let entry = unsafe {
                    // SAFETY: all indices in the free list are in bounds.
                    let index = *index as usize;
                    debug_assert!(index < len);
                    self.items.get_unchecked_mut(index)
                };

                self.first_free = unsafe {
                    // SAFETY: all entries in the free list are the `free` union
                    // variant.
                    entry.free.next_free
                };

                debug_assert!(
                    self.first_free
                        .inflate()
                        .map_or(true, |idx| (*idx as usize) < len),
                    "Invariant: all indices in the free list are in bounds"
                );

                unsafe {
                    // SAFETY: We are allocating this entry, so it needs to
                    // become the `allocated` union variant.
                    std::ptr::write(
                        entry as _,
                        MaybeFree {
                            allocated: ManuallyDrop::new(MaybeUninit::uninit()),
                        },
                    );
                }

                Id {
                    index,
                    _phantom: PhantomData,
                    #[cfg(debug_assertions)]
                    arena_id: self.arena_id.unwrap(),
                }
            }
            None => {
                let index = self.items.len();
                let index = u32::try_from(index)
                    .ok()
                    .and_then(|index| NonMaxU32::new(index))
                    .unwrap();
                self.items.push(MaybeFree {
                    allocated: ManuallyDrop::new(MaybeUninit::uninit()),
                });

                Id {
                    index,
                    _phantom: PhantomData,
                    #[cfg(debug_assertions)]
                    arena_id: self.arena_id.unwrap(),
                }
            }
        }
    }

    /// Deallocate the item with the given `id`.
    ///
    /// It is the caller's responsiblity to run `Drop` implementations if they
    /// wish to.
    ///
    /// # Safety
    ///
    /// The given `id` must have been allocated from this arena.
    ///
    /// The given `id` must currently be allocated, and not free.
    unsafe fn deallocate(&mut self, id: Id<T>) {
        debug_assert_eq!(self.arena_id, Some(id.arena_id));

        let next_free = self.first_free;
        debug_assert!(
            next_free
                .inflate()
                .map_or(true, |idx| (*idx as usize) < self.items.len()),
            "Invariant: all indices in the free list are in bounds"
        );

        let entry = unsafe {
            // SAFETY: all id indices are in bounds.
            let index = *id.index as usize;
            debug_assert!(index < self.items.len());
            self.items.get_unchecked_mut(index)
        };

        unsafe {
            // SAFETY: This entry is no longer allocated, and is entering the
            // free list, so it must become the `free` union variant.
            std::ptr::write(
                entry as _,
                MaybeFree {
                    free: Free { next_free },
                },
            );
        }

        self.first_free = id.index.into();
    }

    /// Get a shared borrow of the underlying value associated with the given
    /// `id`.
    ///
    /// # Safety
    ///
    /// The given `id` must have been allocated from this arena.
    ///
    /// The given `id` must currently be allocated, and not free.
    unsafe fn get(&self, id: Id<T>) -> *mut T {
        debug_assert_eq!(self.arena_id, Some(id.arena_id));

        let entry = unsafe {
            // SAFETY: all id indices are in bounds.
            let index = *id.index as usize;
            debug_assert!(index < self.items.len());
            self.items.get_unchecked(index)
        };

        entry.allocated.as_ptr() as *mut T
    }

    fn capacity(&self) -> usize {
        self.items.capacity()
    }
}

mod non_max {
    use std::ops::Deref;

    #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
    pub struct NonMaxU32(u32);

    impl NonMaxU32 {
        #[inline]
        pub fn new(x: u32) -> Option<Self> {
            if x == u32::MAX {
                None
            } else {
                Some(Self(x))
            }
        }
    }

    // NB: Can't implement `DerefMut` because someone could `std::mem::replace`
    // the inner value to be `u32::MAX`.
    impl Deref for NonMaxU32 {
        type Target = u32;

        #[inline]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl From<NonMaxU32> for u32 {
        fn from(x: NonMaxU32) -> Self {
            x.0
        }
    }

    #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
    pub struct OptionNonMaxU32(u32);

    impl Default for OptionNonMaxU32 {
        fn default() -> Self {
            Self::none()
        }
    }

    impl From<NonMaxU32> for OptionNonMaxU32 {
        fn from(x: NonMaxU32) -> Self {
            Self(x.0)
        }
    }

    impl From<Option<NonMaxU32>> for OptionNonMaxU32 {
        fn from(x: Option<NonMaxU32>) -> Self {
            match x {
                Some(x) => x.into(),
                None => Self::none(),
            }
        }
    }

    impl OptionNonMaxU32 {
        pub const fn none() -> Self {
            Self(u32::MAX)
        }

        pub fn inflate(self) -> Option<NonMaxU32> {
            NonMaxU32::new(self.0)
        }

        pub fn is_none(&self) -> bool {
            self.0 == u32::MAX
        }

        pub fn is_some(&self) -> bool {
            !self.is_none()
        }
    }
}
use non_max::*;
