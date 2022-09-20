//! Implementation of arenas and ids pointing into them.

use crate::node::{InternalNode, LeafNode};
use std::{
    alloc::Layout,
    cell::UnsafeCell,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    num::NonZeroU32,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

/// An arena containing BTree nodes.
pub struct Arena<K, V> {
    leaf_nodes: InnerArena<LeafNode<K, V>>,
    internal_nodes: InnerArena<InternalNode<K, V>>,

    arena_id: Option<usize>,
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
            arena_id: None,
        }
    }

    pub(crate) fn id(&mut self) -> usize {
        if self.arena_id.is_none() {
            static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);
            self.arena_id = Some(ID_COUNTER.fetch_add(1, Ordering::SeqCst));
        }
        self.arena_id.unwrap()
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
    // `u32::MAX` is a sentinal for "none".
    next_free: u32,
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
    index: NonZeroU32,
    _phantom: PhantomData<*mut T>,
}

impl<T> Id<T> {
    #[inline]
    fn new(index: NonZeroU32) -> Self {
        Id {
            index,
            _phantom: PhantomData,
        }
    }

    pub(crate) fn eq(&self, other: Self) -> bool {
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
    /// These two invariants above allow us to omit bounds checks when indexing
    /// into `items` by id.
    ///
    /// Invariant: The first entry, if it exists, is always free, and is the
    /// head of the free list. If the items are empty, then the free list is
    /// also empty.
    ///
    /// This invariant lets us use `NonZeroU32` indices for our `Id`s, allowing
    /// Rust to make `size(Option<Id>) == size(Id)`, without needing to subtract
    /// one from the `NonZeroU32` all over the place to get the actual index for
    /// the id.
    items: Vec<MaybeFree<T>>,
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
        InnerArena { items: vec![] }
    }

    #[inline]
    fn first_free(&self) -> Option<u32> {
        match self.items.get(0).map(|x| unsafe {
            // SAFETY: the first entry in `items` is always our free list head.
            x.free.next_free
        }) {
            Some(u32::MAX) | None => None,
            Some(next) => Some(next),
        }
    }

    #[inline]
    fn set_first_free(&mut self, next_free: u32) {
        debug_assert!(self.items.len() > 0);
        self.items[0].free.next_free = next_free;
    }

    #[inline]
    fn initialize_first_free(&mut self) {
        debug_assert!(self.items.is_empty());
        self.items.push(MaybeFree {
            free: Free {
                next_free: u32::MAX,
            },
        })
    }

    fn allocate(&mut self) -> Id<T> {
        match self.first_free() {
            None => {
                if self.items.is_empty() {
                    self.initialize_first_free();
                }

                let index = self.items.len();
                let index = u32::try_from(index)
                    .ok()
                    .and_then(|index| if index == u32::MAX { None } else { Some(index) })
                    .unwrap();
                self.items.push(MaybeFree {
                    allocated: ManuallyDrop::new(MaybeUninit::uninit()),
                });

                Id::new(unsafe {
                    // SAFETY: `initialize_first_free` reserved the first
                    // element of `items` for the free list head, so our new
                    // item is at least at index 1.
                    debug_assert_ne!(index, 0);
                    NonZeroU32::new_unchecked(index)
                })
            }
            Some(index) => {
                let len = self.items.len();

                let entry = unsafe {
                    // SAFETY: all indices in the free list are in the range
                    // `1..items.len()`
                    let index = index as usize;
                    debug_assert!(1 <= index && index < len);
                    self.items.get_unchecked_mut(index)
                };

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

                let next_free = unsafe {
                    // SAFETY: all entries in the free list are the `free` union
                    // variant.
                    entry.free.next_free
                };
                self.set_first_free(next_free);

                debug_assert!(
                    self.first_free().map_or(true, |idx| (idx as usize) < len),
                    "Invariant: all indices in the free list are in bounds"
                );

                Id::new(unsafe {
                    // SAFETY: all free list indices are in the range
                    // `1..items.len()`.
                    debug_assert!(1 <= index && (index as usize) < self.items.len());
                    NonZeroU32::new_unchecked(index)
                })
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
        let next_free = self.first_free().unwrap_or(u32::MAX);
        debug_assert!(
            next_free == u32::MAX || (next_free as usize) < self.items.len(),
            "Invariant: all indices in the free list are in bounds"
        );

        let entry = unsafe {
            // SAFETY: all id indices are in the range `1..items.len()`.
            let index = id.index.get() as usize;
            debug_assert!(1 <= index && index < self.items.len());
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

        self.set_first_free(id.index.get());
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
        let entry = unsafe {
            // SAFETY: all id indices are in bounds.
            let index = id.index.get() as usize;
            debug_assert!(index < self.items.len());
            self.items.get_unchecked(index)
        };

        entry.allocated.as_ptr() as *mut T
    }

    fn capacity(&self) -> usize {
        self.items.capacity()
    }
}
