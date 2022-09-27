use crate::node::{InternalNode, LeafNode};
use std::{
    alloc::Layout,
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

/// TODO
pub struct Arena<K, V> {
    bump: bumpalo::Bump,
    leaf_nodes: FreeList<LeafNode<K, V>>,
    internal_nodes: FreeList<InternalNode<K, V>>,
}

impl<K, V> Default for Arena<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Arena<K, V> {
    pub fn new() -> Self {
        Arena {
            bump: bumpalo::Bump::new(),
            leaf_nodes: FreeList::default(),
            internal_nodes: FreeList::default(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Arena {
            bump: bumpalo::Bump::with_capacity(capacity),
            leaf_nodes: FreeList::default(),
            internal_nodes: FreeList::default(),
        }
    }

    #[inline]
    pub(crate) fn allocate_leaf_node(&self) -> NonNull<LeafNode<K, V>> {
        unsafe {
            let ptr = match self.leaf_nodes.allocate() {
                Some(ptr) => ptr,
                None => self
                    .bump
                    .alloc_layout(Layout::new::<MaybeFree<LeafNode<K, V>>>())
                    .cast(),
            };
            ptr.cast::<LeafNode<K, V>>()
        }
    }

    #[inline]
    pub(crate) unsafe fn deallocate_leaf_node(&self, ptr: NonNull<LeafNode<K, V>>) {
        self.leaf_nodes.deallocate(ptr.cast());
    }

    #[inline]
    pub(crate) fn allocate_internal_node(&self) -> NonNull<InternalNode<K, V>> {
        unsafe {
            let ptr = match self.internal_nodes.allocate() {
                Some(ptr) => ptr,
                None => self
                    .bump
                    .alloc_layout(Layout::new::<MaybeFree<InternalNode<K, V>>>())
                    .cast(),
            };
            ptr.cast::<InternalNode<K, V>>()
        }
    }

    #[inline]
    pub(crate) unsafe fn deallocate_internal_node(&self, ptr: NonNull<InternalNode<K, V>>) {
        self.internal_nodes.deallocate(ptr.cast());
    }
}

struct Free<T> {
    next_free: Cell<Option<NonNull<MaybeFree<T>>>>,
}

union MaybeFree<T> {
    free: ManuallyDrop<Free<T>>,
    allocated: ManuallyDrop<UnsafeCell<T>>,
}

struct FreeList<T> {
    first_free: Cell<Option<NonNull<MaybeFree<T>>>>,
}

impl<T> Default for FreeList<T> {
    fn default() -> Self {
        Self {
            first_free: Cell::new(None),
        }
    }
}

impl<T> FreeList<T> {
    #[inline]
    unsafe fn allocate(&self) -> Option<NonNull<MaybeFree<T>>> {
        let first_free = self.first_free.get()?;
        let next_free = first_free.as_ref().free.next_free.get();
        self.first_free.set(next_free);
        Some(first_free)
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<MaybeFree<T>>) {
        let next_free = self.first_free.get();
        ptr.as_ref().free.next_free.set(next_free);
        self.first_free.set(Some(ptr));
    }
}
