use crate::node::{InternalNode, LeafNode};
use std::{
    alloc::Layout,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

/// TODO
pub(crate) struct Arena<K, V> {
    leaf_nodes: InnerArena<LeafNode<K, V>>,
    internal_nodes: InnerArena<InternalNode<K, V>>,
}

impl<K, V> Default for Arena<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Arena<K, V> {
    pub const fn new() -> Self {
        Arena {
            leaf_nodes: InnerArena::new(),
            internal_nodes: InnerArena::new(),
        }
    }

    pub fn allocate_leaf_node(&mut self) -> Box<MaybeUninit<LeafNode<K, V>>> {
        if self.leaf_nodes.items.capacity() == 0 {
            self.leaf_nodes.items.reserve(1);
        }
        Box::new(MaybeUninit::<LeafNode<K, V>>::uninit())
    }

    pub unsafe fn deallocate_leaf_node(&mut self, ptr: NonNull<MaybeUninit<LeafNode<K, V>>>) {
        drop(Box::from_raw(ptr.as_ptr()));
    }

    pub fn allocate_internal_node(&mut self) -> Box<MaybeUninit<InternalNode<K, V>>> {
        if self.internal_nodes.items.capacity() == 0 {
            self.internal_nodes.items.reserve(1);
        }
        Box::new(MaybeUninit::<InternalNode<K, V>>::uninit())
    }

    pub unsafe fn deallocate_internal_node(
        &mut self,
        ptr: NonNull<MaybeUninit<InternalNode<K, V>>>,
    ) {
        drop(Box::from_raw(ptr.as_ptr()));
    }

    pub fn has_empty_capacity(&self) -> bool {
        self.leaf_nodes.capacity() == 0 && self.internal_nodes.capacity() == 0
    }
}

#[derive(Copy, Clone)]
struct Free {
    next_free: OptionNonMaxU32,
}

union MaybeFree<T> {
    free: Free,
    allocated: ManuallyDrop<T>,
}

struct Id<T> {
    index: NonMaxU32,
    _phantom: PhantomData<*mut T>,

    #[cfg(debug_assertions)]
    arena_id: usize,
}

struct InnerArena<T> {
    items: Vec<MaybeFree<T>>,
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

        todo!()
    }

    unsafe fn deallocate(&mut self, id: Id<T>) {
        debug_assert_eq!(self.arena_id, Some(id.arena_id));

        todo!()
    }

    unsafe fn get(&self, id: Id<T>) -> *mut T {
        debug_assert_eq!(self.arena_id, Some(id.arena_id));
        todo!()
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
