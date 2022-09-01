use crate::node::{InternalNode, LeafNode};
use std::{
    alloc::Layout,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ptr::NonNull,
};

/// TODO
pub(crate) struct ArenaAllocator<K, V> {
    leaf_nodes: Arena<LeafNode<K, V>>,
    internal_nodes: Arena<InternalNode<K, V>>,
}

impl<K, V> Default for ArenaAllocator<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> ArenaAllocator<K, V> {
    pub const fn new() -> Self {
        ArenaAllocator {
            leaf_nodes: Arena::new(),
            internal_nodes: Arena::new(),
        }
    }

    pub fn allocate_leaf_node(&mut self) -> Box<MaybeUninit<LeafNode<K, V>>> {
        todo!()
    }

    pub unsafe fn deallocate_leaf_node(&mut self, ptr: NonNull<MaybeUninit<LeafNode<K, V>>>) {
        todo!();
    }

    pub fn allocate_internal_node(&mut self) -> Box<MaybeUninit<InternalNode<K, V>>> {
        todo!()
    }

    pub unsafe fn deallocate_internal_node(
        &mut self,
        ptr: NonNull<MaybeUninit<InternalNode<K, V>>>,
    ) {
        todo!();
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
}

struct Arena<T> {
    items: Vec<MaybeFree<T>>,
    first_free: OptionNonMaxU32,
}

unsafe impl<T> Sync for Arena<T> {}
unsafe impl<T> Send for Arena<T> {}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    const fn new() -> Self {
        Arena {
            items: vec![],
            first_free: OptionNonMaxU32::none(),
        }
    }

    fn allocate(&mut self) -> Id<T> {
        todo!()
    }

    unsafe fn deallocate(&mut self, id: Id<T>) {
        todo!()
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
