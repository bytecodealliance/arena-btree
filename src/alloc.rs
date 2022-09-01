use crate::node::{InternalNode, LeafNode};
use std::{alloc::Layout, mem::MaybeUninit, ptr::NonNull};

/// TODO
#[derive(Default)]
pub(crate) struct ArenaAllocator;

impl ArenaAllocator {
    pub const fn new() -> Self {
        ArenaAllocator
    }

    pub fn deallocate(&mut self, ptr: NonNull<u8>, layout: Layout) {
        todo!();
    }

    pub fn box_new_uninit_leaf_node<K, V>(&mut self) -> Box<MaybeUninit<LeafNode<K, V>>> {
        todo!()
    }

    pub fn box_new_uninit_internal_node<K, V>(&mut self) -> Box<MaybeUninit<InternalNode<K, V>>> {
        todo!()
    }
}
