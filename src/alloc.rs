use std::{alloc::Layout, mem::MaybeUninit, ptr::NonNull};

/// TODO
#[derive(Default)]
pub(crate) struct ArenaAllocator;

impl ArenaAllocator {
    pub fn deallocate(&mut self, ptr: NonNull<u8>, layout: Layout) {
        todo!();
    }
}

impl ArenaAllocator {
    pub fn box_new_uninit<T>(&mut self) -> Box<MaybeUninit<T>> {
        todo!()
    }
}
