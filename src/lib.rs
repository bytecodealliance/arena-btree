#![allow(warnings)] // TODO FITZGEN: temp

mod alloc;
mod append;
mod borrow;
mod dedup_sorted_iter;
mod fix;
pub mod map;
mod mem;
mod merge_iter;
mod navigate;
mod node;
mod remove;
mod search;
pub mod set;
mod set_val;
mod split;

pub use map::BTreeMap;
pub use set::BTreeSet;

#[cfg(feature = "arbitrary")]
mod arbitrary;

#[cfg(all(feature = "arbitrary", any(fuzzing, test)))]
pub mod differential;

#[doc(hidden)]
trait Recover<Q: ?Sized> {
    type Key;

    fn get(&self, key: &Q) -> Option<&Self::Key>;
    fn take(&mut self, key: &Q) -> Option<Self::Key>;
    fn replace(&mut self, key: Self::Key) -> Option<Self::Key>;
}

#[cfg(test)]
mod testing;
