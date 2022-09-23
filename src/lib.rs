#![allow(warnings)] // TODO FITZGEN: temp

mod append;
mod arena;
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

pub use arena::Arena;
pub use map::BTreeMap;
pub use set::{BTreeSet, SetArena};

#[cfg(feature = "arbitrary")]
mod arbitrary;

#[cfg(all(feature = "arbitrary", any(fuzzing, test)))]
pub mod differential;

#[doc(hidden)]
trait Recover<Q: ?Sized, K, V> {
    fn get(&self, key: &Q, arena: &Arena<K, V>) -> Option<&K>;
    fn take(&mut self, key: &Q, arena: &mut Arena<K, V>) -> Option<K>;
    fn replace(&mut self, key: K, arena: &mut Arena<K, V>) -> Option<K>;
}

#[cfg(test)]
mod testing;
