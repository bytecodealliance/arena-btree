# `arena-btree`: Arena-based B-Trees for Rust!

Instead of allocating each B-Tree node from the global (or a custom) allocator,
allocates them from a vector of nodes that lives within the B-Tree. And instead
of referring to children and parent nodes via pointer, uses compact `u32`
indices into the backing vector. (This latter point is why this crate cannot be
"just" a custom allocator once `std` supports custom allocators on stable.)

Altogether, this vastly cuts down on the number of allocations a B-Tree needs to
make and also shrinks the size of nodes.

This implementation is forked from `rust-lang/rust`'s `BTree{Map,Set}` at commit
`fb888117da6cb3bdae352bafbdb2dc8e2b78a271`.

## Adding Support for More `std` Methods

For expediency and because of a lack of necessity, a variety of features and
methods of the `std` B-Trees were not ported to this crate. If you need them,
pull requests are welcome!

Porting `std` methods to this crate generally follows these steps:

* Copy the relevant code from `std` into this repo.

* Remove any `rustc`-internal attributes, such as `#[stable]`.

* Replace usage of `A: Allocator` type parameters with usage of the
  `ArenaAllocator` concrete type.

* Instead of dereferencing node pointers, index into the arena allocator (you
  may have to add an `ArenaAllocator` parameter to any new helper methods that
  don't have access to `BTreeMap::alloc` already). This means you will have to
  be careful about *which* arena to index into for any methods that involve
  multiple B-Trees, such as `BTreeSet::union`/`BTreeMap::split_off`/etc!

* Uncomment and/or port over any tests related to the new feature and get them
  passing.

* Extend the quickchecks and fuzzing with support for doing differential
  comparison between `std` and this crate for this new feature. See
  `./fuzz/fuzz_targets/differential.rs` and `./src/differential.rs` for details.
