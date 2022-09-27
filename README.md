# `arena-btree`: Arena-based B-Trees for Rust!

[![Rust](https://github.com/bytecodealliance/arena-btree/actions/workflows/rust.yml/badge.svg)](https://github.com/bytecodealliance/arena-btree/actions/workflows/rust.yml)

Instead of allocating each B-Tree node from the global (or a custom) allocator,
allocates them from a vector of nodes in an arena. This vastly cuts down on the
number of allocations a B-Tree needs to make.

This implementation is forked from `rust-lang/rust`'s `BTree{Map,Set}` at commit
`fb888117da6cb3bdae352bafbdb2dc8e2b78a271`.

## Adding Support for More `std` Methods

For expediency and because of a lack of necessity, a variety of features and
methods of the `std` B-Trees were not ported to this crate. If you need them,
pull requests are welcome!

Porting `std` methods to this crate generally follows these steps:

* Copy the relevant code from `std` into this repo.

* Remove any `rustc`-internal attributes, such as `#[stable]`.

* Replace usage of `A: Allocator` type parameters with usage of the `Arena`
  concrete type.

* Port over any tests related to the new feature and get them passing.

* Extend the tests and fuzzing with support for doing differential comparison
  between `std` and this crate for this new feature. See
  `./fuzz/fuzz_targets/differential_map.rs` and `./src/differential.rs` for
  details.
