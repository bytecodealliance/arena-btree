use super::node::{ForceResult::*, Root};
use super::search::SearchResult::*;
use crate::arena::Arena;
use core::borrow::Borrow;

impl<K, V> Root<K, V> {
    /// Calculates the length of both trees that result from splitting up
    /// a given number of distinct key-value pairs.
    pub fn calc_split_length(
        total_num: usize,
        root_a: &Root<K, V>,
        root_b: &Root<K, V>,
        arena: &Arena<K, V>,
    ) -> (usize, usize) {
        let (length_a, length_b);
        if root_a.height() < root_b.height() {
            length_a = root_a.reborrow().calc_length(arena);
            length_b = total_num - length_a;
            debug_assert_eq!(length_b, root_b.reborrow().calc_length(arena));
        } else {
            length_b = root_b.reborrow().calc_length(arena);
            length_a = total_num - length_b;
            debug_assert_eq!(length_a, root_a.reborrow().calc_length(arena));
        }
        (length_a, length_b)
    }

    /// Split off a tree with key-value pairs at and after the given key.
    /// The result is meaningful only if the tree is ordered by key,
    /// and if the ordering of `Q` corresponds to that of `K`.
    /// If `self` respects all `BTreeMap` tree invariants, then both
    /// `self` and the returned tree will respect those invariants.
    pub fn split_off<Q: ?Sized + Ord>(&mut self, key: &Q, arena: &mut Arena<K, V>) -> Self
    where
        K: Borrow<Q>,
    {
        let left_root = self;
        let mut right_root = Root::new_pillar(left_root.height(), arena);
        let mut left_node = left_root.borrow_mut();
        let mut right_node = right_root.borrow_mut();

        loop {
            let mut split_edge = match left_node.search_node(key, arena) {
                // key is going to the right tree
                Found(kv) => kv.left_edge(arena),
                GoDown(edge) => edge,
            };

            split_edge.move_suffix(&mut right_node, arena);

            match (split_edge.force(), right_node.force()) {
                (Internal(edge), Internal(node)) => {
                    left_node = edge.descend(arena);
                    right_node = node.first_edge(arena).descend(arena);
                }
                (Leaf(_), Leaf(_)) => break,
                _ => unreachable!(),
            }
        }

        left_root.fix_right_border(arena);
        right_root.fix_left_border(arena);
        right_root
    }

    /// Creates a tree consisting of empty nodes.
    fn new_pillar(height: usize, arena: &mut Arena<K, V>) -> Self {
        let mut root = Root::new(arena);
        for _ in 0..height {
            root.push_internal_level(arena);
        }
        root
    }
}
