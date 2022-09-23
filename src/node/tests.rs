use super::super::navigate;
use super::*;
use std::fmt::Debug;

impl<'a, K: 'a, V: 'a> NodeRef<marker::Immut<'a>, K, V, marker::LeafOrInternal> {
    // Asserts that the back pointer in each reachable node points to its parent.
    pub fn assert_back_pointers(self, arena: &Arena<K, V>) {
        if let ForceResult::Internal(node) = self.force() {
            for idx in 0..=node.len(arena) {
                let edge = unsafe { Handle::new_edge(node, idx, arena) };
                let child = edge.descend(arena);
                assert!(child.ascend(arena).ok() == Some(edge));
                child.assert_back_pointers(arena);
            }
        }
    }

    // Renders a multi-line display of the keys in order and in tree hierarchy,
    // picturing the tree growing sideways from its root on the left to its
    // leaves on the right.
    pub fn dump_keys(self, arena: &Arena<K, V>) -> String
    where
        K: Debug,
    {
        let mut result = String::new();
        self.visit_nodes_in_order(arena, |pos| match pos {
            navigate::Position::Leaf(leaf) => {
                let depth = self.height();
                let indent = "  ".repeat(depth);
                result += &format!("\n{}{:?}", indent, leaf.keys(arena));
            }
            navigate::Position::Internal(_) => {}
            navigate::Position::InternalKV(kv) => {
                let depth = self.height() - kv.into_node().height();
                let indent = "  ".repeat(depth);
                result += &format!("\n{}{:?}", indent, kv.into_kv(arena).0);
            }
        });
        result
    }
}

#[test]
fn test_splitpoint() {
    for idx in 0..=CAPACITY {
        let (middle_kv_idx, insertion) = splitpoint(idx);

        // Simulate performing the split:
        let mut left_len = middle_kv_idx;
        let mut right_len = CAPACITY - middle_kv_idx - 1;
        match insertion {
            LeftOrRight::Left(edge_idx) => {
                assert!(edge_idx <= left_len);
                left_len += 1;
            }
            LeftOrRight::Right(edge_idx) => {
                assert!(edge_idx <= right_len);
                right_len += 1;
            }
        }
        assert!(left_len >= MIN_LEN_AFTER_SPLIT);
        assert!(right_len >= MIN_LEN_AFTER_SPLIT);
        assert!(left_len + right_len == CAPACITY);
    }
}

#[test]
fn test_partial_eq() {
    let mut arena = Arena::default();

    let mut root1 = NodeRef::new_leaf(&mut arena);
    root1.borrow_mut().push(1, (), &arena);
    let mut root1 = NodeRef::new_internal(root1.forget_type(), &mut arena).forget_type();
    let root2 = Root::new(&mut arena);
    root1.reborrow().assert_back_pointers(&arena);
    root2.reborrow().assert_back_pointers(&arena);

    let leaf_edge_1a = root1
        .reborrow()
        .first_leaf_edge(&arena)
        .forget_node_type(&arena);
    let leaf_edge_1b = root1
        .reborrow()
        .last_leaf_edge(&arena)
        .forget_node_type(&arena);
    let top_edge_1 = root1.reborrow().first_edge(&arena);
    let top_edge_2 = root2.reborrow().first_edge(&arena);

    assert!(leaf_edge_1a == leaf_edge_1a);
    assert!(leaf_edge_1a != leaf_edge_1b);
    assert!(leaf_edge_1a != top_edge_1);
    assert!(leaf_edge_1a != top_edge_2);
    assert!(top_edge_1 == top_edge_1);
    assert!(top_edge_1 != top_edge_2);

    root1.pop_internal_level(&mut arena);
    unsafe { root1.into_dying().deallocate_and_ascend(&mut arena) };
    unsafe { root2.into_dying().deallocate_and_ascend(&mut arena) };
}

#[test]
#[cfg(target_arch = "x86_64")]
fn test_sizes() {
    assert_eq!(core::mem::size_of::<LeafNode<(), ()>>(), 8);
    assert_eq!(
        core::mem::size_of::<LeafNode<i64, i64>>(),
        8 + CAPACITY * 2 * 8
    );
    assert_eq!(
        core::mem::size_of::<InternalNode<(), ()>>(),
        8 + (CAPACITY + 1) * 8
    );
    assert_eq!(
        core::mem::size_of::<InternalNode<i64, i64>>(),
        8 + (CAPACITY * 3 + 1) * 8
    );
}
