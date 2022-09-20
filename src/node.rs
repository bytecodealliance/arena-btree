// This is an attempt at an implementation following the ideal
//
// ```
// struct BTreeMap<K, V> {
//     height: usize,
//     root: Option<Box<Node<K, V, height>>>
// }
//
// struct Node<K, V, height: usize> {
//     keys: [K; 2 * B - 1],
//     vals: [V; 2 * B - 1],
//     edges: [if height > 0 { Box<Node<K, V, height - 1>> } else { () }; 2 * B],
//     parent: Option<(NonNull<Node<K, V, height + 1>>, u16)>,
//     len: u16,
// }
// ```
//
// Since Rust doesn't actually have dependent types and polymorphic recursion,
// we make do with lots of unsafety.

// A major goal of this module is to avoid complexity by treating the tree as a generic (if
// weirdly shaped) container and avoiding dealing with most of the B-Tree invariants. As such,
// this module doesn't care whether the entries are sorted, which nodes can be underfull, or
// even what underfull means. However, we do rely on a few invariants:
//
// - Trees must have uniform depth/height. This means that every path down to a leaf from a
//   given node has exactly the same length.
// - A node of length `n` has `n` keys, `n` values, and `n + 1` edges.
//   This implies that even an empty node has at least one edge.
//   For a leaf node, "having an edge" only means we can identify a position in the node,
//   since leaf edges are empty and need no data representation. In an internal node,
//   an edge both identifies a position and contains a pointer to a child node.

use crate::arena::{Arena, Id};
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ptr::{self, NonNull};
use core::slice::SliceIndex;
use std::alloc::Layout;

// TODO FITZGEN: make better choices for these numbers, preferably based on the
// sizes of `K` and `V`.
const B: usize = 6;
pub const CAPACITY: usize = 2 * B - 1;
pub const MIN_LEN_AFTER_SPLIT: usize = B - 1;
const KV_IDX_CENTER: usize = B - 1;
const EDGE_IDX_LEFT_OF_CENTER: usize = B - 1;
const EDGE_IDX_RIGHT_OF_CENTER: usize = B;

/// The underlying representation of leaf nodes and part of the representation of internal nodes.
pub(crate) struct LeafNode<K, V> {
    /// We want to be covariant in `K` and `V`.
    parent: Option<Id<InternalNode<K, V>>>,

    /// This node's index into the parent node's `edges` array.
    /// `*node.parent.edges[node.parent_idx]` should be the same thing as `node`.
    /// This is only guaranteed to be initialized when `parent` is non-null.
    parent_idx: MaybeUninit<u16>,

    /// The number of keys and values this node stores.
    len: u16,

    /// The arrays storing the actual data of the node. Only the first `len` elements of each
    /// array are initialized and valid.
    keys: [MaybeUninit<K>; CAPACITY],
    vals: [MaybeUninit<V>; CAPACITY],
}

impl<K, V> LeafNode<K, V> {
    /// Initializes a new `LeafNode` in-place.
    unsafe fn init(this: *mut Self) {
        // As a general policy, we leave fields uninitialized if they can be, as this should
        // be both slightly faster and easier to track in Valgrind.
        unsafe {
            // parent_idx, keys, and vals are all MaybeUninit
            ptr::addr_of_mut!((*this).parent).write(None);
            ptr::addr_of_mut!((*this).len).write(0);
        }
    }

    /// Creates a new boxed `LeafNode`.
    fn new(arena: &mut Arena<K, V>) -> Id<Self> {
        unsafe {
            let mut leaf = arena.allocate_leaf_node();
            LeafNode::init(arena.leaf_node(leaf));
            leaf
        }
    }
}

/// The underlying representation of internal nodes. As with `LeafNode`s, these should be hidden
/// behind `BoxedNode`s to prevent dropping uninitialized keys and values. Any pointer to an
/// `InternalNode` can be directly cast to a pointer to the underlying `LeafNode` portion of the
/// node, allowing code to act on leaf and internal nodes generically without having to even check
/// which of the two a pointer is pointing at. This property is enabled by the use of `repr(C)`.
#[repr(C)]
// gdb_providers.py uses this type name for introspection.
pub(crate) struct InternalNode<K, V> {
    data: LeafNode<K, V>,

    /// The pointers to the children of this node. `len + 1` of these are considered
    /// initialized and valid, except that near the end, while the tree is held
    /// through borrow type `Dying`, some of these pointers are dangling.
    edges: [MaybeUninit<LeafOrInternalId<K, V>>; 2 * B],
}

impl<K, V> InternalNode<K, V> {
    /// Creates a new boxed `InternalNode`.
    ///
    /// # Safety
    /// An invariant of internal nodes is that they have at least one
    /// initialized and valid edge. This function does not set up
    /// such an edge.
    unsafe fn new(arena: &mut Arena<K, V>) -> Id<Self> {
        unsafe {
            let mut node = arena.allocate_internal_node();
            {
                let node = arena.internal_node(node);
                // We only need to initialize the data; the edges are MaybeUninit.
                LeafNode::init(ptr::addr_of_mut!((*node).data));
            }
            node
        }
    }
}

pub(crate) enum LeafOrInternalId<K, V> {
    Leaf(Id<LeafNode<K, V>>),
    Internal(Id<InternalNode<K, V>>),
}

impl<K, V> Copy for LeafOrInternalId<K, V> {}
impl<K, V> Clone for LeafOrInternalId<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V> From<Id<LeafNode<K, V>>> for LeafOrInternalId<K, V> {
    fn from(id: Id<LeafNode<K, V>>) -> Self {
        LeafOrInternalId::Leaf(id)
    }
}

impl<K, V> From<Id<InternalNode<K, V>>> for LeafOrInternalId<K, V> {
    fn from(id: Id<InternalNode<K, V>>) -> Self {
        LeafOrInternalId::Internal(id)
    }
}

// N.B. `NodeRef` is always covariant in `K` and `V`, even when the `BorrowType`
// is `Mut`. This is technically wrong, but cannot result in any unsafety due to
// internal use of `NodeRef` because we stay completely generic over `K` and `V`.
// However, whenever a public type wraps `NodeRef`, make sure that it has the
// correct variance.
///
/// A reference to a node.
///
/// This type has a number of parameters that controls how it acts:
/// - `BorrowType`: A dummy type that describes the kind of borrow and carries a lifetime.
///    - When this is `Immut<'a>`, the `NodeRef` acts roughly like `&'a Node`.
///    - When this is `ValMut<'a>`, the `NodeRef` acts roughly like `&'a Node`
///      with respect to keys and tree structure, but also allows many
///      mutable references to values throughout the tree to coexist.
///    - When this is `Mut<'a>`, the `NodeRef` acts roughly like `&'a mut Node`,
///      although insert methods allow a mutable pointer to a value to coexist.
///    - When this is `Owned`, the `NodeRef` acts roughly like `Box<Node>`,
///      but does not have a destructor, and must be cleaned up manually.
///    - When this is `Dying`, the `NodeRef` still acts roughly like `Box<Node>`,
///      but has methods to destroy the tree bit by bit, and ordinary methods,
///      while not marked as unsafe to call, can invoke UB if called incorrectly.
///   Since any `NodeRef` allows navigating through the tree, `BorrowType`
///   effectively applies to the entire tree, not just to the node itself.
/// - `K` and `V`: These are the types of keys and values stored in the nodes.
/// - `Type`: This can be `Leaf`, `Internal`, or `LeafOrInternal`. When this is
///   `Leaf`, the `NodeRef` points to a leaf node, when this is `Internal` the
///   `NodeRef` points to an internal node, and when this is `LeafOrInternal` the
///   `NodeRef` could be pointing to either type of node.
///   `Type` is named `NodeType` when used outside `NodeRef`.
///
/// Both `BorrowType` and `NodeType` restrict what methods we implement, to
/// exploit static type safety. There are limitations in the way we can apply
/// such restrictions:
/// - For each type parameter, we can only define a method either generically
///   or for one particular type. For example, we cannot define a method like
///   `into_kv` generically for all `BorrowType`, or once for all types that
///   carry a lifetime, because we want it to return `&'a` references.
///   Therefore, we define it only for the least powerful type `Immut<'a>`.
/// - We cannot get implicit coercion from say `Mut<'a>` to `Immut<'a>`.
///   Therefore, we have to explicitly call `reborrow` on a more powerful
///   `NodeRef` in order to reach a method like `into_kv`.
///
/// All methods on `NodeRef` that return some kind of reference, either:
/// - Take `self` by value, and return the lifetime carried by `BorrowType`.
///   Sometimes, to invoke such a method, we need to call `reborrow_mut`.
/// - Take `self` by reference, and (implicitly) return that reference's
///   lifetime, instead of the lifetime carried by `BorrowType`. That way,
///   the borrow checker guarantees that the `NodeRef` remains borrowed as long
///   as the returned reference is used.
///   The methods supporting insert bend this rule by returning a raw pointer,
///   i.e., a reference without any lifetime.
pub(crate) struct NodeRef<BorrowType, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// The number of levels that the node and the level of leaves are apart, a
    /// constant of the node that cannot be entirely described by `Type`, and that
    /// the node itself does not store. We only need to store the height of the root
    /// node, and derive every other node's height from it.
    /// Must be zero if `Type` is `Leaf` and non-zero if `Type` is `Internal`.
    height: usize,
    /// The id of the leaf or internal node. The `IdForType` trait's `Id`
    /// associated type lets us avoid an enum and associated space overheads and
    /// discriminant checks when one variant is impossible.
    node: Type::Id,
    _marker: PhantomData<(BorrowType, Type)>,
}

/// The root node of an owned tree.
///
/// Note that this does not have a destructor, and must be cleaned up manually.
pub(crate) type Root<K, V> = NodeRef<marker::Owned, K, V, marker::LeafOrInternal>;

impl<'a, K: 'a, V: 'a, Type> Copy for NodeRef<marker::Immut<'a>, K, V, Type> where
    Type: marker::IdForType<K, V>
{
}
impl<'a, K: 'a, V: 'a, Type> Clone for NodeRef<marker::Immut<'a>, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<BorrowType, K, V, Type> Sync for NodeRef<BorrowType, K, V, Type>
where
    K: Sync,
    V: Sync,
    Type: marker::IdForType<K, V>,
{
}

unsafe impl<'a, K, V, Type> Send for NodeRef<marker::Immut<'a>, K, V, Type>
where
    K: Sync + 'a,
    V: Sync + 'a,
    Type: marker::IdForType<K, V>,
{
}
unsafe impl<'a, K, V, Type> Send for NodeRef<marker::Mut<'a>, K, V, Type>
where
    K: Send + 'a,
    V: Send + 'a,
    Type: marker::IdForType<K, V>,
{
}
unsafe impl<'a, K, V, Type> Send for NodeRef<marker::ValMut<'a>, K, V, Type>
where
    K: Send + 'a,
    V: Send + 'a,
    Type: marker::IdForType<K, V>,
{
}
unsafe impl<K, V, Type> Send for NodeRef<marker::Owned, K, V, Type>
where
    K: Send,
    V: Send,
    Type: marker::IdForType<K, V>,
{
}
unsafe impl<K, V, Type> Send for NodeRef<marker::Dying, K, V, Type>
where
    K: Send,
    V: Send,
    Type: marker::IdForType<K, V>,
{
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Leaf> {
    pub fn new_leaf(arena: &mut Arena<K, V>) -> Self {
        Self::from_new_leaf(LeafNode::new(arena))
    }

    fn from_new_leaf(leaf: Id<LeafNode<K, V>>) -> Self {
        NodeRef {
            height: 0,
            node: leaf,
            _marker: PhantomData,
        }
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Internal> {
    fn new_internal(child: Root<K, V>, arena: &mut Arena<K, V>) -> Self {
        let mut new_node = unsafe { InternalNode::new(arena) };
        unsafe {
            let new_node = arena.internal_node(new_node);
            (*new_node).edges[0].write(child.node);
        }
        unsafe { NodeRef::from_new_internal(new_node, child.height + 1, arena) }
    }

    /// # Safety
    /// `height` must not be zero.
    unsafe fn from_new_internal(
        internal: Id<InternalNode<K, V>>,
        height: usize,
        arena: &Arena<K, V>,
    ) -> Self {
        debug_assert!(height > 0);
        let mut this = NodeRef {
            height,
            node: internal,
            _marker: PhantomData,
        };
        this.borrow_mut().correct_all_childrens_parent_links(arena);
        this
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    /// Unpack a node reference that was packed as `NodeRef::parent`.
    fn from_internal(node: Id<InternalNode<K, V>>, height: usize) -> Self {
        debug_assert!(height > 0);
        NodeRef {
            height,
            node,
            _marker: PhantomData,
        }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    /// Exposes the data of an internal node.
    ///
    /// Returns a raw ptr to avoid invalidating other references to this node.
    ///
    /// The raw pointer does not keep a borrow on the arena, so extreme care
    /// must be taken to avoid doing something that might cause the arena's
    /// internal items to resize between getting this pointer and dereferencing
    /// it!!!
    fn as_internal_ptr(this: &Self, arena: &Arena<K, V>) -> *mut InternalNode<K, V> {
        unsafe { arena.internal_node(this.node) as *mut _ }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// Borrows exclusive access to the data of an internal node.
    fn as_internal_mut(&mut self, arena: &Arena<K, V>) -> &mut InternalNode<K, V> {
        unsafe { &mut *arena.internal_node(self.node) }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Finds the length of the node. This is the number of keys or values.
    /// The number of edges is `len() + 1`.
    /// Note that, despite being safe, calling this function can have the side effect
    /// of invalidating mutable references that unsafe code has created.
    pub fn len(&self, arena: &Arena<K, V>) -> usize {
        // Crucially, we only access the `len` field here. If BorrowType is marker::ValMut,
        // there might be outstanding mutable references to values that we must not invalidate.
        unsafe { usize::from((*Type::leaf_ptr(self.node, arena)).len) }
    }

    /// Returns the number of levels that the node and leaves are apart. Zero
    /// height means the node is a leaf itself. If you picture trees with the
    /// root on top, the number says at which elevation the node appears.
    /// If you picture trees with leaves on top, the number says how high
    /// the tree extends above the node.
    pub fn height(&self) -> usize {
        self.height
    }

    /// Temporarily takes out another, immutable reference to the same node.
    pub fn reborrow(&self) -> NodeRef<marker::Immut<'_>, K, V, Type> {
        NodeRef {
            height: self.height,
            node: self.node,
            _marker: PhantomData,
        }
    }

    /// Exposes the leaf portion of any leaf or internal node.
    ///
    /// Returns a raw ptr to avoid invalidating other references to this node.
    fn as_leaf_ptr(this: &Self, arena: &Arena<K, V>) -> *mut LeafNode<K, V> {
        // The node must be valid for at least the LeafNode portion.
        // This is not a reference in the NodeRef type because we don't know if
        // it should be unique or shared.
        unsafe { Type::leaf_ptr(this.node, arena) }
    }
}

impl<BorrowType: marker::BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Finds the parent of the current node. Returns `Ok(handle)` if the current
    /// node actually has a parent, where `handle` points to the edge of the parent
    /// that points to the current node. Returns `Err(self)` if the current node has
    /// no parent, giving back the original `NodeRef`.
    ///
    /// The method name assumes you picture trees with the root node on top.
    ///
    /// `edge.descend().ascend().unwrap()` and `node.ascend().unwrap().descend()` should
    /// both, upon success, do nothing.
    pub fn ascend(
        self,
        arena: &Arena<K, V>,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>, Self> {
        let _ = BorrowType::TRAVERSAL_PERMIT;
        // We need to use raw pointers to nodes because, if BorrowType is marker::ValMut,
        // there might be outstanding mutable references to values that we must not invalidate.
        let leaf_ptr: *const _ = Self::as_leaf_ptr(&self, arena);
        unsafe { (*leaf_ptr).parent }
            .as_ref()
            .map(|parent| Handle {
                node: NodeRef::from_internal(*parent, self.height + 1),
                idx: unsafe { usize::from((*leaf_ptr).parent_idx.assume_init()) },
                _marker: PhantomData,
            })
            .ok_or(self)
    }

    pub fn first_edge(self, arena: &Arena<K, V>) -> Handle<Self, marker::Edge> {
        unsafe { Handle::new_edge(self, 0, arena) }
    }

    pub fn last_edge(self, arena: &Arena<K, V>) -> Handle<Self, marker::Edge> {
        let len = self.len(arena);
        unsafe { Handle::new_edge(self, len, arena) }
    }

    /// Note that `self` must be nonempty.
    pub fn first_kv(self, arena: &Arena<K, V>) -> Handle<Self, marker::KV> {
        let len = self.len(arena);
        assert!(len > 0);
        unsafe { Handle::new_kv(self, 0, arena) }
    }

    /// Note that `self` must be nonempty.
    pub fn last_kv(self, arena: &Arena<K, V>) -> Handle<Self, marker::KV> {
        let len = self.len(arena);
        assert!(len > 0);
        unsafe { Handle::new_kv(self, len - 1, arena) }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Could be a public implementation of PartialEq, but only used in this module.
    fn eq(&self, other: &Self) -> bool {
        let Self {
            node,
            height,
            _marker,
        } = self;
        if Type::node_eq(*node, other.node) {
            debug_assert_eq!(*height, other.height);
            true
        } else {
            false
        }
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Immut<'a>, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Exposes the leaf portion of any leaf or internal node in an immutable tree.
    fn into_leaf(self, arena: &Arena<K, V>) -> &'a LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(&self, arena);
        // SAFETY: there can be no mutable references into this tree borrowed as `Immut`.
        unsafe { &*ptr }
    }

    /// Borrows a view into the keys stored in the node.
    pub fn keys(&self, arena: &Arena<K, V>) -> &[K] {
        let leaf = self.into_leaf(arena);
        unsafe {
            // This is `MaybeUninit::slice_assume_init_ref` but that is unstable.
            {
                let slice: &[MaybeUninit<K>] = leaf.keys.get_unchecked(..usize::from(leaf.len));
                // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees that
                // `slice` is initialized, and `MaybeUninit` is guaranteed to have the same layout as `T`.
                // The pointer obtained is valid since it refers to memory owned by `slice` which is a
                // reference and thus guaranteed to be valid for reads.
                unsafe { &*(slice as *const [MaybeUninit<K>] as *const [K]) }
            }
        }
    }
}

impl<K, V> NodeRef<marker::Dying, K, V, marker::LeafOrInternal> {
    /// Similar to `ascend`, gets a reference to a node's parent node, but also
    /// deallocates the current node in the process. This is unsafe because the
    /// current node will still be accessible despite being deallocated.
    pub unsafe fn deallocate_and_ascend(
        self,
        arena: &mut Arena<K, V>,
    ) -> Option<Handle<NodeRef<marker::Dying, K, V, marker::Internal>, marker::Edge>> {
        let height = self.height;
        let node = self.node;
        let ret = self.ascend(arena).ok();
        unsafe {
            match node {
                LeafOrInternalId::Leaf(id) => {
                    debug_assert_eq!(height, 0);
                    arena.deallocate_leaf_node(id)
                }
                LeafOrInternalId::Internal(id) => {
                    debug_assert!(height > 0);
                    arena.deallocate_internal_node(id)
                }
            }
        }
        ret
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Temporarily takes out another mutable reference to the same node. Beware, as
    /// this method is very dangerous, doubly so since it might not immediately appear
    /// dangerous.
    ///
    /// Because mutable pointers can roam anywhere around the tree, the returned
    /// pointer can easily be used to make the original pointer dangling, out of
    /// bounds, or invalid under stacked borrow rules.
    // FIXME(@gereeter) consider adding yet another type parameter to `NodeRef`
    // that restricts the use of navigation methods on reborrowed pointers,
    // preventing this unsafety.
    unsafe fn reborrow_mut(&mut self) -> NodeRef<marker::Mut<'_>, K, V, Type> {
        NodeRef {
            height: self.height,
            node: self.node,
            _marker: PhantomData,
        }
    }

    /// Borrows exclusive access to the leaf portion of a leaf or internal node.
    fn as_leaf_mut(&mut self, arena: &Arena<K, V>) -> &mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(self, arena);
        // SAFETY: we have exclusive access to the entire node.
        unsafe { &mut *ptr }
    }

    /// Offers exclusive access to the leaf portion of a leaf or internal node.
    fn into_leaf_mut(mut self, arena: &Arena<K, V>) -> &'a mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(&mut self, arena);
        // SAFETY: we have exclusive access to the entire node.
        unsafe { &mut *ptr }
    }
}

impl<K, V, Type> NodeRef<marker::Dying, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Borrows exclusive access to the leaf portion of a dying leaf or internal node.
    fn as_leaf_dying(&mut self, arena: &Arena<K, V>) -> &mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(self, arena);
        // SAFETY: we have exclusive access to the entire node.
        unsafe { &mut *ptr }
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Mut<'a>, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Borrows exclusive access to an element of the key storage area.
    ///
    /// # Safety
    /// `index` is in bounds of 0..CAPACITY
    unsafe fn key_area_mut<I, Output: ?Sized>(
        &mut self,
        index: I,
        arena: &Arena<K, V>,
    ) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<K>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe {
            self.as_leaf_mut(arena)
                .keys
                .as_mut_slice()
                .get_unchecked_mut(index)
        }
    }

    /// Borrows exclusive access to an element or slice of the node's value storage area.
    ///
    /// # Safety
    /// `index` is in bounds of 0..CAPACITY
    unsafe fn val_area_mut<I, Output: ?Sized>(
        &mut self,
        index: I,
        arena: &Arena<K, V>,
    ) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<V>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the value slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe {
            self.as_leaf_mut(arena)
                .vals
                .as_mut_slice()
                .get_unchecked_mut(index)
        }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// Borrows exclusive access to an element or slice of the node's storage area for edge contents.
    ///
    /// # Safety
    /// `index` is in bounds of 0..CAPACITY + 1
    unsafe fn edge_area_mut<I, Output: ?Sized>(
        &mut self,
        index: I,
        arena: &Arena<K, V>,
    ) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<LeafOrInternalId<K, V>>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the edge slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe {
            self.as_internal_mut(arena)
                .edges
                .as_mut_slice()
                .get_unchecked_mut(index)
        }
    }
}

unsafe fn get_unchecked<'a, T>(xs: *const [T], idx: usize) -> &'a T {
    (&*xs).get_unchecked(idx)
}

unsafe fn get_unchecked_mut<'a, T>(xs: *mut [T], idx: usize) -> &'a mut T {
    (&mut *xs).get_unchecked_mut(idx)
}

impl<'a, K, V, Type> NodeRef<marker::ValMut<'a>, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// # Safety
    /// - The node has more than `idx` initialized elements.
    unsafe fn into_key_val_mut_at(mut self, idx: usize, arena: &Arena<K, V>) -> (&'a K, &'a mut V) {
        // We only create a reference to the one element we are interested in,
        // to avoid aliasing with outstanding references to other elements,
        // in particular, those returned to the caller in earlier iterations.
        let leaf = Self::as_leaf_ptr(&mut self, arena);
        let keys = unsafe { ptr::addr_of!((*leaf).keys) };
        let vals = unsafe { ptr::addr_of_mut!((*leaf).vals) };
        // We must coerce to unsized array pointers because of Rust issue #74679.
        let keys: *const [_] = keys;
        let vals: *mut [_] = vals;
        let key = unsafe { get_unchecked::<MaybeUninit<K>>(keys, idx).assume_init_ref() };
        let val = unsafe { get_unchecked_mut(vals, idx).assume_init_mut() };
        (key, val)
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Mut<'a>, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Borrows exclusive access to the length of the node.
    pub fn len_mut(&mut self, arena: &Arena<K, V>) -> &mut u16 {
        &mut self.as_leaf_mut(arena).len
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// # Safety
    /// Every item returned by `range` is a valid edge index for the node.
    unsafe fn correct_childrens_parent_links<R: Iterator<Item = usize>>(
        &mut self,
        range: R,
        arena: &Arena<K, V>,
    ) {
        for i in range {
            debug_assert!(i <= self.len(arena));
            unsafe { Handle::new_edge(self.reborrow_mut(), i, arena) }.correct_parent_link(arena);
        }
    }

    fn correct_all_childrens_parent_links(&mut self, arena: &Arena<K, V>) {
        let len = self.len(arena);
        unsafe { self.correct_childrens_parent_links(0..=len, arena) };
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Sets the node's link to its parent edge,
    /// without invalidating other references to the node.
    fn set_parent_link(
        &mut self,
        parent: Id<InternalNode<K, V>>,
        parent_idx: usize,
        arena: &Arena<K, V>,
    ) {
        let leaf = Self::as_leaf_ptr(self, arena);
        unsafe { (*leaf).parent = Some(parent) };
        unsafe { (*leaf).parent_idx.write(parent_idx as u16) };
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::LeafOrInternal> {
    /// Clears the root's link to its parent edge.
    fn clear_parent_link(&mut self, arena: &Arena<K, V>) {
        let mut root_node = self.borrow_mut();
        let leaf = root_node.as_leaf_mut(arena);
        leaf.parent = None;
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::LeafOrInternal> {
    /// Returns a new owned tree, with its own root node that is initially empty.
    pub fn new(arena: &mut Arena<K, V>) -> Self {
        NodeRef::new_leaf(arena).forget_type()
    }

    /// Adds a new internal node with a single edge pointing to the previous root node,
    /// make that new node the root node, and return it. This increases the height by 1
    /// and is the opposite of `pop_internal_level`.
    pub fn push_internal_level(
        &mut self,
        arena: &mut Arena<K, V>,
    ) -> NodeRef<marker::Mut<'_>, K, V, marker::Internal> {
        super::mem::take_mut(self, |old_root| {
            NodeRef::new_internal(old_root, arena).forget_type()
        });

        // `self.borrow_mut()`, except that we just forgot we're internal now:
        NodeRef {
            height: self.height,
            node: match self.node {
                LeafOrInternalId::Leaf(_) => unreachable!(),
                LeafOrInternalId::Internal(id) => id,
            },
            _marker: PhantomData,
        }
    }

    /// Removes the internal root node, using its first child as the new root node.
    /// As it is intended only to be called when the root node has only one child,
    /// no cleanup is done on any of the keys, values and other children.
    /// This decreases the height by 1 and is the opposite of `push_internal_level`.
    ///
    /// Requires exclusive access to the `NodeRef` object but not to the root node;
    /// it will not invalidate other handles or references to the root node.
    ///
    /// Panics if there is no internal level, i.e., if the root node is a leaf.
    pub fn pop_internal_level(&mut self, arena: &mut Arena<K, V>) {
        assert!(self.height > 0);

        let top = self.node;

        // SAFETY: we asserted to be internal.
        let internal_self = unsafe { self.borrow_mut().cast_to_internal_unchecked() };
        // SAFETY: we borrowed `self` exclusively and its borrow type is exclusive.
        let internal_node = unsafe { &mut *NodeRef::as_internal_ptr(&internal_self, arena) };
        // SAFETY: the first edge is always initialized.
        self.node = unsafe { internal_node.edges[0].assume_init_read() };
        self.height -= 1;
        self.clear_parent_link(arena);

        match top {
            LeafOrInternalId::Internal(id) => unsafe {
                arena.deallocate_internal_node(id);
            },
            LeafOrInternalId::Leaf(_) => unreachable!(),
        }
    }
}

impl<K, V, Type> NodeRef<marker::Owned, K, V, Type>
where
    Type: marker::IdForType<K, V>,
{
    /// Mutably borrows the owned root node. Unlike `reborrow_mut`, this is safe
    /// because the return value cannot be used to destroy the root, and there
    /// cannot be other references to the tree.
    pub fn borrow_mut(&mut self) -> NodeRef<marker::Mut<'_>, K, V, Type> {
        NodeRef {
            height: self.height,
            node: self.node,
            _marker: PhantomData,
        }
    }

    /// Slightly mutably borrows the owned root node.
    pub fn borrow_valmut(&mut self) -> NodeRef<marker::ValMut<'_>, K, V, Type> {
        NodeRef {
            height: self.height,
            node: self.node,
            _marker: PhantomData,
        }
    }

    /// Irreversibly transitions to a reference that permits traversal and offers
    /// destructive methods and little else.
    pub fn into_dying(self) -> NodeRef<marker::Dying, K, V, Type> {
        NodeRef {
            height: self.height,
            node: self.node,
            _marker: PhantomData,
        }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Leaf> {
    /// Adds a key-value pair to the end of the node, and returns
    /// the mutable reference of the inserted value.
    pub fn push(&mut self, key: K, val: V, arena: &Arena<K, V>) -> &mut V {
        let len = self.len_mut(arena);
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        unsafe {
            self.key_area_mut(idx, arena).write(key);
            self.val_area_mut(idx, arena).write(val)
        }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// Adds a key-value pair, and an edge to go to the right of that pair,
    /// to the end of the node.
    pub fn push(&mut self, key: K, val: V, edge: Root<K, V>, arena: &Arena<K, V>) {
        assert!(edge.height == self.height - 1);

        let len = self.len_mut(arena);
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        unsafe {
            self.key_area_mut(idx, arena).write(key);
            self.val_area_mut(idx, arena).write(val);
            self.edge_area_mut(idx + 1, arena).write(edge.node);
            Handle::new_edge(self.reborrow_mut(), idx + 1, arena).correct_parent_link(arena);
        }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Leaf> {
    /// Removes any static information asserting that this node is a `Leaf` node.
    pub fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        NodeRef {
            height: self.height,
            node: self.node.into(),
            _marker: PhantomData,
        }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    /// Removes any static information asserting that this node is an `Internal` node.
    pub fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        NodeRef {
            height: self.height,
            node: self.node.into(),
            _marker: PhantomData,
        }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
    /// Checks whether a node is an `Internal` node or a `Leaf` node.
    pub fn force(
        self,
    ) -> ForceResult<
        NodeRef<BorrowType, K, V, marker::Leaf>,
        NodeRef<BorrowType, K, V, marker::Internal>,
    > {
        match self.node {
            LeafOrInternalId::Leaf(node) => {
                debug_assert_eq!(self.height, 0);
                ForceResult::Leaf(NodeRef {
                    height: 0,
                    node,
                    _marker: PhantomData,
                })
            }
            LeafOrInternalId::Internal(node) => {
                debug_assert_ne!(self.height, 0);
                ForceResult::Internal(NodeRef {
                    height: self.height,
                    node,
                    _marker: PhantomData,
                })
            }
        }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Unsafely asserts to the compiler the static information that this node is a `Leaf`.
    unsafe fn cast_to_leaf_unchecked(self) -> NodeRef<marker::Mut<'a>, K, V, marker::Leaf> {
        debug_assert_eq!(self.height, 0);
        NodeRef {
            height: self.height,
            node: match self.node {
                LeafOrInternalId::Leaf(id) => id,
                LeafOrInternalId::Internal(_) => unreachable!(),
            },
            _marker: PhantomData,
        }
    }

    /// Unsafely asserts to the compiler the static information that this node is an `Internal`.
    unsafe fn cast_to_internal_unchecked(self) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        debug_assert!(self.height > 0);
        NodeRef {
            height: self.height,
            node: match self.node {
                LeafOrInternalId::Leaf(_) => unreachable!(),
                LeafOrInternalId::Internal(id) => id,
            },
            _marker: PhantomData,
        }
    }
}

/// A reference to a specific key-value pair or edge within a node. The `Node` parameter
/// must be a `NodeRef`, while the `Type` can either be `KV` (signifying a handle on a key-value
/// pair) or `Edge` (signifying a handle on an edge).
///
/// Note that even `Leaf` nodes can have `Edge` handles. Instead of representing a pointer to
/// a child node, these represent the spaces where child pointers would go between the key-value
/// pairs. For example, in a node with length 2, there would be 3 possible edge locations - one
/// to the left of the node, one between the two pairs, and one at the right of the node.
pub(crate) struct Handle<Node, Type> {
    node: Node,
    idx: usize,
    _marker: PhantomData<Type>,
}

impl<Node: Copy, Type> Copy for Handle<Node, Type> {}
// We don't need the full generality of `#[derive(Clone)]`, as the only time `Node` will be
// `Clone`able is when it is an immutable reference and therefore `Copy`.
impl<Node: Copy, Type> Clone for Handle<Node, Type> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Node, Type> Handle<Node, Type> {
    /// Retrieves the node that contains the edge or key-value pair this handle points to.
    pub fn into_node(self) -> Node {
        self.node
    }

    /// Returns the position of this handle in the node.
    pub fn idx(&self) -> usize {
        self.idx
    }
}

impl<BorrowType, K, V, NodeType> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    /// Creates a new handle to a key-value pair in `node`.
    /// Unsafe because the caller must ensure that `idx < node.len()`.
    pub unsafe fn new_kv(
        node: NodeRef<BorrowType, K, V, NodeType>,
        idx: usize,
        arena: &Arena<K, V>,
    ) -> Self {
        debug_assert!(idx < node.len(arena));

        Handle {
            node,
            idx,
            _marker: PhantomData,
        }
    }

    pub fn left_edge(
        self,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        unsafe { Handle::new_edge(self.node, self.idx, arena) }
    }

    pub fn right_edge(
        self,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        unsafe { Handle::new_edge(self.node, self.idx + 1, arena) }
    }
}

impl<BorrowType, K, V, NodeType, HandleType> PartialEq
    for Handle<NodeRef<BorrowType, K, V, NodeType>, HandleType>
where
    NodeType: marker::IdForType<K, V>,
{
    fn eq(&self, other: &Self) -> bool {
        let Self { node, idx, _marker } = self;
        node.eq(&other.node) && *idx == other.idx
    }
}

impl<BorrowType, K, V, NodeType, HandleType> Handle<NodeRef<BorrowType, K, V, NodeType>, HandleType>
where
    NodeType: marker::IdForType<K, V>,
{
    /// Temporarily takes out another immutable handle on the same location.
    pub fn reborrow(&self) -> Handle<NodeRef<marker::Immut<'_>, K, V, NodeType>, HandleType> {
        // We can't use Handle::new_kv or Handle::new_edge because we don't know our type
        Handle {
            node: self.node.reborrow(),
            idx: self.idx,
            _marker: PhantomData,
        }
    }
}

impl<'a, K, V, NodeType, HandleType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType>
where
    NodeType: marker::IdForType<K, V>,
{
    /// Temporarily takes out another mutable handle on the same location. Beware, as
    /// this method is very dangerous, doubly so since it might not immediately appear
    /// dangerous.
    ///
    /// For details, see `NodeRef::reborrow_mut`.
    pub unsafe fn reborrow_mut(
        &mut self,
    ) -> Handle<NodeRef<marker::Mut<'_>, K, V, NodeType>, HandleType> {
        // We can't use Handle::new_kv or Handle::new_edge because we don't know our type
        Handle {
            node: unsafe { self.node.reborrow_mut() },
            idx: self.idx,
            _marker: PhantomData,
        }
    }
}

impl<BorrowType, K, V, NodeType> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge>
where
    NodeType: marker::IdForType<K, V>,
{
    /// Creates a new handle to an edge in `node`.
    /// Unsafe because the caller must ensure that `idx <= node.len()`.
    pub unsafe fn new_edge(
        node: NodeRef<BorrowType, K, V, NodeType>,
        idx: usize,
        arena: &Arena<K, V>,
    ) -> Self {
        debug_assert!(idx <= node.len(arena));

        Handle {
            node,
            idx,
            _marker: PhantomData,
        }
    }

    pub fn left_kv(
        self,
        arena: &Arena<K, V>,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx > 0 {
            Ok(unsafe { Handle::new_kv(self.node, self.idx - 1, arena) })
        } else {
            Err(self)
        }
    }

    pub fn right_kv(
        self,
        arena: &Arena<K, V>,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx < self.node.len(arena) {
            Ok(unsafe { Handle::new_kv(self.node, self.idx, arena) })
        } else {
            Err(self)
        }
    }
}

pub enum LeftOrRight<T> {
    Left(T),
    Right(T),
}

/// Given an edge index where we want to insert into a node filled to capacity,
/// computes a sensible KV index of a split point and where to perform the insertion.
/// The goal of the split point is for its key and value to end up in a parent node;
/// the keys, values and edges to the left of the split point become the left child;
/// the keys, values and edges to the right of the split point become the right child.
fn splitpoint(edge_idx: usize) -> (usize, LeftOrRight<usize>) {
    debug_assert!(edge_idx <= CAPACITY);
    // Rust issue #74834 tries to explain these symmetric rules.
    match edge_idx {
        x if 0 <= x && x < EDGE_IDX_LEFT_OF_CENTER => {
            (KV_IDX_CENTER - 1, LeftOrRight::Left(edge_idx))
        }
        EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_RIGHT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Right(0)),
        _ => (
            KV_IDX_CENTER + 1,
            LeftOrRight::Right(edge_idx - (KV_IDX_CENTER + 1 + 1)),
        ),
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Inserts a new key-value pair between the key-value pairs to the right and left of
    /// this edge. This method assumes that there is enough space in the node for the new
    /// pair to fit.
    ///
    /// The returned pointer points to the inserted value.
    fn insert_fit(&mut self, key: K, val: V, arena: &Arena<K, V>) -> *mut V {
        debug_assert!(self.node.len(arena) < CAPACITY);
        let new_len = self.node.len(arena) + 1;

        unsafe {
            slice_insert(self.node.key_area_mut(..new_len, arena), self.idx, key);
            slice_insert(self.node.val_area_mut(..new_len, arena), self.idx, val);
            *self.node.len_mut(arena) = new_len as u16;

            self.node.val_area_mut(self.idx, arena).assume_init_mut()
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Inserts a new key-value pair between the key-value pairs to the right and left of
    /// this edge. This method splits the node if there isn't enough room.
    ///
    /// The returned pointer points to the inserted value.
    fn insert(
        mut self,
        key: K,
        val: V,
        arena: &mut Arena<K, V>,
    ) -> (Option<SplitResult<'a, K, V, marker::Leaf>>, *mut V) {
        if self.node.len(arena) < CAPACITY {
            let val_ptr = self.insert_fit(key, val, arena);
            (None, val_ptr)
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx, arena) };
            let mut result = middle.split(arena);
            let mut insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx, arena)
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    Handle::new_edge(result.right.borrow_mut(), insert_idx, arena)
                },
            };
            let val_ptr = insertion_edge.insert_fit(key, val, arena);
            (Some(result), val_ptr)
        }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    /// Fixes the parent pointer and index in the child node that this edge
    /// links to. This is useful when the ordering of edges has been changed,
    fn correct_parent_link(self, arena: &Arena<K, V>) {
        // Create backpointer without invalidating other references to the node.
        let parent = self.node.node;
        let idx = self.idx;
        let mut child = self.descend(arena);
        child.set_parent_link(parent, idx, arena);
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    /// Inserts a new key-value pair and an edge that will go to the right of that new pair
    /// between this edge and the key-value pair to the right of this edge. This method assumes
    /// that there is enough space in the node for the new pair to fit.
    fn insert_fit(&mut self, key: K, val: V, edge: Root<K, V>, arena: &Arena<K, V>) {
        debug_assert!(self.node.len(arena) < CAPACITY);
        debug_assert!(edge.height == self.node.height - 1);
        let new_len = self.node.len(arena) + 1;

        unsafe {
            slice_insert(self.node.key_area_mut(..new_len, arena), self.idx, key);
            slice_insert(self.node.val_area_mut(..new_len, arena), self.idx, val);
            slice_insert(
                self.node.edge_area_mut(..new_len + 1, arena),
                self.idx + 1,
                edge.node,
            );
            *self.node.len_mut(arena) = new_len as u16;

            self.node
                .correct_childrens_parent_links(self.idx + 1..new_len + 1, arena);
        }
    }

    /// Inserts a new key-value pair and an edge that will go to the right of that new pair
    /// between this edge and the key-value pair to the right of this edge. This method splits
    /// the node if there isn't enough room.
    fn insert(
        mut self,
        key: K,
        val: V,
        edge: Root<K, V>,
        arena: &mut Arena<K, V>,
    ) -> Option<SplitResult<'a, K, V, marker::Internal>> {
        assert!(edge.height == self.node.height - 1);

        if self.node.len(arena) < CAPACITY {
            self.insert_fit(key, val, edge, arena);
            None
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx, arena) };
            let mut result = middle.split(arena);
            let mut insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx, arena)
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    Handle::new_edge(result.right.borrow_mut(), insert_idx, arena)
                },
            };
            insertion_edge.insert_fit(key, val, edge, arena);
            Some(result)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Inserts a new key-value pair between the key-value pairs to the right and left of
    /// this edge. This method splits the node if there isn't enough room, and tries to
    /// insert the split off portion into the parent node recursively, until the root is reached.
    ///
    /// If the returned result is some `SplitResult`, the `left` field will be the root node.
    /// The returned pointer points to the inserted value, which in the case of `SplitResult`
    /// is in the `left` or `right` tree.
    pub fn insert_recursing(
        self,
        key: K,
        value: V,
        arena: &mut Arena<K, V>,
    ) -> (
        Option<SplitResult<'a, K, V, marker::LeafOrInternal>>,
        *mut V,
    ) {
        let (mut split, val_ptr) = match self.insert(key, value, arena) {
            (None, val_ptr) => return (None, val_ptr),
            (Some(split), val_ptr) => (split.forget_node_type(), val_ptr),
        };

        loop {
            split = match split.left.ascend(arena) {
                Ok(parent) => match parent.insert(split.kv.0, split.kv.1, split.right, arena) {
                    None => return (None, val_ptr),
                    Some(split) => split.forget_node_type(),
                },
                Err(root) => {
                    return (
                        Some(SplitResult {
                            left: root,
                            ..split
                        }),
                        val_ptr,
                    )
                }
            };
        }
    }
}

impl<BorrowType: marker::BorrowType, K, V>
    Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>
{
    /// Finds the node pointed to by this edge.
    ///
    /// The method name assumes you picture trees with the root node on top.
    ///
    /// `edge.descend().ascend().unwrap()` and `node.ascend().unwrap().descend()` should
    /// both, upon success, do nothing.
    pub fn descend(self, arena: &Arena<K, V>) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        let _ = BorrowType::TRAVERSAL_PERMIT;
        // We need to use raw pointers to nodes because, if BorrowType is
        // marker::ValMut, there might be outstanding mutable references to
        // values that we must not invalidate. There's no worry accessing the
        // height field because that value is copied. Beware that, once the
        // node pointer is dereferenced, we access the edges array with a
        // reference (Rust issue #73987) and invalidate any other references
        // to or inside the array, should any be around.
        let parent_ptr = NodeRef::as_internal_ptr(&self.node, arena);
        let node = unsafe {
            (*parent_ptr)
                .edges
                .get_unchecked(self.idx)
                .assume_init_read()
        };
        NodeRef {
            node,
            height: self.node.height - 1,
            _marker: PhantomData,
        }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Immut<'a>, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    pub fn into_kv(self, arena: &Arena<K, V>) -> (&'a K, &'a V) {
        debug_assert!(self.idx < self.node.len(arena));
        let leaf = self.node.into_leaf(arena);
        let k = unsafe { leaf.keys.get_unchecked(self.idx).assume_init_ref() };
        let v = unsafe { leaf.vals.get_unchecked(self.idx).assume_init_ref() };
        (k, v)
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    pub fn key_mut(&mut self, arena: &Arena<K, V>) -> &mut K {
        unsafe { self.node.key_area_mut(self.idx, arena).assume_init_mut() }
    }

    pub fn into_val_mut(self, arena: &Arena<K, V>) -> &'a mut V {
        debug_assert!(self.idx < self.node.len(arena));
        let leaf = self.node.into_leaf_mut(arena);
        unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() }
    }
}

impl<'a, K, V, NodeType> Handle<NodeRef<marker::ValMut<'a>, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    pub fn into_kv_valmut(self, arena: &Arena<K, V>) -> (&'a K, &'a mut V) {
        unsafe { self.node.into_key_val_mut_at(self.idx, arena) }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    pub fn kv_mut(&mut self, arena: &Arena<K, V>) -> (&mut K, &mut V) {
        debug_assert!(self.idx < self.node.len(arena));
        // We cannot call separate key and value methods, because calling the second one
        // invalidates the reference returned by the first.
        unsafe {
            let leaf = self.node.as_leaf_mut(arena);
            let key = leaf.keys.get_unchecked_mut(self.idx).assume_init_mut();
            let val = leaf.vals.get_unchecked_mut(self.idx).assume_init_mut();
            (key, val)
        }
    }

    /// Replaces the key and value that the KV handle refers to.
    pub fn replace_kv(&mut self, k: K, v: V, arena: &Arena<K, V>) -> (K, V) {
        let (key, val) = self.kv_mut(arena);
        (mem::replace(key, k), mem::replace(val, v))
    }
}

impl<K, V, NodeType> Handle<NodeRef<marker::Dying, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    /// Extracts the key and value that the KV handle refers to.
    /// # Safety
    /// The node that the handle refers to must not yet have been deallocated.
    pub unsafe fn into_key_val(mut self, arena: &Arena<K, V>) -> (K, V) {
        debug_assert!(self.idx < self.node.len(arena));
        let leaf = self.node.as_leaf_dying(arena);
        unsafe {
            let key = leaf.keys.get_unchecked_mut(self.idx).assume_init_read();
            let val = leaf.vals.get_unchecked_mut(self.idx).assume_init_read();
            (key, val)
        }
    }

    /// Drops the key and value that the KV handle refers to.
    /// # Safety
    /// The node that the handle refers to must not yet have been deallocated.
    #[inline]
    pub unsafe fn drop_key_val(mut self, arena: &Arena<K, V>) {
        debug_assert!(self.idx < self.node.len(arena));
        let leaf = self.node.as_leaf_dying(arena);
        unsafe {
            leaf.keys.get_unchecked_mut(self.idx).assume_init_drop();
            leaf.vals.get_unchecked_mut(self.idx).assume_init_drop();
        }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV>
where
    NodeType: marker::IdForType<K, V>,
{
    /// Helps implementations of `split` for a particular `NodeType`,
    /// by taking care of leaf data.
    fn split_leaf_data(&mut self, new_node: &mut LeafNode<K, V>, arena: &Arena<K, V>) -> (K, V) {
        debug_assert!(self.idx < self.node.len(arena));
        let old_len = self.node.len(arena);
        let new_len = old_len - self.idx - 1;
        new_node.len = new_len as u16;
        unsafe {
            let k = self.node.key_area_mut(self.idx, arena).assume_init_read();
            let v = self.node.val_area_mut(self.idx, arena).assume_init_read();

            move_to_slice(
                self.node.key_area_mut(self.idx + 1..old_len, arena),
                &mut new_node.keys[..new_len],
            );
            move_to_slice(
                self.node.val_area_mut(self.idx + 1..old_len, arena),
                &mut new_node.vals[..new_len],
            );

            *self.node.len_mut(arena) = self.idx as u16;
            (k, v)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
    /// Splits the underlying node into three parts:
    ///
    /// - The node is truncated to only contain the key-value pairs to the left of
    ///   this handle.
    /// - The key and value pointed to by this handle are extracted.
    /// - All the key-value pairs to the right of this handle are put into a newly
    ///   allocated node.
    pub fn split(mut self, arena: &mut Arena<K, V>) -> SplitResult<'a, K, V, marker::Leaf> {
        let mut new_node = LeafNode::new(arena);

        let kv = self.split_leaf_data(unsafe { &mut *arena.leaf_node(new_node) }, arena);

        let right = NodeRef::from_new_leaf(new_node);
        SplitResult {
            left: self.node,
            kv,
            right,
        }
    }

    /// Removes the key-value pair pointed to by this handle and returns it, along with the edge
    /// that the key-value pair collapsed into.
    pub fn remove(
        mut self,
        arena: &mut Arena<K, V>,
    ) -> (
        (K, V),
        Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge>,
    ) {
        let old_len = self.node.len(arena);
        unsafe {
            let k = slice_remove(self.node.key_area_mut(..old_len, arena), self.idx);
            let v = slice_remove(self.node.val_area_mut(..old_len, arena), self.idx);
            *self.node.len_mut(arena) = (old_len - 1) as u16;
            ((k, v), self.left_edge(arena))
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    /// Splits the underlying node into three parts:
    ///
    /// - The node is truncated to only contain the edges and key-value pairs to the
    ///   left of this handle.
    /// - The key and value pointed to by this handle are extracted.
    /// - All the edges and key-value pairs to the right of this handle are put into
    ///   a newly allocated node.
    pub fn split(mut self, arena: &mut Arena<K, V>) -> SplitResult<'a, K, V, marker::Internal> {
        let old_len = self.node.len(arena);
        unsafe {
            let mut new_node = InternalNode::new(arena);
            let kv =
                self.split_leaf_data(unsafe { &mut (*arena.internal_node(new_node)).data }, arena);
            let new_len = usize::from(unsafe { (*arena.internal_node(new_node)).data.len });
            move_to_slice(
                self.node.edge_area_mut(self.idx + 1..old_len + 1, arena),
                unsafe { &mut (*arena.internal_node(new_node)).edges[..new_len + 1] },
            );

            let height = self.node.height;
            let right = NodeRef::from_new_internal(new_node, height, arena);

            SplitResult {
                left: self.node,
                kv,
                right,
            }
        }
    }
}

/// Represents a session for evaluating and performing a balancing operation
/// around an internal key-value pair.
pub(crate) struct BalancingContext<'a, K, V> {
    parent: Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV>,
    left_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    right_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    pub fn consider_for_balancing(self, arena: &Arena<K, V>) -> BalancingContext<'a, K, V> {
        let self1 = unsafe { ptr::read(&self) };
        let self2 = unsafe { ptr::read(&self) };
        BalancingContext {
            parent: self,
            left_child: self1.left_edge(arena).descend(arena),
            right_child: self2.right_edge(arena).descend(arena),
        }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Chooses a balancing context involving the node as a child, thus between
    /// the KV immediately to the left or to the right in the parent node.
    /// Returns an `Err` if there is no parent.
    /// Panics if the parent is empty.
    ///
    /// Prefers the left side, to be optimal if the given node is somehow
    /// underfull, meaning here only that it has fewer elements than its left
    /// sibling and than its right sibling, if they exist. In that case,
    /// merging with the left sibling is faster, since we only need to move
    /// the node's N elements, instead of shifting them to the right and moving
    /// more than N elements in front. Stealing from the left sibling is also
    /// typically faster, since we only need to shift the node's N elements to
    /// the right, instead of shifting at least N of the sibling's elements to
    /// the left.
    pub fn choose_parent_kv(
        self,
        arena: &Arena<K, V>,
    ) -> Result<LeftOrRight<BalancingContext<'a, K, V>>, Self> {
        match unsafe { ptr::read(&self) }.ascend(arena) {
            Ok(parent_edge) => match parent_edge.left_kv(arena) {
                Ok(left_parent_kv) => Ok(LeftOrRight::Left(BalancingContext {
                    parent: unsafe { ptr::read(&left_parent_kv) },
                    left_child: left_parent_kv.left_edge(arena).descend(arena),
                    right_child: self,
                })),
                Err(parent_edge) => match parent_edge.right_kv(arena) {
                    Ok(right_parent_kv) => Ok(LeftOrRight::Right(BalancingContext {
                        parent: unsafe { ptr::read(&right_parent_kv) },
                        left_child: self,
                        right_child: right_parent_kv.right_edge(arena).descend(arena),
                    })),
                    Err(_) => unreachable!("empty internal node"),
                },
            },
            Err(root) => Err(root),
        }
    }
}

impl<'a, K, V> BalancingContext<'a, K, V> {
    pub fn left_child_len(&self, arena: &Arena<K, V>) -> usize {
        self.left_child.len(arena)
    }

    pub fn right_child_len(&self, arena: &Arena<K, V>) -> usize {
        self.right_child.len(arena)
    }

    pub fn into_left_child(self) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.left_child
    }

    pub fn into_right_child(self) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.right_child
    }

    /// Returns whether merging is possible, i.e., whether there is enough room
    /// in a node to combine the central KV with both adjacent child nodes.
    pub fn can_merge(&self, arena: &Arena<K, V>) -> bool {
        self.left_child.len(arena) + 1 + self.right_child.len(arena) <= CAPACITY
    }
}

impl<'a, K: 'a, V: 'a> BalancingContext<'a, K, V> {
    /// Performs a merge and lets a closure decide what to return.
    fn do_merge<
        F: FnOnce(
            NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
            NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
        ) -> R,
        R,
    >(
        self,
        result: F,
        arena: &mut Arena<K, V>,
    ) -> R {
        let Handle {
            node: mut parent_node,
            idx: parent_idx,
            _marker,
        } = self.parent;
        let old_parent_len = parent_node.len(arena);
        let mut left_node = self.left_child;
        let old_left_len = left_node.len(arena);
        let mut right_node = self.right_child;
        let right_len = right_node.len(arena);
        let new_left_len = old_left_len + 1 + right_len;

        assert!(new_left_len <= CAPACITY);

        unsafe {
            *left_node.len_mut(arena) = new_left_len as u16;

            let parent_key = slice_remove(
                parent_node.key_area_mut(..old_parent_len, arena),
                parent_idx,
            );
            left_node
                .key_area_mut(old_left_len, arena)
                .write(parent_key);
            move_to_slice(
                right_node.key_area_mut(..right_len, arena),
                left_node.key_area_mut(old_left_len + 1..new_left_len, arena),
            );

            let parent_val = slice_remove(
                parent_node.val_area_mut(..old_parent_len, arena),
                parent_idx,
            );
            left_node
                .val_area_mut(old_left_len, arena)
                .write(parent_val);
            move_to_slice(
                right_node.val_area_mut(..right_len, arena),
                left_node.val_area_mut(old_left_len + 1..new_left_len, arena),
            );

            slice_remove(
                &mut parent_node.edge_area_mut(..old_parent_len + 1, arena),
                parent_idx + 1,
            );
            parent_node.correct_childrens_parent_links(parent_idx + 1..old_parent_len, arena);
            *parent_node.len_mut(arena) -= 1;

            if parent_node.height > 1 {
                // SAFETY: the height of the nodes being merged is one below the height
                // of the node of this edge, thus above zero, so they are internal.
                let mut left_node = left_node.reborrow_mut().cast_to_internal_unchecked();
                let mut right_node = right_node.cast_to_internal_unchecked();
                move_to_slice(
                    right_node.edge_area_mut(..right_len + 1, arena),
                    left_node.edge_area_mut(old_left_len + 1..new_left_len + 1, arena),
                );

                left_node.correct_childrens_parent_links(old_left_len + 1..new_left_len + 1, arena);

                arena.deallocate_internal_node(right_node.node);
            } else {
                match right_node.node {
                    LeafOrInternalId::Leaf(id) => arena.deallocate_leaf_node(id),
                    LeafOrInternalId::Internal(_) => unreachable!(),
                }
            }
        }
        result(parent_node, left_node)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns the shrunk parent node.
    ///
    /// Panics unless we `.can_merge()`.
    pub fn merge_tracking_parent(
        self,
        arena: &mut Arena<K, V>,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        self.do_merge(|parent, _child| parent, arena)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns that child node.
    ///
    /// Panics unless we `.can_merge()`.
    pub fn merge_tracking_child(
        self,
        arena: &mut Arena<K, V>,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.do_merge(|_parent, child| child, arena)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns the edge handle in that child node
    /// where the tracked child edge ended up,
    ///
    /// Panics unless we `.can_merge()`.
    pub fn merge_tracking_child_edge(
        self,
        track_edge_idx: LeftOrRight<usize>,
        arena: &mut Arena<K, V>,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        let old_left_len = self.left_child.len(arena);
        let right_len = self.right_child.len(arena);
        assert!(match track_edge_idx {
            LeftOrRight::Left(idx) => idx <= old_left_len,
            LeftOrRight::Right(idx) => idx <= right_len,
        });
        let child = self.merge_tracking_child(arena);
        let new_idx = match track_edge_idx {
            LeftOrRight::Left(idx) => idx,
            LeftOrRight::Right(idx) => old_left_len + 1 + idx,
        };
        unsafe { Handle::new_edge(child, new_idx, arena) }
    }

    /// Removes a key-value pair from the left child and places it in the key-value storage
    /// of the parent, while pushing the old parent key-value pair into the right child.
    /// Returns a handle to the edge in the right child corresponding to where the original
    /// edge specified by `track_right_edge_idx` ended up.
    pub fn steal_left(
        mut self,
        track_right_edge_idx: usize,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        self.bulk_steal_left(1, arena);
        unsafe { Handle::new_edge(self.right_child, 1 + track_right_edge_idx, arena) }
    }

    /// Removes a key-value pair from the right child and places it in the key-value storage
    /// of the parent, while pushing the old parent key-value pair onto the left child.
    /// Returns a handle to the edge in the left child specified by `track_left_edge_idx`,
    /// which didn't move.
    pub fn steal_right(
        mut self,
        track_left_edge_idx: usize,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        self.bulk_steal_right(1, arena);
        unsafe { Handle::new_edge(self.left_child, track_left_edge_idx, arena) }
    }

    /// This does stealing similar to `steal_left` but steals multiple elements at once.
    pub fn bulk_steal_left(&mut self, count: usize, arena: &Arena<K, V>) {
        assert!(count > 0);
        unsafe {
            let left_node = &mut self.left_child;
            let old_left_len = left_node.len(arena);
            let right_node = &mut self.right_child;
            let old_right_len = right_node.len(arena);

            // Make sure that we may steal safely.
            assert!(old_right_len + count <= CAPACITY);
            assert!(old_left_len >= count);

            let new_left_len = old_left_len - count;
            let new_right_len = old_right_len + count;
            *left_node.len_mut(arena) = new_left_len as u16;
            *right_node.len_mut(arena) = new_right_len as u16;

            // Move leaf data.
            {
                // Make room for stolen elements in the right child.
                slice_shr(right_node.key_area_mut(..new_right_len, arena), count);
                slice_shr(right_node.val_area_mut(..new_right_len, arena), count);

                // Move elements from the left child to the right one.
                move_to_slice(
                    left_node.key_area_mut(new_left_len + 1..old_left_len, arena),
                    right_node.key_area_mut(..count - 1, arena),
                );
                move_to_slice(
                    left_node.val_area_mut(new_left_len + 1..old_left_len, arena),
                    right_node.val_area_mut(..count - 1, arena),
                );

                // Move the left-most stolen pair to the parent.
                let k = left_node
                    .key_area_mut(new_left_len, arena)
                    .assume_init_read();
                let v = left_node
                    .val_area_mut(new_left_len, arena)
                    .assume_init_read();
                let (k, v) = self.parent.replace_kv(k, v, arena);

                // Move parent's key-value pair to the right child.
                right_node.key_area_mut(count - 1, arena).write(k);
                right_node.val_area_mut(count - 1, arena).write(v);
            }

            match (
                left_node.reborrow_mut().force(),
                right_node.reborrow_mut().force(),
            ) {
                (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                    // Make room for stolen edges.
                    slice_shr(right.edge_area_mut(..new_right_len + 1, arena), count);

                    // Steal edges.
                    move_to_slice(
                        left.edge_area_mut(new_left_len + 1..old_left_len + 1, arena),
                        right.edge_area_mut(..count, arena),
                    );

                    right.correct_childrens_parent_links(0..new_right_len + 1, arena);
                }
                (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                _ => unreachable!(),
            }
        }
    }

    /// The symmetric clone of `bulk_steal_left`.
    pub fn bulk_steal_right(&mut self, count: usize, arena: &Arena<K, V>) {
        assert!(count > 0);
        unsafe {
            let left_node = &mut self.left_child;
            let old_left_len = left_node.len(arena);
            let right_node = &mut self.right_child;
            let old_right_len = right_node.len(arena);

            // Make sure that we may steal safely.
            assert!(old_left_len + count <= CAPACITY);
            assert!(old_right_len >= count);

            let new_left_len = old_left_len + count;
            let new_right_len = old_right_len - count;
            *left_node.len_mut(arena) = new_left_len as u16;
            *right_node.len_mut(arena) = new_right_len as u16;

            // Move leaf data.
            {
                // Move the right-most stolen pair to the parent.
                let k = right_node.key_area_mut(count - 1, arena).assume_init_read();
                let v = right_node.val_area_mut(count - 1, arena).assume_init_read();
                let (k, v) = self.parent.replace_kv(k, v, arena);

                // Move parent's key-value pair to the left child.
                left_node.key_area_mut(old_left_len, arena).write(k);
                left_node.val_area_mut(old_left_len, arena).write(v);

                // Move elements from the right child to the left one.
                move_to_slice(
                    right_node.key_area_mut(..count - 1, arena),
                    left_node.key_area_mut(old_left_len + 1..new_left_len, arena),
                );
                move_to_slice(
                    right_node.val_area_mut(..count - 1, arena),
                    left_node.val_area_mut(old_left_len + 1..new_left_len, arena),
                );

                // Fill gap where stolen elements used to be.
                slice_shl(right_node.key_area_mut(..old_right_len, arena), count);
                slice_shl(right_node.val_area_mut(..old_right_len, arena), count);
            }

            match (
                left_node.reborrow_mut().force(),
                right_node.reborrow_mut().force(),
            ) {
                (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                    // Steal edges.
                    move_to_slice(
                        right.edge_area_mut(..count, arena),
                        left.edge_area_mut(old_left_len + 1..new_left_len + 1, arena),
                    );

                    // Fill gap where stolen edges used to be.
                    slice_shl(right.edge_area_mut(..old_right_len + 1, arena), count);

                    left.correct_childrens_parent_links(old_left_len + 1..new_left_len + 1, arena);
                    right.correct_childrens_parent_links(0..new_right_len + 1, arena);
                }
                (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                _ => unreachable!(),
            }
        }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
    pub fn forget_node_type(
        self,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx, arena) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge> {
    pub fn forget_node_type(
        self,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx, arena) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::KV> {
    pub fn forget_node_type(
        self,
        arena: &Arena<K, V>,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV> {
        unsafe { Handle::new_kv(self.node.forget_type(), self.idx, arena) }
    }
}

impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, Type> {
    /// Checks whether the underlying node is an `Internal` node or a `Leaf` node.
    pub fn force(
        self,
    ) -> ForceResult<
        Handle<NodeRef<BorrowType, K, V, marker::Leaf>, Type>,
        Handle<NodeRef<BorrowType, K, V, marker::Internal>, Type>,
    > {
        match self.node.force() {
            ForceResult::Leaf(node) => ForceResult::Leaf(Handle {
                node,
                idx: self.idx,
                _marker: PhantomData,
            }),
            ForceResult::Internal(node) => ForceResult::Internal(Handle {
                node,
                idx: self.idx,
                _marker: PhantomData,
            }),
        }
    }
}

impl<'a, K, V, Type> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, Type> {
    /// Unsafely asserts to the compiler the static information that the handle's node is a `Leaf`.
    pub unsafe fn cast_to_leaf_unchecked(
        self,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, Type> {
        let node = unsafe { self.node.cast_to_leaf_unchecked() };
        Handle {
            node,
            idx: self.idx,
            _marker: PhantomData,
        }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
    /// Move the suffix after `self` from one node to another one. `right` must be empty.
    /// The first edge of `right` remains unchanged.
    pub fn move_suffix(
        &mut self,
        right: &mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
        arena: &Arena<K, V>,
    ) {
        unsafe {
            let new_left_len = self.idx;
            let mut left_node = self.reborrow_mut().into_node();
            let old_left_len = left_node.len(arena);

            let new_right_len = old_left_len - new_left_len;
            let mut right_node = right.reborrow_mut();

            assert!(right_node.len(arena) == 0);
            assert!(left_node.height == right_node.height);

            if new_right_len > 0 {
                *left_node.len_mut(arena) = new_left_len as u16;
                *right_node.len_mut(arena) = new_right_len as u16;

                move_to_slice(
                    left_node.key_area_mut(new_left_len..old_left_len, arena),
                    right_node.key_area_mut(..new_right_len, arena),
                );
                move_to_slice(
                    left_node.val_area_mut(new_left_len..old_left_len, arena),
                    right_node.val_area_mut(..new_right_len, arena),
                );
                match (left_node.force(), right_node.force()) {
                    (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                        move_to_slice(
                            left.edge_area_mut(new_left_len + 1..old_left_len + 1, arena),
                            right.edge_area_mut(1..new_right_len + 1, arena),
                        );
                        right.correct_childrens_parent_links(1..new_right_len + 1, arena);
                    }
                    (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }
}

pub enum ForceResult<Leaf, Internal> {
    Leaf(Leaf),
    Internal(Internal),
}

/// Result of insertion, when a node needed to expand beyond its capacity.
pub(crate) struct SplitResult<'a, K, V, NodeType>
where
    NodeType: marker::IdForType<K, V>,
{
    // Altered node in existing tree with elements and edges that belong to the left of `kv`.
    pub left: NodeRef<marker::Mut<'a>, K, V, NodeType>,
    // Some key and value that existed before and were split off, to be inserted elsewhere.
    pub kv: (K, V),
    // Owned, unattached, new node with elements and edges that belong to the right of `kv`.
    pub right: NodeRef<marker::Owned, K, V, NodeType>,
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Leaf> {
    pub fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal> {
        SplitResult {
            left: self.left.forget_type(),
            kv: self.kv,
            right: self.right.forget_type(),
        }
    }
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Internal> {
    pub fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal> {
        SplitResult {
            left: self.left.forget_type(),
            kv: self.kv,
            right: self.right.forget_type(),
        }
    }
}

pub mod marker {
    use super::{InternalNode, LeafNode};
    use crate::arena::{Arena, Id};
    use core::marker::PhantomData;
    use std::ptr;

    pub enum Leaf {}
    pub enum Internal {}
    pub enum LeafOrInternal {}

    pub(crate) trait IdForType<K, V> {
        type Id: Copy;

        fn node_eq(a: Self::Id, b: Self::Id) -> bool;
        unsafe fn leaf_ptr(id: Self::Id, arena: &Arena<K, V>) -> *mut LeafNode<K, V>;
    }

    impl<K, V> IdForType<K, V> for Leaf {
        type Id = Id<super::LeafNode<K, V>>;

        fn node_eq(a: Self::Id, b: Self::Id) -> bool {
            a.eq(b)
        }

        unsafe fn leaf_ptr(id: Self::Id, arena: &Arena<K, V>) -> *mut LeafNode<K, V> {
            arena.leaf_node(id)
        }
    }

    impl<K, V> IdForType<K, V> for Internal {
        type Id = Id<super::InternalNode<K, V>>;

        fn node_eq(a: Self::Id, b: Self::Id) -> bool {
            a.eq(b)
        }

        unsafe fn leaf_ptr(id: Self::Id, arena: &Arena<K, V>) -> *mut LeafNode<K, V> {
            let node = arena.internal_node(id);
            ptr::addr_of_mut!((*node).data)
        }
    }

    impl<K, V> IdForType<K, V> for LeafOrInternal {
        type Id = super::LeafOrInternalId<K, V>;

        fn node_eq(a: Self::Id, b: Self::Id) -> bool {
            match (a, b) {
                (super::LeafOrInternalId::Leaf(a), super::LeafOrInternalId::Leaf(b)) => a.eq(b),
                (super::LeafOrInternalId::Internal(a), super::LeafOrInternalId::Internal(b)) => {
                    a.eq(b)
                }
                _ => false,
            }
        }

        unsafe fn leaf_ptr(id: Self::Id, arena: &Arena<K, V>) -> *mut LeafNode<K, V> {
            match id {
                super::LeafOrInternalId::Leaf(id) => Leaf::leaf_ptr(id, arena),
                super::LeafOrInternalId::Internal(id) => Internal::leaf_ptr(id, arena),
            }
        }
    }

    pub enum Owned {}
    pub enum Dying {}
    pub struct Immut<'a>(PhantomData<&'a ()>);
    pub struct Mut<'a>(PhantomData<&'a mut ()>);
    pub struct ValMut<'a>(PhantomData<&'a mut ()>);

    pub trait BorrowType {
        // If node references of this borrow type allow traversing to other
        // nodes in the tree, this constant can be evaluated. Thus reading it
        // serves as a compile-time assertion.
        const TRAVERSAL_PERMIT: () = ();
    }
    impl BorrowType for Owned {
        // Reject evaluation, because traversal isn't needed. Instead traversal
        // happens using the result of `borrow_mut`.
        // By disabling traversal, and only creating new references to roots,
        // we know that every reference of the `Owned` type is to a root node.
        const TRAVERSAL_PERMIT: () = panic!();
    }
    impl BorrowType for Dying {}
    impl<'a> BorrowType for Immut<'a> {}
    impl<'a> BorrowType for Mut<'a> {}
    impl<'a> BorrowType for ValMut<'a> {}

    pub enum KV {}
    pub enum Edge {}
}

/// Inserts a value into a slice of initialized elements followed by one uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T) {
    unsafe {
        let len = slice.len();
        debug_assert!(len > idx);
        let slice_ptr = slice.as_mut_ptr();
        if len > idx + 1 {
            ptr::copy(slice_ptr.add(idx), slice_ptr.add(idx + 1), len - idx - 1);
        }
        (*slice_ptr.add(idx)).write(val);
    }
}

/// Removes and returns a value from a slice of all initialized elements, leaving behind one
/// trailing uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
unsafe fn slice_remove<T>(slice: &mut [MaybeUninit<T>], idx: usize) -> T {
    unsafe {
        let len = slice.len();
        debug_assert!(idx < len);
        let slice_ptr = slice.as_mut_ptr();
        let ret = (*slice_ptr.add(idx)).assume_init_read();
        ptr::copy(slice_ptr.add(idx + 1), slice_ptr.add(idx), len - idx - 1);
        ret
    }
}

/// Shifts the elements in a slice `distance` positions to the left.
///
/// # Safety
/// The slice has at least `distance` elements.
unsafe fn slice_shl<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr.add(distance), slice_ptr, slice.len() - distance);
    }
}

/// Shifts the elements in a slice `distance` positions to the right.
///
/// # Safety
/// The slice has at least `distance` elements.
unsafe fn slice_shr<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr, slice_ptr.add(distance), slice.len() - distance);
    }
}

/// Moves all values from a slice of initialized elements to a slice
/// of uninitialized elements, leaving behind `src` as all uninitialized.
/// Works like `dst.copy_from_slice(src)` but does not require `T` to be `Copy`.
fn move_to_slice<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    assert!(src.len() == dst.len());
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}

#[cfg(test)]
mod tests;
