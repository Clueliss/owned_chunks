#![feature(
    negative_impls,
    vec_into_raw_parts,
    maybe_uninit_extra,
    maybe_uninit_uninit_array,
    test,
    generic_associated_types,
    array_from_fn
)]

//! A collection of iterators and traits that allow you to get _owned_ chunks
//! from collections (currently [`Vec`](std::vec::Vec) and [`array`](prim@array))
//!
//! # Example
//! ```rust
//! use owned_chunks::OwnedChunks;
//!
//! fn take_ownership(v: Vec<i32>) {
//!     // implementation
//! }
//!
//! for (ix, chunk) in vec![vec![1, 2], vec![3, 4], vec![5, 6]].owned_chunks(2).enumerate() {
//!     match ix {
//!         0 => assert_eq!(&[vec![1, 2], vec![3, 4]], chunk.as_slice()),
//!         1 => assert_eq!(&[vec![5, 6]], chunk.as_slice()),
//!         _ => panic!("no more chunks expected"),
//!     }
//!
//!     for vec in chunk {
//!         take_ownership(vec);
//!     }
//! }
//! ```

/// chunk iterators for [`arrays`](prim@array)
pub mod array;

/// chunk iterators for [`Vecs`](Vec)
pub mod vec;

/// A trait to get _owned_ chunks from a collection.
/// This is very similar to the [`slice::*chunks*`](slice::chunks) family of functions except that the chunks will
/// not be references/slices into the storage but iterators that yield the owned items inside it.
///
/// # Note
/// Although there exists an implementation of [`OwnedChunks`] for [`arrays`](prim@array) you should always [**\*1**]
/// prefer [`StaticOwnedChunks`] if possible, due to how this is implemented for them.
/// (See [`array::ArrayChunks#Implementation details`] for more information)
///
/// **\*1**: For small [`arrays`](prim@array) the performance penalty should be negligible so it is probably fine for those.
///
/// # Example
/// Demonstaration of simmilarity to slice functions
///
/// ```rust
/// use owned_chunks::OwnedChunks;
///
/// for (ix, chunk) in vec![1, 2, 3, 4, 5].owned_chunks(2).enumerate() {
///     let expected: &[i32] = match ix {
///         0 => &[1, 2],
///         1 => &[3, 4],
///         2 => &[5],
///         _ => panic!("no more chunks expected"),
///     };
///     assert_eq!(expected, chunk.as_slice());
/// }
/// ```
///
/// # Example
/// Ownership transfer
///
/// ```rust
/// use owned_chunks::OwnedChunks;
///
/// fn take_ownership(v: Vec<i32>) {
///     // some implementation
/// }
///
/// for chunk in vec![vec![1, 2, 3]; 10].owned_chunks(4) {
///     for vec in chunk {
///         take_ownership(vec);
///     }
/// }
/// ```
pub trait OwnedChunks: Sized {
    type Iter;
    fn owned_chunks(self, chunk_size: usize) -> Self::Iter;
}

/// A variant of [`OwnedChunks`] with const chunk size; this primarily exists to allow storage size
/// optimizations for types where storage size depends on a constant, like [`arrays`](prim@array). For further
/// information see the docs of [`array::ArrayChunks#Implementation details`].
///
/// # Example
/// ```rust
/// use owned_chunks::StaticOwnedChunks;
///
/// fn take_ownership(v: Vec<i32>) {
///     // some implementation
/// }
///
/// for chunk in [vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]].static_owned_chunks::<2>() {
///     for v in chunk {
///         take_ownership(v);
///     }
/// }
/// ```
///
pub trait StaticOwnedChunks: Sized {
    type Iter<const CHUNK_SZ: usize>;
    fn static_owned_chunks<const CHUNK_SZ: usize>(self) -> Self::Iter<CHUNK_SZ>;
}

impl<T, const N: usize> OwnedChunks for [T; N] {
    type Iter = array::ArrayChunks<T, N, N>;

    fn owned_chunks(self, chunk_size: usize) -> Self::Iter {
        array::ArrayChunks::new(self, chunk_size)
    }
}

impl<T, const N: usize> StaticOwnedChunks for [T; N] {
    type Iter<const CHUNK_SZ: usize> = array::ArrayChunks<T, N, CHUNK_SZ>;

    fn static_owned_chunks<const CHUNK_SZ: usize>(self) -> Self::Iter<CHUNK_SZ> {
        array::ArrayChunks::new(self, CHUNK_SZ)
    }
}

impl<T> OwnedChunks for Vec<T> {
    type Iter = vec::VecChunks<T>;

    fn owned_chunks(self, chunk_size: usize) -> Self::Iter {
        vec::VecChunks::new(self, chunk_size)
    }
}
