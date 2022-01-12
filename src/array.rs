use std::{
    cmp::min,
    mem::{self, MaybeUninit},
    ops::Range,
    ptr,
};

/// An iterator that yields owned chunks from an [`array`]
///
/// # Implementation details
/// As you can see this type is both parameterized by `N` and `CHUNK_SZ`
/// where `N` is the size of the [`array`] and `CHUNK_SZ` is _the size of the storage inside individual [`ArrayChunk`]s_.
///
/// That means that each [`ArrayChunk`] currently in use (e.g. not dropped) will consume
/// at least ```CHUNK_SZ * ```[`size_of`](core::mem::size_of)```::<T>()``` bytes on the stack.
///
/// By extension this means you should (if you are able to) choose the `CHUNK_SZ` that is the smallest
/// (or at least close to the smallest) possible chunk size that still fits a chunk.
///
/// The implementation of [`OwnedChunks`](crate::OwnedChunks) for [`arrays`](array) *does not* do this, since it simply can't
/// (because of lack of additional information),
/// it will always choose ```CHUNK_SZ == N``` since it is always safe to do so.
pub struct ArrayChunks<T, const N: usize, const CHUNK_SZ: usize> {
    array: [MaybeUninit<T>; N],
    chunk_size: usize,

    // INVARIANT:
    // 1. the whole range of alive must be valid indices into array
    // 2. alive contains only those indices where the elements have not been given
    //      out or dropped and therefore are exclusively owned by us
    alive: Range<usize>,
}

/// A single chunk yielded by [`ArrayChunks`]
pub struct ArrayChunk<T, const CHUNK_SZ: usize> {
    array: [MaybeUninit<T>; CHUNK_SZ],

    // INVARIANT:
    // 1. the whole range of alive must be valid indices into array
    // 2. alive only contains those indices, where we are the exclusive owner
    //      and no element has been dropped
    alive: Range<usize>,
}

impl<T, const N: usize, const CHUNK_SZ: usize> ArrayChunks<T, N, CHUNK_SZ> {
    /// Constructs a new [`ArrayChunks`] iterator.
    ///
    /// # Note
    /// You should probably call [`StaticOwnedChunks::static_owned_chunks`](crate::StaticOwnedChunks::static_owned_chunks)
    /// or [`OwnedChunks::owned_chunks`](crate::OwnedChunks::owned_chunks) on the [`array`] instead.
    ///
    /// # Panics
    ///
    /// - if `CHUNK_SZ` is smaller than `chunk_size` since that would mean that chunks cannot fit inside
    /// the chunk storage
    ///
    /// - if `CHUNK_SZ` is greater than `N` since `N` is a known constant and every
    /// possible chunk of an [`array`] of size `N` would fit in a storage of size `N`
    pub fn new(array: [T; N], chunk_size: usize) -> Self {
        assert!(
            CHUNK_SZ <= N,
            "it does not make sense to choose a storage size of greater than N, \
            since that is the minimum, statically known upper bound"
        );

        assert!(
            CHUNK_SZ >= chunk_size,
            "not enough storage for requested dynamic chunksize"
        );

        // SAFETY:
        // MaybeUninit is #[repr(transparent)] and therefore T can be transmuted to MaybeUninit<T>
        // and by extension [T; N] into [MaybeUninit<T>; N]
        // TODO: use transmute instead of transmute_copy when it works with const generics
        let copy = unsafe { mem::transmute_copy(&array) };
        mem::forget(array);

        Self {
            alive: 0..N,
            array: copy,
            chunk_size,
        }
    }
}

impl<T, const CHUNK_SZ: usize> ArrayChunk<T, CHUNK_SZ> {
    /// returns a reference to the remaining elements of this iterator
    /// in the form of a slice
    ///
    /// # Example
    /// ```rust
    /// use owned_chunks::StaticOwnedChunks;
    ///
    /// let mut chunks = [1, 2, 3, 4, 5].static_owned_chunks::<3>();
    /// let mut chunk = chunks.next().unwrap();
    /// let _ = chunk.next();
    ///
    /// assert_eq!(&[2, 3], chunk.as_slice());
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // SAFETY:
        // 1. by the alive invariant every element must be exclusively owned by us and not dropped
        //      and therefore we can give out a ref to the contiguous memory section
        // 2. MaybeUninit<T> is #[repr(transparent)] and therefore a pointer to it is also a valid
        //      pointer to a T
        unsafe { &*(&self.array[self.alive.clone()] as *const [MaybeUninit<T>] as *const [T]) }
    }

    /// returns a reference to the remaining elements of this iterator
    /// in the form of a slice
    ///
    /// # Example
    /// ```rust
    /// use owned_chunks::StaticOwnedChunks;
    ///
    /// let mut chunks = [1, 2, 3, 4, 5].static_owned_chunks::<3>();
    /// let mut chunk = chunks.next().unwrap();
    /// let _ = chunk.next();
    ///
    /// assert_eq!(&mut [2, 3], chunk.as_mut_slice());
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: see SAFETY of as_slice
        unsafe { &mut *(&mut self.array[self.alive.clone()] as *mut [MaybeUninit<T>] as *mut [T]) }
    }
}

impl<T, const N: usize, const CHUNK_SZ: usize> Drop for ArrayChunks<T, N, CHUNK_SZ> {
    fn drop(&mut self) {
        // SAFETY:
        // alive contains exactly the indices to the elements that have not been moved out yet and
        // still need to be dropped
        unsafe {
            ptr::drop_in_place(&mut self.array[self.alive.clone()]);
        }
    }
}

impl<T, const CHUNK_SZ: usize> Drop for ArrayChunk<T, CHUNK_SZ> {
    fn drop(&mut self) {
        // SAFETY:
        // as_mut_slice returns a slice to exactly the elements that have not been moved
        // out yet and that still need to be dropped
        unsafe {
            ptr::drop_in_place(self.as_mut_slice());
        }
    }
}

impl<T, const N: usize, const CHUNK_SZ: usize> Iterator for ArrayChunks<T, N, CHUNK_SZ> {
    type Item = ArrayChunk<T, CHUNK_SZ>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.alive.is_empty() {
            None
        } else {
            let chunk_start = self.alive.start;
            let chunk_end = min(chunk_start + self.chunk_size, self.alive.end);
            self.alive.start = chunk_end;
            let chunk_len = chunk_end - chunk_start;

            let mut chunk = ArrayChunk {
                array: MaybeUninit::uninit_array(),
                alive: 0..chunk_len,
            };

            // SAFETY:
            // 1. chunk_start..chunk_end lies fully in the alive section of the array
            //      and therefore has not been given out to anyone and contains valid objects
            //      therefore it is ok to transfer ownership
            // 2. self.array and chunk.array are contained in distinct objects an therefore cannot
            //      overlap
            unsafe {
                ptr::copy_nonoverlapping(
                    self.array.as_ptr().add(chunk_start),
                    chunk.array.as_mut_ptr(),
                    chunk_len,
                );
            }
            Some(chunk)
        }
    }
}

impl<T, const CHUNK_SZ: usize> Iterator for ArrayChunk<T, CHUNK_SZ> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // ix is in the alive section of the array and therefore must:
        //      1. be a valid index
        //      2. be initialized, and not been given out to anyone else
        self.alive
            .next()
            .map(|ix| unsafe { self.array.get_unchecked(ix).assume_init_read() })
    }
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::ArrayChunks;
    use test::Bencher;

    fn make_array<const N: usize>() -> [usize; N] {
        core::array::from_fn(|i| i + 1)
    }

    #[bench]
    fn basic_test(b: &mut Bencher) {
        const N: usize = 32;

        b.iter(|| {
            let v = make_array::<N>();
            let v2 = v.clone();

            for (ix, c) in ArrayChunks::<_, N, 4>::new(v, 4).enumerate() {
                let c = c.as_slice();

                let expected = &v2[ix * 4..(ix + 1) * 4];
                assert_eq!(expected, c);
            }
        });
    }

    #[bench]
    fn dyamic_chunksz(b: &mut Bencher) {
        const N: usize = 32;

        b.iter(|| {
            let v = make_array::<N>();
            let v2 = v.clone();

            for (ix, c) in ArrayChunks::<_, N, N>::new(v, 4).enumerate() {
                let c = c.as_slice();

                let expected = &v2[ix * 4..(ix + 1) * 4];
                assert_eq!(expected, c);
            }
        });
    }

    #[test]
    fn repeated_as_slice() {
        let v: [i32; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        for (ix, mut c) in ArrayChunks::<_, 10, 4>::new(v, 4).enumerate() {
            match ix {
                0 => {
                    assert_eq!(&[1, 2, 3, 4], c.as_slice());
                    assert_eq!(Some(1), c.next());

                    assert_eq!(&[2, 3, 4], c.as_slice());
                    assert_eq!(Some(2), c.next());

                    assert_eq!(&[3, 4], c.as_slice());
                    assert_eq!(Some(3), c.next());

                    assert_eq!(&[4], c.as_slice());
                    assert_eq!(Some(4), c.next());

                    assert_eq!(&[] as &[i32], c.as_slice());
                    assert_eq!(None, c.next());
                }
                1 => {
                    assert_eq!(&[5, 6, 7, 8], c.as_slice());
                    assert_eq!(Some(5), c.next());

                    assert_eq!(&[6, 7, 8], c.as_slice());
                    assert_eq!(Some(6), c.next());

                    assert_eq!(&[7, 8], c.as_slice());
                    assert_eq!(Some(7), c.next());

                    assert_eq!(&[8], c.as_slice());
                    assert_eq!(Some(8), c.next());

                    assert_eq!(&[] as &[i32], c.as_slice());
                    assert_eq!(None, c.next());
                }
                2 => {
                    assert_eq!(&[9, 10], c.as_slice());
                    assert_eq!(Some(9), c.next());

                    assert_eq!(&[10], c.as_slice());
                    assert_eq!(Some(10), c.next());

                    assert_eq!(&[] as &[i32], c.as_slice());
                    assert_eq!(None, c.next());
                }
                _ => panic!("expected no more chunks"),
            }
        }
    }

    #[test]
    fn drop_iter_but_not_chunk() {
        let v = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];

        let chunk = {
            let mut chunks = ArrayChunks::<_, 14, 4>::new(v, 4);
            chunks.next().unwrap()
        };

        assert_eq!(&[1, 2, 3, 4], chunk.as_slice());
    }
}
