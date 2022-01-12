use std::{
    cmp::min,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::Range,
    rc::Rc,
};

unsafe fn drop_vec<T>(
    vec: &mut Rc<(*mut ManuallyDrop<T>, usize, usize)>,
    alive: &mut Range<usize>,
) {
    // SAFETY:
    // 1. we are only dropping elements from the alive section,
    //      so we can be sure that they have not been given out yet, and therefore we
    //      are responsible for dropping them
    // 2. by the alive invariant all indexes of alive must be valid indexes into the vec
    for ix in alive {
        ManuallyDrop::drop(&mut *vec.0.add(ix));
    }

    // SAFETY:
    // 1. the strong count is 1, therefore we are the only owner of the memory of the vec
    //      and are allowed to free it
    // 2. the raw parts were once a valid vec and have not changed since then,
    //      therefore we can construct a valid vec out of them
    // 3. the type is Vec<ManuallyDrop<T>> therefore Vec will no attempt to drop any elements
    //      for the second time
    // 4. dropping a tuple containing a pointer and to ints does nothing
    //      and therefore does not drop the vec twice
    if Rc::strong_count(vec) == 1 {
        drop(Vec::from_raw_parts(vec.0, vec.1, vec.2));
    }
}

/// An iterator that yields owned chunks for a [`Vec`]
pub struct VecChunks<T> {
    vec: Rc<(*mut ManuallyDrop<T>, usize, usize)>,
    chunk_size: usize,

    // INVARIANT:
    // 1. the whole range of alive must be valid indices into vec
    // 2. alive contains only those indices where the elements have not been given
    //      out or dropped and therefore are exclusively owned by us
    alive: Range<usize>,

    _phantom_t: PhantomData<T>,
    _phantom_vec: PhantomData<Vec<ManuallyDrop<T>>>,
}

/// A single chunk yielded by [`VecChunks`]
pub struct VecChunk<T> {
    vec: Rc<(*mut ManuallyDrop<T>, usize, usize)>,

    // INVARIANT:
    // 1. the whole range of alive must be valid indices into vec
    // 2. alive only contains those indices, where we are the exclusive owner
    //      and no element has been dropped
    alive: Range<usize>,

    _phantom_t: PhantomData<T>,
    _phantom_vec: PhantomData<Vec<ManuallyDrop<T>>>,
}

impl<T> VecChunks<T> {
    /// Constructs a new [`VecChunks`] iterator.
    ///
    /// # Note
    /// You should probably call [`OwnedChunks::owned_chunks`](crate::OwnedChunks::owned_chunks)
    /// on the [`Vec`] instead.
    pub fn new(v: Vec<T>, chunk_size: usize) -> Self {
        let len = v.len();

        // SAFETY:
        // ManuallyDrop is #[repr(transparent)] and therefore T can be transmuted to ManuallyDrop<T>
        // and by extension Vec<T> into Vec<ManuallyDrop<T>>
        let parts = unsafe { mem::transmute::<_, Vec<ManuallyDrop<T>>>(v) }.into_raw_parts();

        Self {
            vec: Rc::new(parts),
            alive: 0..len,
            chunk_size,
            _phantom_vec: PhantomData::default(),
            _phantom_t: PhantomData::default(),
        }
    }
}

impl<T> VecChunk<T> {
    /// returns a reference to the remaining elements of this iterator
    /// in the form of a slice
    ///
    /// # Example
    /// ```rust
    /// use owned_chunks::OwnedChunks;
    ///
    /// let mut chunks = vec![1, 2, 3, 4, 5].owned_chunks(3);
    /// let mut chunk = chunks.next().unwrap();
    /// let _ = chunk.next();
    ///
    /// assert_eq!(&[2, 3], chunk.as_slice());
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // SAFETY:
        // 1. `base` is a pointer inside of the alive section of our vec and points to the
        //      first element that has not been given out yet
        // 2. `len` is the offset from the start of the alive section to the end
        //
        // therefore we own every element in this section and can give a ref to the contiguous memory
        unsafe {
            let base = self.vec.0.add(self.alive.start);
            let len = self.alive.len();

            std::slice::from_raw_parts(&**base, len)
        }
    }

    /// returns a reference to the remaining elements of this iterator
    /// in the form of a slice
    ///
    /// # Example
    /// ```rust
    /// use owned_chunks::OwnedChunks;
    ///
    /// let mut chunks = vec![1, 2, 3, 4, 5].owned_chunks(3);
    /// let mut chunk = chunks.next().unwrap();
    /// let _ = chunk.next();
    ///
    /// assert_eq!(&mut [2, 3], chunk.as_mut_slice());
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: see SAFETY of as_slice
        unsafe {
            let base = self.vec.0.add(self.alive.start);
            let len = self.alive.len();

            std::slice::from_raw_parts_mut(&mut **base, len)
        }
    }
}

impl<T> !Send for VecChunks<T> {}
impl<T> !Sync for VecChunks<T> {}

impl<T> !Send for VecChunk<T> {}
impl<T> !Sync for VecChunk<T> {}

impl<T> Drop for VecChunks<T> {
    fn drop(&mut self) {
        unsafe {
            drop_vec(&mut self.vec, &mut self.alive);
        }
    }
}

impl<T> Drop for VecChunk<T> {
    fn drop(&mut self) {
        unsafe {
            drop_vec(&mut self.vec, &mut self.alive);
        }
    }
}

impl<T> Iterator for VecChunks<T> {
    type Item = VecChunk<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.alive.is_empty() {
            None
        } else {
            let range_start = self.alive.start;
            let range_end = min(range_start + self.chunk_size, self.alive.end);
            self.alive.start = range_end;

            Some(VecChunk {
                vec: self.vec.clone(),
                alive: range_start..range_end,
                _phantom_t: PhantomData::default(),
                _phantom_vec: PhantomData::default(),
            })
        }
    }
}

impl<T> Iterator for VecChunk<T>
where
    T: Sized,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.alive
            .next()
            .map(|ix| ManuallyDrop::into_inner(unsafe { self.vec.0.add(ix).read() }))
    }
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::VecChunks;
    use test::Bencher;

    #[test]
    fn basic_test() {
        let v = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];

        for (ix, c) in VecChunks::new(v, 4).enumerate() {
            let c = c.as_slice();

            let expected: &[i32] = match ix {
                0 => &[1, 2, 3, 4],
                1 => &[5, 6, 7, 8],
                2 => &[9, 10, 11, 12],
                3 => &[13, 14],
                _ => panic!("expected no more chunks"),
            };

            assert_eq!(expected, c);
        }
    }

    #[test]
    fn repeated_as_slice() {
        let v: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        for (ix, mut c) in VecChunks::new(v, 4).enumerate() {
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
        let v = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];

        let chunk = {
            let mut chunks = VecChunks::new(v, 4);
            chunks.next().unwrap()
        };

        assert_eq!(&[1, 2, 3, 4], chunk.as_slice());
    }

    fn make_vec() -> Vec<i32> {
        let mut i = 0;
        Vec::from_iter(std::iter::from_fn(move || {
            if i < 500 {
                Some({
                    let tmp = i;
                    i += 1;
                    tmp
                })
            } else {
                None
            }
        }))
    }

    #[bench]
    fn repeated_drain(b: &mut Bencher) {
        b.iter(move || {
            let mut v = make_vec();
            let mut res: Vec<i32> = Vec::new();

            while !v.is_empty() {
                let chunk = v.drain(..std::cmp::min(4, v.len()));
                res.push(chunk.sum());
            }
        });
    }

    #[bench]
    fn chunk_iter(b: &mut Bencher) {
        b.iter(move || {
            let v = make_vec();
            let mut res: Vec<i32> = Vec::new();

            for chunk in VecChunks::new(v, 4) {
                res.push(chunk.sum());
            }
        });
    }
}
