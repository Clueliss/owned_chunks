# owned_chunks

A collection of iterators and traits that allow you to get _owned_ chunks
from collections 
(currently [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) 
and [`array`](https://doc.rust-lang.org/std/primitive.array.html))

## Example
```rust
use owned_chunks::OwnedChunks;

fn take_ownership(v: Vec<i32>) {
    // implementation
}

for (ix, chunk) in vec![vec![1, 2], vec![3, 4], vec![5, 6]].owned_chunks(2).enumerate() {
    match ix {
        0 => assert_eq!(&[vec![1, 2], vec![3, 4]], chunk.as_slice()),
        1 => assert_eq!(&[vec![5, 6]], chunk.as_slice()),
        _ => panic!("no more chunks expected"),
    }

    for vec in chunk {
        take_ownership(vec);
    }
}
```

License: GPL-2.0-or-later
