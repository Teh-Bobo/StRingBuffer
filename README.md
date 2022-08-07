# StRing Buffer
A fixed sized string using a ring buffer. Once full, the front of the 
buffer is overwritten ensuring as writes are done in constant time.
---
```rust
use st_ring_buffer::{HeapStRingBuffer, StRingBuffer, StringBuffer};

fn main() {
  // On the heap
  let mut heap = HeapStRingBuffer::new(5);
  heap.push_str("ABCDE");
  assert_eq!(heap.as_slices().0, "ABCDE");
  heap.push_str("FG");
  let (first, second) = heap.as_slices();
  assert_eq!(first, "CDE");
  assert_eq!(second, "FG");

  // On the stack
  let mut stack = StRingBuffer::<5>::new();
  stack.push_str("ABCDE");
  stack.push_char('F');
  stack.align();
  assert_eq!(stack.as_slices().0, "BCDEF");
}
```

## License

Licensed under either of

* Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.