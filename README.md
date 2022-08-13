# StRing Buffer

StRing Buffer is a fixed sized UTF-8 String. It uses a ring buffer that overwrites
the front when the buffer is full.

---
![GitHub Workflow Status](https://img.shields.io/github/workflow/status/Teh-Bobo/StRingBuffer/Rust)
![docs.rs](https://img.shields.io/docsrs/st_ring_buffer)
![Crates.io](https://img.shields.io/crates/l/st_ring_buffer)
![Crates.io](https://img.shields.io/crates/v/st_ring_buffer)

## Usage

You can create a buffer on the stack using a constant size ```StRingBuffer::<SIZE>::new()``` or
on the heap using a variable size ```HeapStRingBuffer::new(SIZE)```.

Both types of buffer implement the ```StringBuffer``` trait. The trait has a ```.push_str()``` and ```.push_char()``` method to add data to the buffer.

To read data is a bit more complicated. The ```.as_slices()``` method returns two ```&str```. If the 
buffer reaches the end of its alloted size and loops back then the first ```&str``` will contain the string
data from the start to the end of the buffer and the second string will contain the rest of the data.

If you want all the data in one ```&str``` then call ```.align()``` on the buffer first. This will ensure that all the
data is returned to the first ```&str``` from ```.as_slices()```.

## Examples
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

## Time Complexity
Pushing data into the buffer is always constant time. Aligning the buffer is also done in constant
time using, at most, two memcopys. The ```StringBuffer``` trait also provides ```align_no_alloc``` if you
would like to perform the alignment using O(n) time, where 'n' is the length of the shortest leg of the buffer.

## No Std
This library is nostd compatible by default.

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