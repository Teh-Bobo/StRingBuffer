# StRing Buffer

StRing Buffer is a fixed sized UTF-8 String. It uses a ring buffer that overwrites
the front when the buffer is full.

---
[![GitHub Workflow Status](https://img.shields.io/github/workflow/status/Teh-Bobo/StRingBuffer/Rust)](https://github.com/Teh-Bobo/StRingBuffer/actions)
[![docs.rs](https://img.shields.io/docsrs/st_ring_buffer)](https://docs.rs/st_ring_buffer/0.2.0/st_ring_buffer/)
![Crates.io](https://img.shields.io/crates/l/st_ring_buffer)
[![Crates.io](https://img.shields.io/crates/v/st_ring_buffer)](https://crates.io/crates/st_ring_buffer)

## Usage

You can create a buffer on the stack using a constant size ```StRingBuffer::<SIZE>::new()``` or
on the heap using a variable size ```HeapStRingBuffer::new(SIZE)```.

Both types of buffer implement the ```StringBuffer``` trait. The trait has a ```.push_str()``` and ```.push_char()``` method to add data to the buffer.

To read data is a bit more complicated. The ```.as_slices()``` method returns two ```&str```. If the 
buffer reaches the end of its allotted size and loops back then the first ```&str``` will contain the string
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
  //as_slices() returns (&str, &str). If the buffer does not loop around the capacity then the second &str is empty.  
  assert_eq!(heap.as_slices().0, "ABCDE");
  //"FG" loops around to the front of the buffer, overwriting "AB"
  heap.push_str("FG");
  let (first, second) = heap.as_slices();
  assert_eq!(first, "CDE");
  assert_eq!(second, "FG");

  // On the stack
  let mut stack = StRingBuffer::<5>::new();
  stack.push_str("ABCDE");
  //'F' overwrites 'A', making the buffer loop around the capacity
  stack.push_char('F');
  //align the buffer so everything fits in one &str
  stack.align();
  assert_eq!(stack.as_slices().0, "BCDEF");
}
```

## Time Complexity
Pushing data into the buffer is always constant time. Aligning the buffer is also done in constant
time using, at most, two memcopys; however, it does allocate a temporary buffer that is the same size as the shortest
&str returned by ```as_slices()```. The ```StringBuffer``` trait also provides ```align_no_alloc``` if you
would like to perform the alignment without allocating a temporary buffer, but using O(n) time, where 'n' is the length 
of the shortest leg of the buffer.

## Features
Optional support for [Serde](https://docs.rs/serde/latest/serde/index.html) is included. 

### No Std
This library is nostd compatible by default. A ```std``` feature exists to add 
[std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html) to the ```StringBufferError``` type.

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