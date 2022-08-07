#![no_std]
#![deny(missing_docs)]

//! A ring buffer specialization for strings. The crate provides two versions of the buffer and a
//! [`StringBuffer`](StringBuffer) trait they both implement. [`StRingBuffer`](StRingBuffer) is a
//! stack allocated version using const generics. [`HeapStRingBuffer`](HeapStRingBuffer) is a heap
//! allocated version.
//!
//! When full these buffers both operate by overwriting the current head. All operations happen
//! in constant time except where explicitly noted.

extern crate alloc;

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::Formatter;
use core::iter::Chain;
use core::str::{Chars, from_utf8_unchecked};

/// A buffer specializing in holding data for a string. Pushing data to the buffer will not fail nor
/// panic. When full, the end of the data overwrites the start, while keeping the integrity of the
/// underlying utf-8 data.
pub trait StringBuffer {
    /// Adds a char to the buffer. Overwrites the start if the buffer is full.
    ///
    /// This will never panic nor fail. However, if the length of the char in utf-8 exceeds the
    /// length of the buffer then the buffer will be emptied.
    fn push_char(&mut self, c: char);

    /// Adds a &str to the buffer. Overwrites the start if the buffer is full.
    ///
    /// This will never panic nor fail.
    fn push_str(&mut self, s: &str) {
        s.chars().for_each(|c| self.push_char(c));
    }

    /// Get a reference to the two buffer segments in order.
    ///
    /// If the current data fits entirely in the buffer, and it is aligned, then the second
    /// reference will be an empty &str.
    fn as_slices(&self) -> (&str, &str);

    /// Copies data as required to make the head the start of the buffer. This allocates a temporary
    /// buffer the size of the smaller &str given by [`as_slices`](StringBuffer::as_slices).
    ///
    /// This is required to represent the entire buffer as a single &str.
    fn align(&mut self);

    /// Aligns the head of the buffer to the start via rotation. Compared to
    /// [`align`](StringBuffer::align) this function does not allocate any memory; however, it works
    /// in O([`buffer.len()`](StringBuffer::len)) time.
    ///
    /// This is required to represent the entire buffer as a single &str.
    fn align_no_alloc(&mut self);

    /// Returns the length of this buffer, in bytes, not chars or graphemes
    fn len(&self) -> usize;

    /// Returns true if there is no data in the buffer.
    fn is_empty(&self) -> bool;

    /// The number of bytes this buffer can hold. Not the number of chars or graphemes.
    fn capacity(&self) -> usize;

    /// Returns an iterator over the characters in the buffer. This includes both slices, in order,
    /// if the buffer is currently split.
    fn chars(&self) -> Chain<Chars<'_>, Chars<'_>> {
        let (front, back) = self.as_slices();
        front.chars().chain(back.chars())
    }

    /// Empties the buffer
    fn clear(&mut self);
}

/// An implementation of [`StringBuffer`](StringBuffer) using const generics to store its data on
/// the stack.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct StRingBuffer<const SIZE: usize> {
    data: [u8; SIZE],
    state: State,
}

/// An implementation of [`StringBuffer`](StringBuffer) that stores its data on the heap.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct HeapStRingBuffer {
    data: Box<[u8]>,
    state: State,
}

macro_rules! impl_buffer_trait {
() => {
        fn push_char(&mut self, c: char) {
            let char_len = c.len_utf8();
            let slice = match char_len.cmp(&self.capacity()) {
                Ordering::Less => self.state.get_char_slice(char_len, &mut self.data),
                Ordering::Equal => {
                    self.state = State::Straight {count: char_len };
                    &mut self.data
                }
                Ordering::Greater => {
                    self.clear();
                    return;
                },
            };
            c.encode_utf8(slice);
        }

        fn as_slices(&self) -> (&str, &str) {
            unsafe {
                match self.state {
                    State::Empty => ("", ""),
                    State::Straight { count } => (from_utf8_unchecked(&self.data[0..count]),""),
                    State::Looped { first, end_offset, next } => {
                        (from_utf8_unchecked(&self.data[first..(self.capacity() - end_offset as usize)]),
                         from_utf8_unchecked(&self.data[0..next]))
                    }
                }
            }
        }

        fn align(&mut self) {
            match self.state {
                State::Empty | State::Straight { .. } => {}
                State::Looped { first, end_offset, next } => {
                    let copy = self.data[0..next].to_owned();
                    let len = self.len();
                    let capacity_minus_offset = self.capacity() - end_offset as usize;
                    let first_len = capacity_minus_offset - first;
                    self.data.copy_within(first..capacity_minus_offset, 0);
                    self.data[first_len..].copy_from_slice(&copy);
                    self.state = State::Straight {count: len};
                }
            }
        }

        fn align_no_alloc(&mut self) {
            match self.state {
                State::Empty | State::Straight { .. } => {}
                State::Looped { first, end_offset, next } => {
                    let len = if next == first {
                        let len = self.data.len() - end_offset as usize;
                        self.data[..len].rotate_left(first);
                        len
                    } else {
                        let first_len = self.data.len() - end_offset as usize;
                        let second_len = next;
                        self.data.rotate_left(first);
                        self.data[first_len..].rotate_left(end_offset as usize);
                        first_len + second_len
                    };
                    self.state = State::Straight {count: len};
                }
            }
        }

        fn len(&self) -> usize {
            match self.state {
                State::Empty => 0,
                State::Straight { count } => count,
                State::Looped { first, end_offset, next } => {
                    if next > first {
                        self.capacity() - end_offset as usize
                    } else {
                        self.capacity() - end_offset as usize - (first - next)
                    }
                }
            }
        }

        fn is_empty(&self) -> bool {
            matches!(self.state, State::Empty)
        }

        fn capacity(&self) -> usize {
            self.data.len()
        }

        fn clear(&mut self) {
            self.state = State::Empty;
        }
    }
}

impl<const SIZE: usize> StringBuffer for StRingBuffer<SIZE> {
    impl_buffer_trait!();
}

impl<const SIZE: usize> core::fmt::Display for StRingBuffer<SIZE> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let (first, second) = self.as_slices();
        write!(f, "({first}, {second})")
    }
}

impl<const SIZE: usize> From<[u8; SIZE]> for StRingBuffer<SIZE> {
    fn from(data: [u8; SIZE]) -> Self {
        StRingBuffer {
            data,
            state: State::Empty,
        }
    }
}

impl<const SIZE: usize> StRingBuffer<SIZE> {

    /// Creates a new StRingBuffer on the stack using the const generic size.
    pub const fn new() -> Self {
        Self {
            data: [0; SIZE],
            state: State::Empty,
        }
    }
}

impl StringBuffer for HeapStRingBuffer {
    impl_buffer_trait!();
}

impl core::fmt::Display for HeapStRingBuffer {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let (first, second) = self.as_slices();
        write!(f, "({first}, {second})")
    }
}

impl From<String> for HeapStRingBuffer {
    fn from(s: String) -> Self {
        let count = s.len();
        let data = s.into_boxed_str().into_boxed_bytes();
        HeapStRingBuffer {
            data,
            state: State::Straight { count },
        }
    }
}

impl TryFrom<Vec<u8>> for HeapStRingBuffer {
    type Error = alloc::string::FromUtf8Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        Ok(String::from_utf8(value)?.into())
    }
}

impl TryFrom<Box<[u8]>> for HeapStRingBuffer {
    type Error = alloc::string::FromUtf8Error;

    fn try_from(value: Box<[u8]>) -> Result<Self, Self::Error> {
        Ok(String::from_utf8(value.into())?.into())
    }
}

impl HeapStRingBuffer {

    /// Creates a new HeapStRingBuffer on the heap using the given size.
    pub fn new(size: usize) -> Self {
        HeapStRingBuffer{
            data: vec![0; size].into_boxed_slice(),
            state: Default::default(),
        }
    }
}

const fn is_utf8_char_boundary(b: u8) -> bool {
    // Stolen from core::num::mod, which keeps this function private
    // This is bit magic equivalent to: b < 128 || b >= 192
    (b as i8) >= -0x40
}

fn next_char_boundary(data: &[u8], start: usize) -> Option<usize> {
    data[start.min(data.len())..].iter()
        .enumerate()
        .find(|(_, b)| is_utf8_char_boundary(**b))
        .map(|(i, _)| i + start)
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum State {
    #[default]
    Empty,
    Straight{count: usize},
    Looped{first: usize, end_offset: u8, next: usize}
}

impl State {
    fn get_char_slice<'a>(&'a mut self, char_len: usize, data: &'a mut [u8]) -> &'a mut [u8] {
        match self {
            State::Empty => {
                *self = State::Straight { count: char_len };
                data
            }
            State::Straight { count } => {
                if *count + char_len > data.len() {
                    //char doesn't fit in straight, need to loop
                    let end_offset = (data.len() - *count).try_into().unwrap();
                    let first = next_char_boundary(&data[..*count], char_len);
                    *self = match first {
                        //nothing found, this should only happen if the buffer
                        //is small and adding this char overlaps the end and causes
                        //the char to be written from the start--clearing the existing buffer
                        None => State::Straight { count: char_len },
                        //new first found within straight
                        Some(first) =>
                            State::Looped {
                                first,
                                end_offset,
                                next: char_len,
                            },
                    };
                    data
                } else {
                    //char fits as-is
                    *count += char_len;
                    &mut data[(*count - char_len)..*count]
                }
            }
            State::Looped { first, end_offset, next } => {
                if *first - *next < char_len {
                    //first needs to move
                    let new_first = next_char_boundary(data, *first + char_len);
                    match new_first {
                        None => {
                            //first needs to loop back to the start (back to straight)
                            *self = State::Straight {count: *next};
                            // head down the straight pipeline
                            self.get_char_slice(char_len, data)
                        }
                        Some(nf) => {
                            let next_copy = *next;
                            let new_next = next_copy + char_len;
                            if new_next > data.len() - *end_offset as usize {
                                //char insert overwrites end offset
                                *end_offset = (data.len() - new_next).try_into().unwrap();
                            }
                            *next = new_next;
                            *first = nf;
                            &mut data[next_copy..new_next]
                        }
                    }
                } else {
                    //big enough gap between first and next
                    let next_copy = *next;
                    *next = next_copy + char_len;
                    &mut data[next_copy..(next_copy + char_len)]
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use alloc::string::ToString;
    use test_case::test_case;

    use crate::{next_char_boundary, StRingBuffer, StringBuffer};
    use crate::HeapStRingBuffer;

    const SMALL_SIZE: usize = 5;
    const SMALL_CONST: StRingBuffer<SMALL_SIZE> = StRingBuffer::new();

    fn small_heap() -> HeapStRingBuffer{
        HeapStRingBuffer::new(SMALL_SIZE)
    }

    fn verify_empty(test: &impl StringBuffer) {
        verify(test, 0, "", "");
    }

    fn verify(test: &impl StringBuffer, expected_len: usize, first: &str, second: &str) {
        assert_eq!(test.len(), expected_len);
        assert_eq!(test.is_empty(), expected_len == 0);
        assert_eq!(test.as_slices().0, first);
        assert_eq!(test.as_slices().1, second);
        first.chars().chain(second.chars()).zip(test.chars()).for_each(|(expected, given)|assert_eq!(expected, given));
    }

    #[test_case(& mut SMALL_CONST.clone())]
    #[test_case(& mut small_heap())]
    fn basic(test: &mut impl StringBuffer){
        verify_empty(test);
        test.push_char('A');
        verify(test, 1, "A", "");

        test.push_str("BCDE");
        verify(test, 5, "ABCDE", "");

        assert_eq!(SMALL_SIZE, 5);
        test.push_char('X');
        verify(test, 5, "BCDE", "X");

        test.align();
        verify(test, 5, "BCDEX", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 3 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(3))]
    fn two_byte(test: &mut impl StringBuffer) {
        verify_empty(test);
        assert_eq!(test.capacity(), 3);
        test.push_str("ABC");
        //[^A, B, C*]
        assert_eq!(test.len(), 3);
        test.push_char('Ɵ'); //Latin Capital Letter O with Middle Tilde (0xC6 0x9F in UTF-8)
        //[0xC6, 0x9F, *^C]
        verify(test, 3, "C", "Ɵ");

        test.push_str("XY");
        //[Y*, _, ^X]
        verify(test, 2, "X", "Y");

        //split on buffer end
        test.push_char('Z');
        //[Y, Z, *^X]
        assert_eq!(test.len(), 3);
        test.push_char('Ɵ');
        //[^0xC6, 0x9F*, _]
        verify(test, 2, "Ɵ", "");

        test.push_char('ƛ'); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[^0xC6, 0x9B*, _]
        verify(test, 2, "ƛ", "");

        //three bytes
        test.push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xEA, 0x99, 0x82*]
        verify(test, 3, "Ꙃ", "");

        test.push_char('A');
        //[^A*, _, _]
        verify(test, 1, "A", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 3 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(3))]
    fn too_big(test: &mut impl StringBuffer) {
        verify_empty(test);
        //four bytes (too big for buffer)
        test.push_char('🦀'); //Crab Emoji (Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        verify(test, 0, "", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 5 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(5))]
    fn big_edge(test: &mut impl StringBuffer) {
        verify_empty(test);
        test.push_str("ABCD");
        //[^A, B, C, D*, _]
        verify(test, 4, "ABCD","");

        test.push_char('ƛ'); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[0xC6, 0x9B*, ^C, D, _]
        verify(test, 4, "CD", "ƛ");

        test.push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xC6, 0x9B, 0xEA, 0x99, 0x82*]
        verify(test, 5, "ƛꙂ", "");

        test.push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xEA, 0x99, 0x82*, _, _]
        verify(test, 3, "Ꙃ", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 5 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(5))]
    fn align(test: &mut impl StringBuffer) {
        verify_empty(test);
        test.push_str("ABCDE");
        verify(test, 5, "ABCDE", "");

        test.push_char('F');
        verify(test, 5, "BCDE", "F");
        test.align();
        verify(test, 5, "BCDEF", "");

        test.push_char('ƛ'); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        verify(test, 5, "DEF", "ƛ");
        test.align();
        verify(test, 5, "DEFƛ", "");

        test.push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        verify(test, 5, "ƛ", "Ꙃ");
        test.align();
        verify(test, 5, "ƛꙂ", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 5 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(5))]
    fn align_linear(test: &mut impl StringBuffer) {
        verify_empty(test);
        test.push_str("ABCDE");
        verify(test, 5, "ABCDE", "");

        test.push_char('F');
        verify(test, 5, "BCDE", "F");
        test.align_no_alloc();
        verify(test, 5, "BCDEF", "");

        test.push_char('ƛ'); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        verify(test, 5, "DEF", "ƛ");
        test.align_no_alloc();
        verify(test, 5, "DEFƛ", "");

        test.push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        verify(test, 5, "ƛ", "Ꙃ");
        test.align_no_alloc();
        verify(test, 5, "ƛꙂ", "");

        test.clear();
        verify_empty(test);
    }

    #[test]
    fn char_boundary_simple() {
        let data = "ABCD".as_bytes();
        assert_eq!(next_char_boundary(data, 0), Some(0));
        assert_eq!(next_char_boundary(data, 1), Some(1));
        assert_eq!(next_char_boundary(data, 2), Some(2));
        assert_eq!(next_char_boundary(data, 3), Some(3));
    }

    #[test]
    fn char_boundary_two_byte() {
        let data = "AƟB".as_bytes();
        assert_eq!(next_char_boundary(data,0), Some(0));
        assert_eq!(next_char_boundary(data,1), Some(1));
        assert_eq!(next_char_boundary(data,2), Some(3));
        assert_eq!(next_char_boundary(data,3), Some(3));
    }

    #[test]
    fn char_boundary_three_byte() {
        let data = "ꙂB".as_bytes();
        assert_eq!(next_char_boundary(data, 0), Some(0));
        assert_eq!(next_char_boundary(data,1), Some(3));
        assert_eq!(next_char_boundary(data,2), Some(3));
        assert_eq!(next_char_boundary(data,3), Some(3));
    }

    #[test]
    fn char_boundary_none() {
        let data = "AꙂ".as_bytes();
        assert_eq!(next_char_boundary(data, 0), Some(0));
        assert_eq!(next_char_boundary(data,1), Some(1));
        assert_eq!(next_char_boundary(data,2), None);
        assert_eq!(next_char_boundary(data,3), None);
    }

    #[test]
    fn from_string() {
        let mut buffer: HeapStRingBuffer = "ABCDE".to_string().into();
        verify(&mut buffer, 5, "ABCDE", "");

        buffer.clear();
        basic(&mut buffer);
    }

    #[test]
    fn from_vec() {
        let mut buffer: HeapStRingBuffer = "ABCDE".as_bytes().to_vec().try_into().unwrap();
        verify(&mut buffer, 5, "ABCDE", "");

        buffer.clear();
        basic(&mut buffer);
    }

    #[test]
    fn from_box_slice() {
        let mut buffer: HeapStRingBuffer = "ABCDE".as_bytes().to_vec().into_boxed_slice().try_into().unwrap();
        verify(&mut buffer, 5, "ABCDE", "");

        buffer.clear();
        basic(&mut buffer);
    }

    #[test]
    fn test_send() {
        fn assert_send<T: Send>() {}
        assert_send::<StRingBuffer<0>>();
        assert_send::<HeapStRingBuffer>();
    }

    #[test]
    fn test_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<StRingBuffer<0>>();
        assert_sync::<HeapStRingBuffer>();
    }
}
