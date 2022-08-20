#![cfg_attr(not(feature = "std"), no_std)]
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

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// An error type used for the failable push functions on StringBuffer.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum StringBufferError {
    /// Returned if the buffer has 0 bytes of free space
    BufferFull,
    /// Returned if the buffer does not have enough free space to fit the given string
    NotEnoughSpaceForStr,
    /// Returned if the buffer does not have enough free space to fit the given char
    NotEnoughSpaceForChar,
}

impl core::fmt::Display for StringBufferError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            StringBufferError::BufferFull => "The buffer is full (0 bytes of free space).",
            StringBufferError::NotEnoughSpaceForStr => "The buffer does not have enough space to fit the given String",
            StringBufferError::NotEnoughSpaceForChar => "The buffer does not have enough space to fit the given char",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StringBufferError {}

/// A buffer specializing in holding data for a string. Pushing data to the buffer will not fail nor
/// panic. When full, the end of the data overwrites the start, while keeping the integrity of the
/// underlying utf-8 data.
pub trait StringBuffer {
    /// Adds a char to the buffer. Overwrites the start if the buffer is full.
    ///
    /// This will never panic nor fail. However, if the length of the char in utf-8 exceeds the
    /// length of the buffer then the buffer will be emptied.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// buffer.push_char('F');
    /// assert_eq!(buffer.as_slices().0, "F");
    /// assert_eq!(buffer.as_slices().1, "");
    /// ```
    fn push_char(&mut self, c: char);

    /// Remove a char from the buffer if one exists. Returns None if the buffer is empty.
    fn pop(&mut self) -> Option<char>;

    /// Tries to push the given character into the buffer. Will return Ok(c.bytes_len) if the write
    /// succeeded. If there is not enough room for the char or the buffer is full then
    /// Err(NotEnoughSpaceForChar) or Err(BufferFull) is returned respectively.
    ///
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer, StringBufferError};
    ///
    /// let mut buffer = StRingBuffer::<5>::new();
    /// let res = buffer.try_push_char('🦀'); //Crab Emoji (Fat Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
    /// assert_eq!(res, Ok(4));
    ///
    /// let res = buffer.try_push_char('🦀');
    /// //already 4 bytes in the buffer, can't fit 4 more
    /// assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForChar));
    ///
    /// //but 1 more does fit
    /// assert_eq!(buffer.try_push_char('A'), Ok(1));
    ///
    /// //now the buffer is full and can't fit anything
    /// assert_eq!(buffer.try_push_char('A'), Err(StringBufferError::BufferFull));
    /// ```
    fn try_push_char(&mut self, c: char) -> Result<usize, StringBufferError>;

    /// Adds a &str to the buffer. Overwrites the start if the buffer is full.
    ///
    /// This will never panic nor fail.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// buffer.push_str("ABCDE");
    /// buffer.push_char('F');
    /// assert_eq!(buffer.as_slices().0,"BCDE");
    /// assert_eq!(buffer.as_slices().1, "F");
    /// ```
    fn push_str(&mut self, s: &str) {
        s.chars().for_each(|c| self.push_char(c));
    }

    /// Will push as many chars as will fit into the existing space of the buffer. Will not
    /// overwrite any existing data.
    ///
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    ///
    /// let mut buffer = StRingBuffer::<5>::new();
    /// let res = buffer.try_push_some("ABCDEFGHIJKLMNO"); // too long
    /// assert_eq!(res, Ok(5)); //only 5 bytes pushed
    /// // the first bytes are pushed so long as there's room
    /// assert_eq!(buffer.as_slices().0,"ABCDE");
    /// ```
    fn try_push_some(&mut self, s: &str) -> Result<usize, StringBufferError>;

    /// Try to push the entire string into the buffer. If the string is too long or the buffer is
    /// full then nothing is written and Err(NotEnoughSpaceForStr) or Err(BufferFull) is returned
    /// respectively.
    ///
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer, StringBufferError};
    ///
    /// let mut buffer = StRingBuffer::<5>::new();
    /// assert_eq!(buffer.try_push_all("ABCDE"), Ok(()));
    /// assert_eq!(buffer.try_push_all("Z"), Err(StringBufferError::BufferFull));
    ///
    /// buffer.clear();
    /// let res = buffer.try_push_all("ABCDEFGHIJKLMNO"); // too long
    /// assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForStr));
    /// ```
    fn try_push_all(&mut self, s: &str) -> Result<(), StringBufferError> {
        if self.remaining_size() == 0 {
            return Err(StringBufferError::BufferFull);
        }

        if s.len() <= self.capacity() - self.len() {
            self.push_str(s);
            Ok(())
        } else {
            Err(StringBufferError::NotEnoughSpaceForStr)
        }
    }

    /// Get a reference to the two buffer segments in order.
    ///
    /// If the current data fits entirely in the buffer, and it is aligned, then the second
    /// reference will be an empty &str.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// buffer.push_str("ABCDE");
    /// assert_eq!(buffer.as_slices().0, "ABCDE");
    /// assert_eq!(buffer.as_slices().1, "");
    ///
    /// buffer.push_char('F');
    /// assert_eq!(buffer.as_slices().0, "BCDE");
    /// assert_eq!(buffer.as_slices().1,"F");
    /// ```
    fn as_slices(&self) -> (&str, &str);

    /// Copies data as required to make the head the start of the buffer. This allocates a temporary
    /// buffer the size of the smaller &str given by [`as_slices`](StringBuffer::as_slices).
    ///
    /// This is required to represent the entire buffer as a single &str.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// buffer.push_str("ABCDE");
    /// buffer.push_char('F');
    /// assert_eq!(buffer.as_slices().0, "BCDE");
    /// assert_eq!(buffer.as_slices().1, "F");
    /// buffer.align();
    /// assert_eq!(buffer.as_slices().0, "BCDEF");
    /// ```
    fn align(&mut self);

    /// Aligns the head of the buffer to the start via rotation. Compared to
    /// [`align`](StringBuffer::align) this function does not allocate any memory; however, it works
    /// in O([`buffer.len()`](StringBuffer::len)) time.
    ///
    /// This is required to represent the entire buffer as a single &str.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// buffer.push_str("ABCDE");
    /// buffer.push_char('F');
    /// assert_eq!(buffer.as_slices().0, "BCDE");
    /// assert_eq!(buffer.as_slices().1, "F");
    /// buffer.align_no_alloc();
    /// assert_eq!(buffer.as_slices().0, "BCDEF");
    /// ```
    fn align_no_alloc(&mut self);

    /// Returns the length of this buffer, in bytes, not chars or graphemes
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// buffer.push_str("ABCDEF");
    /// assert_eq!(buffer.len(), 5);
    /// ```
    fn len(&self) -> usize;

    /// Returns true if there is no data in the buffer.
    fn is_empty(&self) -> bool;

    /// The number of bytes this buffer can hold. Not the number of chars or graphemes.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    /// let mut buffer = StRingBuffer::<5>::new();
    /// assert_eq!(buffer.capacity(), 5);
    /// ```
    fn capacity(&self) -> usize;

    /// Convenience function to return the number of bytes remaining in the buffer before data is
    /// overwritten. This is roughly equivalent to ```self.capacity() - self.len()```, but takes into
    /// account any padding required along the edge of the buffer.
    fn remaining_size(&self) -> usize;

    /// Returns an iterator over the characters in the buffer. This includes both slices, in order,
    /// if the buffer is currently split.
    /// # Example
    /// ```rust
    /// use st_ring_buffer::{StRingBuffer, StringBuffer};
    ///
    /// let mut buffer = StRingBuffer::<5>::new();
    /// //Fill up the buffer
    /// buffer.push_str("ABCDE");
    /// //add one more so that the buffer is looped
    /// buffer.push_char('F');
    /// assert_eq!(buffer.as_slices().0, "BCDE");
    /// assert_eq!(buffer.as_slices().1, "F");
    ///
    /// //iterator doesn't care about loop and still gives all chars in order
    /// let mut iter = buffer.chars();
    /// assert_eq!(Some('B'), iter.next());
    /// assert_eq!(Some('C'), iter.next());
    /// assert_eq!(Some('D'), iter.next());
    /// assert_eq!(Some('E'), iter.next());
    /// assert_eq!(Some('F'), iter.next());
    /// assert_eq!(None, iter.next());
    /// ```
    fn chars(&self) -> Chain<Chars<'_>, Chars<'_>> {
        let (front, back) = self.as_slices();
        front.chars().chain(back.chars())
    }

    /// Empties the buffer
    fn clear(&mut self);
}

/// An implementation of [`StringBuffer`](StringBuffer) using const generics to store its data on
/// the stack.
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

        fn try_push_char(&mut self, c: char) -> Result<usize, StringBufferError> {
            let remaining_size = self.remaining_size();
            if remaining_size == 0 {
                Err(StringBufferError::BufferFull)
            } else if remaining_size < c.len_utf8() {
                Err(StringBufferError::NotEnoughSpaceForChar)
            } else {
                self.push_char(c);
                Ok(c.len_utf8())
            }
        }

        fn push_str(&mut self, s: &str) {
            unsafe {
                //SAFETY: s is a valid utf-8 byte sequence because it's a &str
                self.state.insert_bytes(&mut self.data, s.as_bytes());
            }
        }

        fn try_push_some(&mut self, s: &str) -> Result<usize, StringBufferError> {
            if self.remaining_size() == 0 {
                return Err(StringBufferError::BufferFull)
            }
            let bytes = s.as_bytes();
            let char_boundary = prev_char_boundary(bytes, self.remaining_size()).unwrap_or(0);
            let b = &bytes[..char_boundary];

            // SAFETY: we know b is valid utf-8 because it came from a &str and we made sure to
            // split it on a char boundary. Self.data must also be valid utf-8.
            let len = unsafe {
                self.state.insert_bytes(&mut self.data, b)
            };
            if len == 0 {
                Err(StringBufferError::NotEnoughSpaceForStr)
            } else {
                Ok(len)
            }
        }

        fn as_slices(&self) -> (&str, &str) {
            unsafe {
                //SAFETY: self.data must be valid utf-8 sequence. This is ensured by any method in
                //this trait that modifies the buffer.
                match self.state {
                    State::Empty => ("", ""),
                    State::Straight { count } => (from_utf8_unchecked(&self.data[0..count]),""),
                    State::OffsetStraight {offset, next} => (from_utf8_unchecked(&self.data[offset..next]),""),
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
                State::OffsetStraight { offset, next } => {
                    self.data.copy_within(offset..next, 0);
                    self.state = State::Straight { count: next - offset }
                }
                State::Looped { first, end_offset, next } => {
                    let count = self.len();
                    let capacity_minus_offset = self.capacity() - end_offset as usize;
                    let first_len = capacity_minus_offset - first;

                    if first_len < next {
                        let copy = self.data[first..capacity_minus_offset].to_owned();
                        self.data.copy_within(0..next, first_len);
                        self.data[0..first_len].copy_from_slice(&copy);
                    } else {
                        let copy = self.data[0..next].to_owned();
                        self.data.copy_within(first..capacity_minus_offset, 0);
                        self.data[first_len..].copy_from_slice(&copy);
                    }

                    self.state = State::Straight {count};
                }
            }
        }

        fn align_no_alloc(&mut self) {
            match self.state {
                State::Empty | State::Straight { .. } => {}
                State::OffsetStraight { offset, next } => {
                    self.data.copy_within(offset..next, 0);
                    self.state = State::Straight { count: next - offset }
                }
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
                State::OffsetStraight{offset, next} => next - offset,
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

        fn remaining_size(&self) -> usize {
            match self.state {
                State::Empty | State::Straight { .. } | State::OffsetStraight { .. } => self.capacity() - self.len(),
                State::Looped { end_offset, .. } => self.capacity() - self.len() - end_offset as usize,
            }
        }

        fn clear(&mut self) {
            self.state = State::Empty;
        }
    }
}

impl<const SIZE: usize> StringBuffer for StRingBuffer<SIZE> {
    impl_buffer_trait!();

    fn pop(&mut self) -> Option<char> {
        match &mut self.state {
            State::Empty => None,
            State::OffsetStraight { offset, next } => {
                //SAFETY: We know there is at least one char in the buffer since we're in the
                // straight state. The only way for prev_char_boundary to fail is if self.data is
                // malformed, which is undefined behavior.
                let new_next = unsafe {
                    prev_char_boundary(&self.data, *next - 1)
                        .unwrap_unchecked()
                        .max(*offset)
                };
                //SAFETY: we know that data is always valid utf-8 and have sliced it along a char
                //boundary, ensuring that char iterator will return exactly one char
                let c = unsafe { from_utf8_unchecked(&self.data[new_next..*next]).chars().next().unwrap_unchecked() };
                if new_next == *offset {
                    self.state = State::Empty;
                } else {
                    *next = new_next
                }
                Some(c)
            }
            State::Straight { count } => {
                //SAFETY: We know there is at least one char in the buffer since we're in the
                // straight state. The only way for prev_char_boundary to fail is if self.data is
                // malformed, which is undefined behavior.
                let new_count = unsafe { prev_char_boundary(&self.data, *count - 1).unwrap_unchecked() };
                //SAFETY: we know that data is always valid utf-8 and have sliced it along a char
                //boundary, ensuring that char iterator will return exactly one char
                let c = unsafe { from_utf8_unchecked(&self.data[new_count..*count]).chars().next().unwrap_unchecked() };
                if new_count == 0 {
                    self.state = State::Empty;
                } else {
                    *count = new_count
                }
                Some(c)
            }
            State::Looped { first, end_offset, next } => {
                let prev_offset = if *next > self.data.len() {
                    *end_offset as usize
                } else {
                    0
                } + 1;
                //SAFETY: We know there is at least one char in the buffer since we're in the
                // looped state. The only way for prev_char_boundary to fail is if self.data is
                // malformed, which is undefined behavior.
                let new_next = unsafe { prev_char_boundary(&self.data, *next - prev_offset).unwrap_unchecked() };
                //SAFETY: we know that data is always valid utf-8 and have sliced it along a char
                //boundary, ensuring that char iterator will return exactly one char
                let c = unsafe { from_utf8_unchecked(&self.data[new_next..*next]).chars().next().unwrap_unchecked() };

                if new_next == 0 {
                    self.state = State::OffsetStraight { offset: *first, next: self.data.len() }
                } else if new_next == *first {
                    self.state = State::Empty;
                } else {
                    *next = new_next
                }

                Some(c)
            },
        }
    }
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

    fn pop(&mut self) -> Option<char> {
        todo!()
    }
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

impl<const SIZE: usize> IntoIterator for StRingBuffer<SIZE> {
    type Item = char;
    type IntoIter = BufferIterator<StRingBuffer<SIZE>>;

    fn into_iter(self) -> Self::IntoIter {
        BufferIterator{
            buffer: self
        }
    }
}

impl IntoIterator for HeapStRingBuffer {
    type Item = char;
    type IntoIter = BufferIterator<HeapStRingBuffer>;

    fn into_iter(self) -> Self::IntoIter {
        BufferIterator{
            buffer: self
        }
    }
}

/// An iterator for StringBuffer types.
pub struct BufferIterator<T>
    where T: StringBuffer {
    buffer: T,
}

impl<T> Iterator for BufferIterator<T>
    where T: StringBuffer {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.buffer.pop()
    }
}

//-------------------------
const fn is_utf8_char_boundary(b: u8) -> bool {
    // Stolen from core::num::mod, which keeps this function private
    // This is bit magic equivalent to: b < 128 || b >= 192
    (b as i8) >= -0x40
}

//Only returns None if 0 is not a char boundary--which is illegal state
fn prev_char_boundary(data: &[u8], start: usize) -> Option<usize> {
    data[..=start].iter()
        .rev()
        .enumerate()
        .find(|(_, b)| is_utf8_char_boundary(**b))
        .map(|(i, _)| start - i)
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
    OffsetStraight{offset: usize, next: usize},
    Looped{first: usize, end_offset: u8, next: usize}
}

impl State {
    /// Returns the slice of data where the char should be inserted; modifying the state to prepare
    /// for the insert if necessary.
    fn get_char_slice<'a>(&'a mut self, char_len: usize, data: &'a mut [u8]) -> &'a mut [u8] {
        debug_assert!(char_len < data.len());
        match self {
            State::Empty => {
                *self = State::Straight { count: char_len };
                data
            }
            State::OffsetStraight { offset, next } => {
                if *next + char_len > data.len() {
                    //char doesn't fit in straight, need to convert to looped
                    let end_offset = (data.len() - *next).try_into().unwrap();
                    if char_len <= *offset {
                        //char fits before the offset
                        *self = State::Looped {
                            first: *offset,
                            end_offset,
                            next: char_len,
                        };
                        data
                    } else {
                        //offset needs to move
                        *self = match next_char_boundary(&data, char_len) {
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
                    }
                } else {
                    //char fits as-is
                    *next += char_len;
                    &mut data[(*next - char_len)..*next]
                }
            }
            State::Straight { count } => {
                if *count + char_len > data.len() {
                    //char doesn't fit in straight, need to convert to looped
                    let end_offset = (data.len() - *count).try_into().unwrap();
                    *self = match next_char_boundary(&data[..*count], char_len) {
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
                    match next_char_boundary(data, *first + char_len) {
                        None => {
                            //first needs to loop back to the start (back to straight)
                            *self = State::Straight {count: *next};
                            // head down the straight pipeline
                            self.get_char_slice(char_len, data)
                        }
                        Some(new_first) => {
                            let next_copy = *next;
                            let new_next = next_copy + char_len;
                            if new_next > data.len() - *end_offset as usize {
                                //char insert overwrites end offset
                                *end_offset = (data.len() - new_next).try_into().unwrap();
                            }
                            *next = new_next;
                            *first = new_first;
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

    /// Inserts bytes into data, while ensuring the State remains valid.
    ///
    /// Returns the number of bytes copied. If this is less than bytes.len() and the return value is
    /// n then the bytes copied is `bytes[(bytes.len() - n)..]`.
    ///
    /// # Safety
    /// `bytes` must be a valid utf-8 sequence. If its not then any reads from `data` will result
    /// in undefined behavior.
    unsafe fn insert_bytes(&mut self, data: &mut [u8], bytes: &[u8]) -> usize {
        if bytes.is_empty() { return 0 }
        else if bytes.len() > data.len() {
            let bytes_start_index = bytes.len() - data.len();
            return match next_char_boundary(bytes, bytes_start_index) {
                None => {
                    // there is no valid char boundary between where the split needs to be and the
                    // end. Treat the buffer like the start was written and then overwritten by
                    // later data and clear the buffer
                    *self = State::Empty;
                    0
                }
                Some(start_index) => {
                    data.copy_from_slice(&bytes[start_index..]);
                    *self = State::Straight {count: data.len()};
                    data.len()
                }
            };
        } else if bytes.len() == data.len() {
            data.copy_from_slice(bytes);
            *self = State::Straight {count: data.len()};
            return data.len();
        }
        match self {
            State::Empty => {
                let bytes_len = bytes.len();
                let count = if bytes_len <= data.len() {
                    data[..bytes_len].copy_from_slice(bytes);
                    bytes_len
                } else {
                    match next_char_boundary(bytes, bytes_len - data.len()) {
                        None => return 0,
                        Some(start) => {
                            let len = bytes_len - start;
                            data[..len].copy_from_slice(&bytes[start..]);
                            len
                        }
                    }
                };
                *self = State::Straight {count};
                count
            }
            State::Straight { count } => {
                let bytes_len = bytes.len();
                if *count + bytes_len <= data.len() {
                    //everything fits
                    data[*count..(*count + bytes_len)].copy_from_slice(bytes);
                    *count += bytes_len;
                } else {
                    // doesn't fit
                    // start by finding where to split bytes. The first half will be inserted after
                    // count, while the second half will loop back to the start
                    let first_len = data.len() - *count;
                    let index = prev_char_boundary(bytes, first_len)
                        .expect("Tried to insert bytes with malformed utf-8");
                    let (first, second) = bytes.split_at(index);
                    let end_offset = (first_len - first.len()).try_into().unwrap();

                    //copy first and calculate the end_offset
                    data[*count..(*count + first.len())].copy_from_slice(first);
                    data[..second.len()].copy_from_slice(second);

                    // find where the head should be
                    let search_range = if first.is_empty() {
                        // we didn't insert anything after count and we looped around so everything
                        // after count is "empty"
                        &data[..*count]
                    } else {
                        // if first was not empty then first may need to be the first char that
                        // was inserted from bytes
                        &data[..=*count]
                    };
                    match next_char_boundary(search_range, second.len()) {
                        None => *count = second.len(),
                        Some(new_first) => *self = State::Looped {
                            first: new_first,
                            end_offset,
                            next: second.len(),
                        },
                    };

                }
                bytes_len
            }
            State::OffsetStraight { offset, next } => {
                let bytes_len = bytes.len();
                if *next + bytes_len <= data.len() {
                    //everything fits
                    data[*next..(*next + bytes_len)].copy_from_slice(bytes);
                    *next += bytes_len;
                } else {
                    // doesn't fit
                    // start by finding where to split bytes. The first half will be inserted after
                    // next, while the second half will loop back to the start
                    let first_len = data.len() - *next;
                    let index = prev_char_boundary(bytes, first_len)
                        .expect("Tried to insert bytes with malformed utf-8");
                    let (first, second) = bytes.split_at(index);
                    let end_offset = (first_len - first.len()).try_into().unwrap();

                    //copy first and calculate the end_offset
                    data[*next..(*next + first.len())].copy_from_slice(first);
                    data[..second.len()].copy_from_slice(second);
                    if second.len() > *offset {
                        // offset needs to move
                        // find where the head should be
                        let search_range = if first.is_empty() {
                            // we didn't insert anything after count and we looped around so everything
                            // after count is "empty"
                            &data[..*next]
                        } else {
                            // if first was not empty then first may need to be the first char that
                            // was inserted from bytes
                            &data[..=*next]
                        };
                        match next_char_boundary(search_range, second.len()) {
                            None => *next = second.len(),
                            Some(new_first) => *self = State::Looped {
                                first: new_first,
                                end_offset,
                                next: second.len(),
                            },
                        };
                    } else {
                        // offset stays, need to change to looped
                        *self = State::Looped {
                            first: *offset,
                            end_offset,
                            next: second.len()
                        };
                    }
                }
                bytes_len
            }
            State::Looped { first, end_offset, next } => {
                if *first - *next >= bytes.len() {
                    // big enough gap between first and next to fit the bytes
                    data[*next..(*next + bytes.len())].copy_from_slice(bytes);
                    *next += bytes.len();
                } else {
                    //first needs to move
                    match next_char_boundary(data, *first + bytes.len()) {
                        None => {
                            // first loops back to the start (straight)
                            *self = State::Straight {count: *next};
                            // finish in the straight pipeline
                            self.insert_bytes(data, bytes);
                        }
                        Some(new_first) => {
                            let new_next = *next + bytes.len();
                            if new_next > data.len() - *end_offset as usize {
                                //char insert overwrites end offset
                                *end_offset = (data.len() - new_next).try_into().unwrap();
                            }
                            data[*next..new_next].copy_from_slice(bytes);
                            *next = new_next;
                            *first = new_first;
                        }
                    }
                }
                // both branches always copy the whole byte slice
                bytes.len()
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use test_case::test_case;

    use crate::{next_char_boundary, prev_char_boundary, StRingBuffer, StringBuffer, StringBufferError};
    use crate::HeapStRingBuffer;

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

    #[test_case(& mut StRingBuffer::< 5 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(5))]
    fn basic(test: &mut impl StringBuffer){
        verify_empty(test);
        test.push_char('A');
        verify(test, 1, "A", "");

        test.push_str("BCDE");
        verify(test, 5, "ABCDE", "");

        test.push_char('X');
        verify(test, 5, "BCDE", "X");

        test.align();
        verify(test, 5, "BCDEX", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 5 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(5))]
    fn basic_str(test: &mut impl StringBuffer) {
        verify_empty(test);
        test.push_str("ABC");
        verify(test, 3, "ABC", "");

        test.push_str("DE");
        verify(test, 5, "ABCDE", "");

        test.push_str("X");
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

        test.push_char('X');
        test.push_char('Y');
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
    fn two_byte_str(test: &mut impl StringBuffer) {
        verify_empty(test);
        assert_eq!(test.capacity(), 3);
        test.push_str("ABC");
        //[^A, B, C*]
        assert_eq!(test.len(), 3);
        test.push_str("Ɵ"); //Latin Capital Letter O with Middle Tilde (0xC6 0x9F in UTF-8)
        //[0xC6, 0x9F, *^C]
        verify(test, 3, "C", "Ɵ");

        test.push_str("XY");
        //[Y*, _, ^X]
        verify(test, 2, "X", "Y");

        //split on buffer end
        test.push_str("Z");
        //[Y, Z, *^X]
        verify(test, 3, "X", "YZ");
        test.push_str("Ɵ");
        //[^0xC6, 0x9F*, _]
        verify(test, 2, "Ɵ", "");

        test.push_str("ƛ"); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[^0xC6, 0x9B*, _]
        verify(test, 2, "ƛ", "");

        //three bytes
        test.push_str("Ꙃ"); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xEA, 0x99, 0x82*]
        verify(test, 3, "Ꙃ", "");

        test.push_str("A");
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
        test.push_char('🦀'); //Crab Emoji (Fat Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        verify(test, 0, "", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 3 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(3))]
    fn too_big_str(test: &mut impl StringBuffer) {
        verify_empty(test);
        //four bytes (too big for buffer)
        test.push_str("🦀"); //Crab Emoji (Fat Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
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
    fn big_edge_str(test: &mut impl StringBuffer) {
        verify_empty(test);
        test.push_str("ABCD");
        //[^A, B, C, D*, _]
        verify(test, 4, "ABCD","");

        test.push_str("ƛ"); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[0xC6, 0x9B*, ^C, D, _]
        verify(test, 4, "CD", "ƛ");

        test.push_str("Ꙃ"); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xC6, 0x9B, 0xEA, 0x99, 0x82*]
        verify(test, 5, "ƛꙂ", "");

        test.push_str("Ꙃ"); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
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
    fn next_char_boundary_simple() {
        let data = "ABCD".as_bytes();
        assert_eq!(next_char_boundary(data, 0), Some(0));
        assert_eq!(next_char_boundary(data, 1), Some(1));
        assert_eq!(next_char_boundary(data, 2), Some(2));
        assert_eq!(next_char_boundary(data, 3), Some(3));
    }

    #[test]
    fn next_char_boundary_two_byte() {
        let data = "AƟB".as_bytes();
        assert_eq!(next_char_boundary(data,0), Some(0));
        assert_eq!(next_char_boundary(data,1), Some(1));
        assert_eq!(next_char_boundary(data,2), Some(3));
        assert_eq!(next_char_boundary(data,3), Some(3));
    }

    #[test]
    fn next_char_boundary_three_byte() {
        let data = "ꙂB".as_bytes();
        assert_eq!(next_char_boundary(data, 0), Some(0));
        assert_eq!(next_char_boundary(data,1), Some(3));
        assert_eq!(next_char_boundary(data,2), Some(3));
        assert_eq!(next_char_boundary(data,3), Some(3));
    }

    #[test]
    fn next_char_boundary_none() {
        let data = "AꙂ".as_bytes();
        assert_eq!(next_char_boundary(data, 0), Some(0));
        assert_eq!(next_char_boundary(data,1), Some(1));
        assert_eq!(next_char_boundary(data,2), None);
        assert_eq!(next_char_boundary(data,3), None);
    }

    #[test]
    fn prev_char_boundary_simple() {
        let data = "ABCD".as_bytes();
        assert_eq!(prev_char_boundary(data, 0), Some(0));
        assert_eq!(prev_char_boundary(data, 1), Some(1));
        assert_eq!(prev_char_boundary(data, 2), Some(2));
        assert_eq!(prev_char_boundary(data, 3), Some(3));
    }

    #[test]
    fn prev_char_boundary_two_byte() {
        let data = "AƟB".as_bytes();
        assert_eq!(prev_char_boundary(data,0), Some(0));
        assert_eq!(prev_char_boundary(data,1), Some(1));
        assert_eq!(prev_char_boundary(data,2), Some(1));
        assert_eq!(prev_char_boundary(data,3), Some(3));
    }

    #[test]
    fn prev_char_boundary_three_byte() {
        let data = "ꙂB".as_bytes();
        assert_eq!(prev_char_boundary(data, 0), Some(0));
        assert_eq!(prev_char_boundary(data,1), Some(0));
        assert_eq!(prev_char_boundary(data,2), Some(0));
        assert_eq!(prev_char_boundary(data,3), Some(3));
    }

    #[test]
    fn prev_char_boundary_none() {
        let data = "AꙂ".as_bytes();
        assert_eq!(prev_char_boundary(data, 0), Some(0));
        assert_eq!(prev_char_boundary(data,1), Some(1));
        assert_eq!(prev_char_boundary(data,2), Some(1));
        assert_eq!(prev_char_boundary(data,3), Some(1));
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

    #[test_case(& mut StRingBuffer::< 3 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(3))]
    fn try_char(test: &mut impl StringBuffer) {
        verify_empty(test);
        //four bytes (too big for buffer)
        let res = test.try_push_char('🦀'); //Crab Emoji (Fat Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForChar));
        verify(test, 0, "", "");

        let res = test.try_push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xEA, 0x99, 0x82*]
        assert_eq!(res, Ok(3));
        verify(test, 3, "Ꙃ", "");

        let res = test.try_push_char('A');
        assert_eq!(res, Err(StringBufferError::BufferFull));
        verify(test, 3, "Ꙃ", "");

        test.push_str("AB");
        //[^A, B, *_]
        let res = test.try_push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForChar));
        verify(test, 2, "AB", "");

        test.clear();
        verify_empty(test);
    }

    #[test_case(& mut StRingBuffer::< 3 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(3))]
    fn try_push_some(test: &mut impl StringBuffer) {
        verify_empty(test);

        //four bytes (too big for buffer)
        let res = test.try_push_some("🦀"); //Crab Emoji (Fat Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForStr));
        verify_empty(test);

        let res = test.try_push_some("ƛƛ"); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[^0xC6, 0x9B, _*]
        assert_eq!(res, Ok(2));
        verify(test, 2, "ƛ", "");

        test.clear();
        let res = test.try_push_some("ABCD");
        //[^A, B, C]*
        assert_eq!(res, Ok(3));
        verify(test, 3, "ABC", "");

        let res = test.try_push_some("XYZ");
        //[^A, B, C]*
        assert_eq!(res, Err(StringBufferError::BufferFull));
        verify(test, 3, "ABC", "");

        test.push_char('X');
        //[X, ^*B, C]
        verify(test, 3, "BC", "X");

        let res = test.try_push_some("YZ");
        //[X, ^*B, C]
        assert_eq!(res, Err(StringBufferError::BufferFull));
        verify(test, 3, "BC", "X");
    }

    #[test_case(& mut StRingBuffer::< 3 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(3))]
    fn try_str_all(test: &mut impl StringBuffer) {
        verify_empty(test);

        //four bytes (too big for buffer)
        let res = test.try_push_all("🦀"); //Crab Emoji (Fat Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForStr));
        verify_empty(test);

        let res = test.try_push_all("ƛƛ"); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[^0xC6, 0x9B, _*]
        assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForStr));
        verify_empty(test);

        let res = test.try_push_all("ABCD");
        //[^_*, _, _]
        assert_eq!(res, Err(StringBufferError::NotEnoughSpaceForStr));
        verify(test, 0, "", "");

        let res = test.try_push_all("XYZ");
        //[^X, Y, Z]*
        assert_eq!(res, Ok(()));
        verify(test, 3, "XYZ", "");

        let res = test.try_push_all("ABC");
        //[^X, Y, Z]*
        assert_eq!(res, Err(StringBufferError::BufferFull));
        verify(test, 3, "XYZ", "");

        test.push_char('A');
        //[A, ^*Y, Z]
        verify(test, 3, "YZ", "A");

        let res = test.try_push_all("BC");
        //[A, ^*Y, Z]
        assert_eq!(res, Err(StringBufferError::BufferFull));
        verify(test, 3, "YZ", "A");
    }

    #[test_case(& mut StRingBuffer::< 4 >::new())]
    #[test_case(& mut HeapStRingBuffer::new(4))]
    fn pop_char(test: &mut impl StringBuffer) {
        //Empty
        assert_eq!(test.pop(), None);

        //Straight
        test.push_char('A');
        assert_eq!(test.pop(), Some('A'));

        test.push_str("ƛƛ"); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        assert_eq!(test.pop(), Some('ƛ'));
        verify(test, 2, "ƛ", "");
        assert_eq!(test.pop(), Some('ƛ'));
        verify_empty(test);
        assert_eq!(test.pop(), None);

        //Looped
        test.push_str("ABCD");
        test.push_char('E');
        //[E, ^*B, C, D]
        assert_eq!(test.pop(), Some('E'));
        //[_, ^B, C, D]*
        verify(test, 3, "BCD", "");

        test.push_char('ƛ');
        //[0xC6, 0x9B, ^*C, D]
        verify(test, 4, "CD", "ƛ");
        assert_eq!(test.pop(), Some('ƛ'));
        verify(test, 2, "CD", "");
    }
}
