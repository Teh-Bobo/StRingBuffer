use std::cmp::Ordering;
use std::str::{Chars, from_utf8_unchecked};

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

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
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

#[derive(Copy, Clone, Debug)]
struct StRingBuffer<const SIZE: usize> {
    data: [u8; SIZE],
    state: State,
}

#[derive(Clone, Debug)]
struct HeapStRingBuffer {
    data: Box<[u8]>,
    state: State,
}

trait StringBuffer {
    /// Adds a char to the buffer. Overwrites the start if the buffer is full.
    fn push_char(&mut self, c: char);

    /// Adds a &str to the buffer. Overwrites the start if the buffer is full.
    fn push_str(&mut self, s: &str){
        s.chars().for_each(|c| self.push_char(c));
    }

    /// Get a reference to the two buffer segments in order.
    ///
    /// If the current data fits entirely in the buffer, and it is aligned, then the second
    /// reference will be an empty &str.
    fn as_slices(&self) -> (&str, &str);

    /// Copies data as required to make the head the start of the buffer. Required to represent the
    /// entire buffer as a single &str.
    fn align(&mut self);

    /// Returns the length of this buffer, in bytes, not chars or graphemes
    fn len(&self) -> usize;

    fn capacity(&self) -> usize;

    fn chars(&self) -> std::iter::Chain<Chars<'_>, Chars<'_>> {
        let (front, back) = self.as_slices();
        front.chars().chain(back.chars())
    }

    fn clear(&mut self);
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

impl<const SIZE: usize> StRingBuffer<SIZE> {
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

impl HeapStRingBuffer {
    pub fn new(size: usize) -> Self {
        HeapStRingBuffer{
            data: vec![0; size].into_boxed_slice(),
            state: Default::default(),
        }
    }
}


#[cfg(test)]
mod tests {
    use test_case::test_case;

    use crate::{HeapStRingBuffer, next_char_boundary, StRingBuffer, StringBuffer};

    const SMALL_SIZE: usize = 5;
    const SMALL_CONST: StRingBuffer<SMALL_SIZE> = StRingBuffer::new();

    fn small_heap() -> HeapStRingBuffer{
        HeapStRingBuffer::new(SMALL_SIZE)
    }

    fn verify(test: &impl StringBuffer, expected_len: usize, first: &str, second: &str) {
        assert_eq!(test.len(), expected_len);
        assert_eq!(test.as_slices().0, first);
        assert_eq!(test.as_slices().1, second);
        first.chars().chain(second.chars()).zip(test.chars()).for_each(|(expected, given)|assert_eq!(expected, given));
    }

    #[test_case(&mut SMALL_CONST.clone())]
    #[test_case(&mut small_heap())]
    fn basic(test: &mut impl StringBuffer){
        test.push_char('A');
        verify(test, 1, "A", "");

        test.push_str("BCDE");
        verify(test, 5, "ABCDE", "");

        assert_eq!(SMALL_SIZE, 5);
        test.push_char('X');
        verify(test, 5, "BCDE", "X");

        test.align();
        verify(test, 5, "BCDEX", "");
    }

    #[test_case(&mut StRingBuffer::<3>::new())]
    #[test_case(&mut HeapStRingBuffer::new(3))]
    fn two_byte(test: &mut impl StringBuffer) {
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
    }

    #[test_case(&mut StRingBuffer::<3>::new())]
    #[test_case(&mut HeapStRingBuffer::new(3))]
    fn too_big(test: &mut impl StringBuffer) {
        //four bytes (too big for buffer)
        test.push_char('🦀'); //Crab Emoji (Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        verify(test, 0, "", "");
    }

    #[test_case(&mut StRingBuffer::<5>::new())]
    #[test_case(&mut HeapStRingBuffer::new(5))]
    fn big_edge(test: &mut impl StringBuffer) {
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
}
