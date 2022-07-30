use std::cmp::{min, Ordering};
use std::iter::FusedIterator;
use std::str::{Chars, from_utf8, from_utf8_unchecked};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
enum State {
    #[default]
    Empty,
    Straight{count: usize},
    Looped{first: usize, end_offset: u8, next: usize}
}

impl State {
    unsafe fn get_char_push_slice<'a>(&'a mut self, c: char, data: &'a mut [u8]) -> &'a mut [u8] {
        let c_len = c.len_utf8();
        match self {
            State::Empty => {
                *self = State::Straight { count: c_len };
                data
            }
            State::Straight { count } => {
                if *count + c_len > data.len() {
                    let end_offset = (data.len() - *count).try_into().unwrap();
                    let (first, _) = from_utf8_unchecked(data).char_indices().find(|(i,_)| *i>=c_len).expect("No valid place for new head found");
                    *self = State::Looped {
                        first,
                        end_offset,
                        next: c_len,
                    };
                    data
                } else {
                    // self = &mut State::Straight { count: *count + c_len };
                    // &mut data[*count..(*count + c_len)]
                    *count += c_len;
                    &mut data[(*count - c_len)..*count]
                }
            }
            State::Looped { first, end_offset, next } => {
                if *first - *next < c_len {
                    //first needs to move
                    todo!()
                } else {
                    //big enough gap between first and next
                    let next = *next;
                    *self = State::Looped { next: next + c_len, first: *first, end_offset: *end_offset };
                    &mut data[next..(next + c_len)]
                }
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct StRingBuffer<const SIZE: usize> {
    data: [u8; SIZE],
    first: usize,
    last: usize,
    end_offset: u8,
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

    /// Moves the head of the buffer near the specified index. Will move to an index >= the given
    /// index ensuring that the head lies on a valid UTF-8 boundary.
    fn move_head(&mut self, index: usize) -> usize;

    /// Returns the length of this buffer, in bytes, not chars or graphemes
    fn len(&self) -> usize;

    fn capacity(&self) -> usize;

    fn chars(&self) -> std::iter::Chain<Chars<'_>, Chars<'_>> {
        let (front, back) = self.as_slices();
        front.chars().chain(back.chars())
    }

    fn clear(&mut self);
}

impl<const SIZE: usize> StringBuffer for StRingBuffer<SIZE> {
    fn push_char(&mut self, c: char) {
        let c_len = c.len_utf8();
        match c_len.cmp(&SIZE) {
            Ordering::Less => {
                if self.last < self.first {
                    if self.last + c_len > self.first {
                        //head needs to move
                        self.move_head(self.last + c_len);
                    }
                    //everything fits
                    c.encode_utf8(&mut self.data[self.last+1..]);
                    self.last += c_len;
                } else {
                    if c_len + self.last > SIZE {
                        // loop
                        self.end_offset = (SIZE - self.last) as u8;
                        self.last = 0;
                        //recurse to hit the self.tail < self.head case
                        self.push_char(c);
                    } else {
                        //everything fits
                        c.encode_utf8(&mut self.data[self.last+1..]);
                        self.last += c_len;
                    }
                }
            }
            Ordering::Equal => {
                self.clear();
                c.encode_utf8(&mut self.data);
            }
            Ordering::Greater => self.clear(),
        }
    }

    fn as_slices(&self) -> (&str, &str) {
        // SAFETY: Great care is taken in the other functions to ensure the validity of the str invariants
        unsafe {
            if self.last >= self.first {
               (from_utf8_unchecked(&self.data[self.first..=self.last]), "")
            } else {
                (from_utf8_unchecked(&self.data[self.first..(SIZE - self.end_offset as usize)]), from_utf8_unchecked(&self.data[0..=self.last]))
            }
        }
    }

    fn align(&mut self) {
        todo!()
    }

    fn move_head(&mut self, index: usize) -> usize {
        todo!()
    }

    fn len(&self) -> usize {
        if self.last < self.first {
            SIZE - (self.first - self.last) - self.end_offset as usize
        } else {
            self.last - self.first
        }
    }

    fn capacity(&self) -> usize {
        self.data.len()
    }

    fn clear(&mut self) {
        self.first = 0;
        self.last = 0;
    }
}

impl<const SIZE: usize> StRingBuffer<SIZE> {
    const fn new() -> Self {
        Self{
            data: [0; SIZE],
            first: 0,
            last: 0,
            end_offset: 0,
        }
    }
}

impl StringBuffer for HeapStRingBuffer {
    fn push_char(&mut self, c: char) {
        let c_len = c.len_utf8();
        let mut slice = match c_len.cmp(&self.capacity()) {
            Ordering::Less => unsafe {
                self.state.get_char_push_slice(c, &mut self.data)
            }
            Ordering::Equal => {
                self.state = State::Straight {count: c_len};
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
                let first_len = self.capacity() - end_offset as usize - first;
                self.data.copy_within(first..(self.capacity() - end_offset as usize), 0);
                self.data[first_len..].copy_from_slice(&copy);
                self.state = State::Straight {count: len};
            }
        }
    }

    fn move_head(&mut self, index: usize) -> usize {
        todo!()
    }

    fn len(&self) -> usize {
        match self.state {
            State::Empty => 0,
            State::Straight { count } => count,
            State::Looped { first, end_offset, next } => {
                self.capacity() - end_offset as usize - (first - next)
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
    use crate::{HeapStRingBuffer, StRingBuffer, StringBuffer};

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
        //[^0xEA, 0x99, 0x8x*]
        verify(test, 1, "Ꙃ", "");

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
}
