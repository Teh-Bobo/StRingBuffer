use std::cmp::min;
use std::iter::FusedIterator;
use std::str::{Chars, from_utf8, from_utf8_unchecked};

#[derive(Copy, Clone, Debug)]
struct StRingBuffer<const SIZE: usize> {
    data: [u8; SIZE],
    head: usize,
    tail: usize,
}

#[derive(Clone, Debug)]
struct HeapStRingBuffer {
    data: Box<[u8]>,
    head: usize,
    tail: usize,
}

trait StringBuffer {
    /// Adds a char to the buffer. Overwrites the start if the buffer is full.
    fn push_char(&mut self, c: char);

    /// Adds a &str to the buffer. Overwrites the start if the buffer is full.
    fn push_str(&mut self, s: &str);

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
}

impl<const SIZE: usize> AsRef<str> for StRingBuffer<SIZE> {
    fn as_ref(&self) -> &str {
        //TODO: how does splitting a codepoint across the ring work?
        // splitting it means we need to find the end before the split codepoint here
        // not splitting means that the &str ends before the end of the buffer

        // SAFETY:
        unsafe {
            if self.tail >= self.head {
                from_utf8_unchecked(&self.data[self.head..min(self.tail, SIZE)])
            } else {
                from_utf8_unchecked(&self.data[self.head..SIZE])
            }
        }
    }
}

impl<const SIZE: usize> StringBuffer for StRingBuffer<SIZE> {
    fn push_char(&mut self, c: char) {
        todo!()
    }

    fn push_str(&mut self, s: &str) {
        let bytes = s.as_bytes();
        if self.tail + bytes.len() < SIZE {
            let new_tail = self.tail + bytes.len();
            self.data[self.tail..new_tail].copy_from_slice(bytes);
        }
    }

    fn as_slices(&self) -> (&str, &str) {
        todo!()
    }

    fn align(&mut self) {
        todo!()
    }

    fn move_head(&mut self, index: usize) -> usize {
        todo!()
    }

    fn len(&self) -> usize {
        todo!()
    }

    fn capacity(&self) -> usize {
        self.data.len()
    }
}

impl<const SIZE: usize> StRingBuffer<SIZE> {
    const fn new() -> Self {
        Self{
            data: [0; SIZE],
            head: 0,
            tail: 0
        }
    }
}

impl StringBuffer for HeapStRingBuffer {
    fn push_char(&mut self, c: char) {
        todo!()
    }

    fn push_str(&mut self, s: &str) {
        todo!()
    }

    fn as_slices(&self) -> (&str, &str) {
        todo!()
    }

    fn align(&mut self) {
        todo!()
    }

    fn move_head(&mut self, index: usize) -> usize {
        todo!()
    }

    fn len(&self) -> usize {
        todo!()
    }

    fn capacity(&self) -> usize {
        self.data.len()
    }
}

impl HeapStRingBuffer {
    pub fn new(size: usize) -> Self {
        HeapStRingBuffer{
            data: vec![0; size].into_boxed_slice(),
            head: 0,
            tail: 0
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

    #[test_case(&mut SMALL_CONST.clone())]
    #[test_case(&mut small_heap())]
    fn basic(test: &mut impl StringBuffer){
        test.push_char('A');
        assert_eq!(test.len(), 1);
        assert_eq!(test.as_slices().0, "A");
        assert_eq!(test.as_slices().1, "");
        test.push_str("BCDE");
        assert_eq!(test.len(), 5);
        assert_eq!(test.as_slices().0, "ABCDE");
        assert_eq!(test.as_slices().1, "");

        assert_eq!(SMALL_SIZE, 5);
        test.push_char('X');
        assert_eq!(test.len(), 5);
        assert_eq!(test.as_slices().0, "BCDE");
        assert_eq!(test.as_slices().1, "X");
        test.align();
        assert_eq!(test.len(), 5);
        assert_eq!(test.as_slices().0, "BCDEX");
        assert_eq!(test.as_slices().1, "");
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
        assert_eq!(test.len(), 3);
        assert_eq!(test.as_slices().0, "C");
        assert_eq!(test.as_slices().1, "Ɵ");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), Some('C'));
            assert_eq!(iter.next(), Some('Ɵ'));
            assert_eq!(iter.next(), None);
        }

        test.push_str("XY");
        //[Y*, _, ^X]
        assert_eq!(test.len(), 2);
        assert_eq!(test.as_slices().0, "X");
        assert_eq!(test.as_slices().1, "Y");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), Some('X'));
            assert_eq!(iter.next(), Some('Y'));
            assert_eq!(iter.next(), None);
        }

        //split on buffer end
        test.push_char('Z');
        //[Y, Z, *^X]
        assert_eq!(test.len(), 3);
        test.push_char('Ɵ');
        //[^0xC6, 0x9F*, _]
        assert_eq!(test.len(), 2);
        assert_eq!(test.as_slices().0, "Ɵ");
        assert_eq!(test.as_slices().1, "");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), Some('Ɵ'));
            assert_eq!(iter.next(), None);
        }

        test.push_char('ƛ'); //Latin Small Letter Lambda with Stroke (UTF-8: 0xC6 0x9B)
        //[^0xC6, 0x9B*, _]
        assert_eq!(test.len(), 2);
        assert_eq!(test.as_slices().0, "ƛ");
        assert_eq!(test.as_slices().1, "");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), Some('ƛ'));
            assert_eq!(iter.next(), None);
        }

        //three bytes
        test.push_char('Ꙃ'); //Cyrillic Capital Letter Dzelo (UTF-8: 0xEA 0x99 0x82)
        //[^0xEA, 0x99, 0x8x*]
        assert_eq!(test.len(), 1);
        assert_eq!(test.as_slices().0, "Ꙃ");
        assert_eq!(test.as_slices().1, "");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), Some('Ꙃ'));
            assert_eq!(iter.next(), None);
        }
        test.push_char('A');
        //[^A*, _, _]
        assert_eq!(test.len(), 1);
        assert_eq!(test.as_slices().0, "A");
        assert_eq!(test.as_slices().1, "");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), Some('A'));
            assert_eq!(iter.next(), None);
        }

        //four bytes (too big for buffer)
        test.push_char('🦀'); //Crab Emoji (Ferris) (UTF-8: 0xF0 0x9F 0xA6 0x80)
        //[^_*, _, _]
        assert_eq!(test.len(), 0);
        assert_eq!(test.as_slices().0, "");
        assert_eq!(test.as_slices().1, "");
        {
            let mut iter = test.chars();
            assert_eq!(iter.next(), None);
        }
    }
}
