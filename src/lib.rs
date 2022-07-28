use eframe::egui::TextBuffer;
use std::cmp::min;
use std::ops::Range;
use std::str::{from_utf8, from_utf8_unchecked};

struct StRingBuffer<const size: usize> {
    data: [u8; size],
    head: usize,
    tail: usize,
}

struct HeapStRingBuffer {
    data: Box<[u8]>,
    head: usize,
    tail: usize,
}

trait StringBuffer: TextBuffer {
    /// Adds a char to the buffer. Overwrites the start if the buffer is full.
    fn push_char(&mut self, c: char);

    /// Adds a &str to the buffer. Overwrites the start if the buffer is full.
    fn push_str(&mut self, s: &str);

    /// Get a reference to the two buffer segments in order.
    ///
    /// If the current data fits entirely in the buffer, and it is aligned, then the second
    /// reference will be an empty &str.
    fn as_slices(&self) -> (&str, &str);

    /// Moves the head of the ring to the start of the buffer. Required to represent the entire
    /// buffer as a single &str
    fn align(&mut self);

    /// Moves the head of the buffer near the specified index. Will move to an index >= the given
    /// index ensuring that the head lies on a valid UTF-8 boundary.
    fn move_head(&mut self, index: usize) -> usize;
}

// impl<const size: usize> TextBuffer for StRingBuffer<size> {
//     fn is_mutable(&self) -> bool {
//         true
//     }
//
//     fn char_range(&self, char_range: Range<usize>) -> &str {
//         todo!()
//     }
//
//     fn byte_index_from_char_index(&self, char_index: usize) -> usize {
//         todo!()
//     }
//
//     fn insert_text(&mut self, text: &str, char_index: usize) -> usize {
//         todo!()
//     }
//
//     fn delete_char_range(&mut self, char_range: Range<usize>) {
//         todo!()
//     }
//
//     fn clear(&mut self) {
//         self.head = 0;
//         self.tail = 0;
//     }
//
//     fn replace(&mut self, text: &str) {
//         self.clear();
//         self.push_str(text);
//     }
// }

impl<const size: usize> AsRef<str> for StRingBuffer<size> {
    fn as_ref(&self) -> &str {
        //TODO: how does splitting a codepoint across the ring work?
        // splitting it means we need to find the end before the split codepoint here
        // not splitting means that the &str ends before the end of the buffer

        // SAFETY:
        unsafe {
            if self.tail >= self.head {
                from_utf8_unchecked(&self.data[self.head..min(self.tail, size)])
            } else {
                from_utf8_unchecked(&self.data[self.head..size])
            }
        }
    }
}

impl<const size: usize> StringBuffer for StRingBuffer<size> {
    fn push_char(&mut self, c: char) {
        todo!()
    }

    fn push_str(&mut self, s: &str) {
        let bytes = s.as_bytes();
        if self.tail + bytes.len() < size {
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
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
