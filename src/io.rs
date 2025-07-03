use crate::{AVec, Alignment};

use std::io;

impl<A> io::Write for AVec<u8, A>
where
    A: Alignment,
{
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
        let len = bufs.iter().map(|b| b.len()).sum();
        self.reserve(len);
        for buf in bufs {
            self.extend_from_slice(buf);
        }
        Ok(len)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.extend_from_slice(buf);
        Ok(())
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use crate::{ConstAlign, RuntimeAlign};

    use super::*;

    #[test]
    fn write_read_const_align() {
        let mut vec = AVec::<_, ConstAlign<8>>::new(4);
        let data = b"Hello, world!";
        let bytes_written = vec.write(data).unwrap();
        assert_eq!(bytes_written, data.len());
        assert_eq!(vec.as_slice(), data);
    }

    #[test]
    fn write_read_runtime_align() {
        let mut vec = AVec::<_, RuntimeAlign>::new(8);
        let data = b"Hello, world!";
        let bytes_written = vec.write(data).unwrap();
        assert_eq!(bytes_written, data.len());
        assert_eq!(vec.as_slice(), data);
    }
}
