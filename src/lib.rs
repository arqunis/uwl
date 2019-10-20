//! A stream of chars for building such as a lexer. Making the step of "iteration between characters" considerably easier.
//! And providing certain utilites for making the code simpler.
//! Respects both ASCII and Unicode.
//!
//! Example, lexing identifiers, numbers and some punctuation marks:
//!
//! ```rust
//! use uwl::Stream;
//!
//! #[derive(Debug, PartialEq)]
//! enum TokenKind {
//!     Ident,
//!     Number,
//!     Question,
//!     Exclamation,
//!     Comma,
//!     Point,
//!
//!     // An invalid token
//!     Illegal,
//! }
//!
//! #[derive(Debug, PartialEq)]
//! enum Lit<'a> {
//!     Short(char),
//!     Long(&'a str),
//! }
//!
//! #[derive(Debug, PartialEq)]
//! struct Token<'a> {
//!     kind: TokenKind,
//!     lit: Lit<'a>,
//! }
//!
//! impl<'a> Token<'a> {
//!     fn new(kind: TokenKind, lit: Lit<'a>) -> Self {
//!         Token {
//!             kind,
//!             lit,
//!         }
//!     }
//! }
//!
//! fn lex<'a>(stream: &mut Stream<'a>) -> Option<Token<'a>> {
//!     match stream.current() {
//!         Some(c) => match c {
//!             // Ignore whitespace.
//!             s if s.is_whitespace() => {
//!                 stream.take_while(|c| c.is_whitespace());
//!                 return lex(stream);
//!             },
//!             s if s.is_alphabetic() => {
//!                 let lit = Lit::Long(stream.take_while(|s| s.is_alphabetic()));
//!                 Some(Token::new(TokenKind::Ident, lit))
//!             },
//!             s if s.is_numeric() => {
//!                 let lit = Lit::Long(stream.take_while(|s| s.is_numeric()));
//!                 Some(Token::new(TokenKind::Number, lit))
//!             },
//!             '?' => Some(Token::new(TokenKind::Question, Lit::Short(stream.next()?))),
//!             '!' => Some(Token::new(TokenKind::Exclamation, Lit::Short(stream.next()?))),
//!             ',' => Some(Token::new(TokenKind::Comma, Lit::Short(stream.next()?))),
//!             '.' => Some(Token::new(TokenKind::Point, Lit::Short(stream.next()?))),
//!             _ => Some(Token::new(TokenKind::Illegal, Lit::Short(stream.next()?))),
//!         },
//!         None => None,
//!     }
//! }
//!
//! fn main() {
//!     let mut stream = Stream::new("Hello, world! ...world? Hello?");
//!
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, Lit::Long("Hello"))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Comma, Lit::Short(','))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, Lit::Long("world"))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Exclamation, Lit::Short('!'))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Point, Lit::Short('.'))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Point, Lit::Short('.'))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Point, Lit::Short('.'))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, Lit::Long("world"))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Question, Lit::Short('?'))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, Lit::Long("Hello"))));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Question, Lit::Short('?'))));
//!
//!     // Reached the end
//!     assert_eq!(lex(&mut stream), None);
//! }
//! ```

#![no_std]
#![doc(html_root_url = "https://docs.rs/uwl/*")]
#![deny(rust_2018_idioms)]
#![cfg_attr(test, feature(test))]

/// Adds additional `is_*` methods to `char`,
pub trait CharExt: Copy {
    /// Is the character fit for the beginning of an identifier? (A-Z)
    fn is_ident_start(self) -> bool;
    /// Is the character fit for continuing the identifier? (A-Z; 0-9; _)
    fn is_ident_continue(self) -> bool;
    /// Is the character fit for continuing the identifier in kebab-case? (A-Z; 0-9; -)
    fn is_kebab_continue(self) -> bool;
}

impl CharExt for char {
    #[inline]
    fn is_ident_start(self) -> bool {
        self.is_ascii_alphabetic()
    }

    #[inline]
    fn is_ident_continue(self) -> bool {
        self == '_' || self.is_ident_start()
    }

    #[inline]
    fn is_kebab_continue(self) -> bool {
        self == '-' || self.is_ident_start()
    }
}

#[inline]
fn current_char(src: &str, offset: usize) -> Option<char> {
    src[offset..].chars().next()
}

#[inline]
fn peek_char(src: &str, mut offset: usize, ahead: usize) -> Option<char> {
    for _ in 0..ahead {
        let c = current_char(src, offset)?;

        offset += c.len_utf8();
    }

    current_char(src, offset)
}

#[inline]
fn take_while(src: &str, mut offset: usize, mut f: impl FnMut(char) -> bool) -> &str {
    let start = offset;

    while let Some(c) = current_char(src, offset) {
        if !f(c) {
            break;
        }

        offset += c.len_utf8();
    }

    &src[start..offset]
}

/// A stream of characters. Handles ASCII and/or Unicode.
#[derive(Debug, Default, Clone, Copy)]
pub struct Stream<'a> {
    src: &'a str,
    offset: usize,
    buf: Option<char>,
}

impl<'a> Stream<'a> {
    /// Create a new stream from a source.
    #[inline]
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            offset: 0,
            buf: current_char(src, 0),
        }
    }

    /// The "offset"; the start of the current char.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("a 🍆");
    ///
    /// assert_eq!(stream.offset(), 0);
    /// stream.next();
    /// assert_eq!(stream.offset(), 1);
    /// stream.next();
    /// assert_eq!(stream.offset(), 2);
    /// stream.next();
    /// assert_eq!(stream.offset(), 6);
    /// ```
    #[inline]
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the source the stream is operating on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let stream = Stream::new("Once upon a time... life");
    ///
    /// assert_eq!(stream.source(), "Once upon a time... life");
    /// ```
    #[inline]
    pub fn source(&self) -> &'a str {
        self.src
    }

    /// The provided source's length. Returns the amount of bytes.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("abc🍆");
    /// assert_eq!(stream.len(), 7);
    /// stream.next();
    /// // Regardless of any modification method present on the stream,
    /// // `len` always returns a constant.
    /// assert_eq!(stream.len(), 7);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.src.len()
    }

    /// Is the provided source empty?
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let stream = Stream::new("");
    ///
    /// assert!(stream.is_empty());
    /// assert_eq!(stream.source(), "");
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the remainder (after the offset).
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("foo bar");
    ///
    /// assert_eq!(stream.take_until(|s| s == ' '), "foo");
    /// assert_eq!(stream.next(), Some(' '));
    /// assert_eq!(stream.rest(), "bar");
    #[inline]
    pub fn rest(&self) -> &'a str {
        &self.src[self.offset..]
    }

    /// Determines the end of the input.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("a");
    ///
    /// assert!(!stream.at_end());
    /// stream.next();
    /// assert!(stream.at_end());
    /// assert_eq!(stream.current(), None);
    /// ```
    #[inline]
    pub fn at_end(&self) -> bool {
        self.offset >= self.len()
    }

    /// Fetch the current char.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some('h'));
    /// ```
    #[inline]
    pub fn current(&self) -> Option<char> {
        self.buf
    }

    /// Advance to the next char
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some('h'));
    ///
    /// assert_eq!(stream.next(), Some('h'));
    /// assert_eq!(stream.current(), Some('e'));
    /// ```
    #[inline]
    pub fn next(&mut self) -> Option<char> {
        let buf = self.buf;

        if let Some(c) = buf {
            self.offset += c.len_utf8();
            self.buf = current_char(self.src, self.offset);
        }

        buf
    }

    /// Consume while true.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some('h'));
    /// assert_eq!(stream.take_while(|s| s.is_alphabetic()), "hello");
    /// assert_eq!(stream.current(), None);
    /// ```
    pub fn take_while(&mut self, f: impl FnMut(char) -> bool) -> &'a str {
        if self.at_end() {
            return "";
        }

        let s = take_while(self.src, self.offset, f);

        self.offset += s.len();
        self.buf = current_char(self.src, self.offset);

        s
    }

    /// Consume until true.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello!");
    ///
    /// assert_eq!(stream.current(), Some('h'));
    /// assert_eq!(stream.take_until(|s| s == '!'), "hello");
    /// assert_eq!(stream.current(), Some('!'));
    /// ```
    #[inline]
    pub fn take_until(&mut self, mut f: impl FnMut(char) -> bool) -> &'a str {
        self.take_while(|c| !f(c))
    }

    /// Lookahead for as long as `f` returns true. Returns a substring up to the ending character
    /// that it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::{Stream, CharExt};
    ///
    /// let mut stream = Stream::new("hello _wo_r_l_4d");
    ///
    /// assert_eq!(stream.peek_while(|s| s.is_alphabetic()), "hello");
    /// assert_eq!(stream.rest(), "hello _wo_r_l_4d");
    /// stream.take_while(|s| s.is_alphabetic());
    /// stream.next();
    /// assert_eq!(stream.peek_while(|s| s.is_diglet()), "_wo_r_l_4d");
    /// assert_eq!(stream.rest(), "_wo_r_l_4d");
    /// ```
    #[inline]
    pub fn peek_while(&self, f: impl FnMut(char) -> bool) -> &'a str {
        if self.at_end() {
            return "";
        }

        take_while(self.src, self.offset, f)
    }

    /// Lookahead for as long as `f` does not return true. Returns a substring up to the end it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello!");
    ///
    /// assert_eq!(stream.peek_until(|s| s == '!'), "hello");
    /// assert_eq!(stream.rest(), "hello!");
    /// ```
    #[inline]
    pub fn peek_until(&self, mut f: impl FnMut(char) -> bool) -> &'a str {
        self.peek_while(|c| !f(c))
    }

    /// Lookahead by `x` chars. Returns a substring up to the ending character
    /// that it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello world");
    ///
    /// assert_eq!(stream.current(), Some('h'));
    /// assert_eq!(stream.peek_for(5), "hello");
    ///
    /// for _ in 0..5 {
    ///     stream.next();
    /// }
    ///
    /// assert_eq!(stream.next(), Some(' '));
    /// assert_eq!(stream.peek_for(5), "world");
    /// assert_eq!(stream.next(), Some('w'));
    /// assert_eq!(stream.next(), Some('o'));
    /// assert_eq!(stream.next(), Some('r'));
    /// assert_eq!(stream.next(), Some('l'));
    /// assert_eq!(stream.next(), Some('d'));
    /// ```
    #[inline]
    pub fn peek_for(&self, mut much: usize) -> &'a str {
        self.peek_while(|_| {
            let b = 0 < much;
            much -= 1;
            b
        })
    }

    /// Advance by `x` characters. Short-circuits
    /// if there are no more characters available.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello world");
    ///
    /// assert_eq!(stream.advance(5), "hello");
    /// stream.next();
    /// assert_eq!(stream.advance(5), "world");
    /// assert!(stream.at_end());
    /// ```
    #[inline]
    pub fn advance(&mut self, mut much: usize) -> &'a str {
        self.take_while(|_| {
            let b = 0 < much;
            much -= 1;
            b
        })
    }

    /// Advance if the leading string matches to the expected input.
    /// Returns `true` on succession, `false` on failure.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello world");
    ///
    /// assert!(stream.eat("hello"));
    /// assert!(!stream.eat("not a space"));
    /// assert!(stream.eat(" "));
    /// assert_eq!(stream.rest(), "world");
    /// ```
    #[inline]
    pub fn eat(&mut self, m: &str) -> bool {
        let s = self.peek_for(m.chars().count());

        if s == m {
            self.offset += s.len();

            true
        } else {
            false
        }
    }

    /// Lookahead by `x` characters. Returns the character it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some('h'));
    /// assert_eq!(stream.peek(1), Some('e'));
    /// assert_eq!(stream.current(), Some('h'));
    /// assert_eq!(stream.peek(2), Some('l'));
    /// assert_eq!(stream.current(), Some('h'));
    /// ```
    #[inline]
    pub fn peek(&self, ahead: usize) -> Option<char> {
        peek_char(self.src, self.offset, ahead)
    }

    /// Set the offset to the `pos`.
    #[inline]
    pub fn set(&mut self, pos: usize) {
        self.offset = pos;
    }

    /// Increment the offset by `n` bytes.
    #[inline]
    pub fn increment(&mut self, n: usize) {
        self.offset += n;
        self.buf = current_char(self.src, self.offset);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    extern crate test;

    use alloc::string::String;
    use alloc::vec::Vec;

    #[test]
    fn all_chars() {
        const STRING: &str = "hello a b c ! ?👀👁!!!";
        let mut v = Vec::with_capacity(STRING.len());
        let mut s = Stream::new(STRING);

        while let Some(c) = s.next() {
            v.push(c);
        }

        assert_eq!(v[0], 'h');
        assert_eq!(v[1], 'e');
        assert_eq!(v[2], 'l');
        assert_eq!(v[3], 'l');
        assert_eq!(v[4], 'o');
        assert_eq!(v[5], ' ');
        assert_eq!(v[6], 'a');
        assert_eq!(v[7], ' ');
        assert_eq!(v[8], 'b');
        assert_eq!(v[9], ' ');
        assert_eq!(v[10], 'c');
        assert_eq!(v[11], ' ');
        assert_eq!(v[12], '!');
        assert_eq!(v[13], ' ');
        assert_eq!(v[14], '?');
        assert_eq!(v[15], '👀');
        assert_eq!(v[16], '👁');
        assert_eq!(v[17], '!');
        assert_eq!(v[18], '!');
        assert_eq!(v[19], '!');
        assert_eq!(v.len(), 20);

        // There are no other characters beyond index `19`
        assert_eq!(v.get(20), None);

        assert_eq!(v.into_iter().collect::<String>(), STRING);
    }

    #[test]
    fn peek() {
        const STRING: &str = "// a comment!";

        let mut s = Stream::new(STRING);

        assert_eq!(s.current(), Some('/'));
        assert_eq!(s.peek(0), Some('/'));
        assert_eq!(s.peek(1), Some('/'));
        assert_eq!(s.peek(2), Some(' '));

        assert_eq!(s.next(), Some('/'));
        assert_eq!(s.next(), Some('/'));
        assert_eq!(s.rest(), " a comment!");
    }

    #[bench]
    fn lang(b: &mut test::Bencher) {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum TokenKind {
            Illegal,
            Identifier,
            Number,
            Paren,
            CParen,
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum Lit<'a> {
            Short(char),
            Long(&'a str),
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Token<'a> {
            kind: TokenKind,
            lit: Lit<'a>,
        }

        return b.iter(|| {
            const SRC: &str = "(abc foo bar) ()() 1 2 3 4 5 6 7 8 9";

            let mut stream = Stream::new(SRC);

            while let Some(_) = lit(&mut stream) {}
        });

        fn lit<'a>(s: &mut Stream<'a>) -> Option<Token<'a>> {
            match s.current() {
                Some(c) => {
                    if c.is_ident_start() {
                        let l = Lit::Long(s.take_while(|c| c.is_ident_continue()));

                        Some(Token {
                            kind: TokenKind::Identifier,
                            lit: l,
                        })
                    } else if c.is_ascii_digit() {
                        let l = Lit::Long(s.take_while(|c| c.is_ascii_digit()));

                        Some(Token {
                            kind: TokenKind::Number,
                            lit: l,
                        })
                    } else {
                        s.next();

                        let kind = match c {
                            '(' => TokenKind::Paren,
                            ')' => TokenKind::CParen,
                            _ => TokenKind::Illegal,
                        };

                        Some(Token {
                            kind,
                            lit: Lit::Short(c),
                        })
                    }
                }
                None => None,
            }
        }
    }
}
