//! A stream designed for the individual manipulation of bytes and Unicode codepoint characters.
//!
//! # Example
//!
//! Using the stream for creating a lexer to tokenize the English language.
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
//! struct Token<'a> {
//!     kind: TokenKind,
//!     lit: &'a str,
//! }
//!
//! impl<'a> Token<'a> {
//!     fn new(kind: TokenKind, lit: &'a str) -> Self {
//!         Self { kind, lit }
//!     }
//! }
//!
//! fn lex<'a>(stream: &mut Stream<'a>) -> Option<Token<'a>> {
//!     let b: u8 = stream.current()?;
//!
//!     if b.is_ascii_whitespace() {
//!         // Ignore whitespace.
//!         stream.take_while(|b| b.is_ascii_whitespace());
//!         return lex(stream);
//!     }
//!
//!     if b.is_ascii_digit() {
//!         let lit = stream.take_while(|b| b.is_ascii_digit());
//!         return Some(Token::new(TokenKind::Number, lit));
//!     }
//!
//!     if b.is_ascii_alphabetic() {
//!         let lit = stream.take_while(|b| b.is_ascii_alphabetic());
//!         return Some(Token::new(TokenKind::Ident, lit));
//!     }
//!
//!     let token = match b {
//!         b'?' => Some(Token::new(TokenKind::Question, &stream.rest()[..1])),
//!         b'!' => Some(Token::new(TokenKind::Exclamation, &stream.rest()[..1])),
//!         b',' => Some(Token::new(TokenKind::Comma, &stream.rest()[..1])),
//!         b'.' => Some(Token::new(TokenKind::Point, &stream.rest()[..1])),
//!         _ => Some(Token::new(TokenKind::Illegal, &stream.rest()[..1])),
//!     };
//!
//!     stream.next();
//!
//!     token
//! }
//!
//! fn main() {
//!     let mut stream = Stream::new("Hello, world! ...world? Hello?");
//!
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, "Hello")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Comma, ",")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, "world")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Exclamation, "!")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Point, ".")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Point, ".")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Point, ".")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, "world")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Question, "?")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Ident, "Hello")));
//!     assert_eq!(lex(&mut stream), Some(Token::new(TokenKind::Question, "?")));
//!
//!     // Reached the end
//!     assert_eq!(lex(&mut stream), None);
//! }
//! ```

#![no_std]
#![doc(html_root_url = "https://docs.rs/uwl/*")]
#![deny(rust_2018_idioms)]
#![cfg_attr(test, feature(test))]

/// A stream of bytes and characters.
#[derive(Debug, Default, Clone, Copy)]
pub struct Stream<'a> {
    src: &'a [u8],
    offset: usize,
}

impl<'a> Stream<'a> {
    /// Create a new stream from a string source.
    #[inline]
    pub fn new(src: &'a str) -> Self {
        Self {
            src: src.as_bytes(),
            offset: 0,
        }
    }

    /// Returns the current position of the stream.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("an 🍆");
    ///
    /// assert_eq!(stream.offset(), 0);
    /// stream.next();
    /// assert_eq!(stream.offset(), 1);
    /// stream.next();
    /// assert_eq!(stream.offset(), 2);
    /// stream.next();
    /// assert_eq!(stream.offset(), 3);
    /// stream.next_char();
    /// assert_eq!(stream.offset(), 7);
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
        // This is safe for as long as the passed source had been constructed
        // in a safe manner.
        unsafe { core::str::from_utf8_unchecked(self.src) }
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

    /// Returns a boolean indicating whether there are no more bytes to parse.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("a");
    ///
    /// assert!(!stream.is_empty());
    /// stream.next();
    /// assert!(stream.is_empty());
    /// assert_eq!(stream.current(), None);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.offset >= self.len()
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
    /// assert_eq!(stream.take_until(|s| s == b' '), "foo");
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.rest(), "bar");
    #[inline]
    pub fn rest(&self) -> &'a str {
        &self.source()[self.offset..]
    }

    /// Look ahead by the `amount` of bytes.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.peek(1), Some(b'e'));
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.peek(2), Some(b'l'));
    /// assert_eq!(stream.current(), Some(b'h'));
    /// ```
    #[inline]
    pub fn peek(&self, amount: usize) -> Option<u8> {
        self.src.get(self.offset + amount).copied()
    }

    /// Look ahead by the `amount` of characters.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("🍆👅🍆");
    ///
    /// assert_eq!(stream.current_char(), Some('🍆'));
    /// assert_eq!(stream.peek_char(0), Some('🍆'));
    /// assert_eq!(stream.current_char(), Some('🍆'));
    /// assert_eq!(stream.peek_char(1), Some('👅'));
    /// assert_eq!(stream.current_char(), Some('🍆'));
    /// assert_eq!(stream.peek_char(2), Some('🍆'));
    /// ```
    #[inline]
    pub fn peek_char(&self, amount: usize) -> Option<char> {
        self.source()[self.offset..].chars().nth(amount)
    }

    /// Fetch the current byte.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// ```
    #[inline]
    pub fn current(&self) -> Option<u8> {
        self.peek(0)
    }

    /// Fetch the current character.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let stream = Stream::new("😃 😂");
    ///
    /// assert_eq!(stream.current_char(), Some('😃'));
    /// ```
    #[inline]
    pub fn current_char(&self) -> Option<char> {
        self.peek_char(0)
    }

    /// Advance to the next byte. Returns the current byte prior to advancement.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    ///
    /// assert_eq!(stream.next(), Some(b'h'));
    /// assert_eq!(stream.current(), Some(b'e'));
    /// ```
    #[inline]
    pub fn next(&mut self) -> Option<u8> {
        self.current().map(|c| {
            self.offset += 1;

            c
        })
    }

    /// Advance to the next character.
    /// Returns the current character prior to advancement.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("😃 😂");
    ///
    /// assert_eq!(stream.next_char(), Some('😃'));
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.current_char(), Some('😂'));
    /// ```
    #[inline]
    pub fn next_char(&mut self) -> Option<char> {
        self.current_char().map(|c| {
            self.offset += c.len_utf8();

            c
        })
    }

    /// Look ahead based on a predicate while it returns true.
    /// Returns a string before the lookahead and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello _wo_r_l_4d");
    ///
    /// assert_eq!(stream.peek_while(|b| b.is_ascii_alphabetic()), "hello");
    /// assert_eq!(stream.rest(), "hello _wo_r_l_4d");
    /// stream.take_while(|b| b.is_ascii_alphabetic());
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.peek_while(|b| b == b'_' || b.is_ascii_alphanumeric()), "_wo_r_l_4d");
    /// assert_eq!(stream.rest(), "_wo_r_l_4d");
    /// ```
    #[inline]
    pub fn peek_while(&self, mut f: impl FnMut(u8) -> bool) -> &'a str {
        if self.is_empty() {
            return "";
        }

        let src = self.src;
        let start = self.offset;
        let mut end = start;

        while let Some(b) = src.get(end) {
            if !f(*b) {
                break;
            }

            end += 1;
        }

        &self.source()[start..end]
    }

    /// Look ahead based on a predicate while it returns true.
    /// Returns a string before the lookahead and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("🍆🍆🍆🍆🍆 _wo_r_l_4d");
    ///
    /// assert_eq!(stream.peek_while_char(|c| c == '🍆'), "🍆🍆🍆🍆🍆");
    /// assert_eq!(stream.rest(), "🍆🍆🍆🍆🍆 _wo_r_l_4d");
    /// stream.take_while_char(|c| c == '🍆');
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.peek_while(|b| b == b'_' || b.is_ascii_alphanumeric()), "_wo_r_l_4d");
    /// assert_eq!(stream.rest(), "_wo_r_l_4d");
    /// ```
    #[inline]
    pub fn peek_while_char(&self, mut f: impl FnMut(char) -> bool) -> &'a str {
        if self.is_empty() {
            return "";
        }

        let src = self.rest();
        let mut end = 0;

        for c in src.chars() {
            if !f(c) {
                break;
            }

            end += c.len_utf8();
        }

        &src[..end]
    }

    /// Look ahead based on a predicate until it returns true.
    /// Returns a string before the lookahead and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello!");
    ///
    /// assert_eq!(stream.peek_until(|b| b == b'!'), "hello");
    /// assert_eq!(stream.rest(), "hello!");
    /// ```
    #[inline]
    pub fn peek_until(&self, mut f: impl FnMut(u8) -> bool) -> &'a str {
        self.peek_while(|c| !f(c))
    }

    /// Look ahead based on a predicate until it returns true.
    /// Returns a string before the lookahead and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello🍆");
    ///
    /// assert_eq!(stream.peek_until_char(|c| c == '🍆'), "hello");
    /// assert_eq!(stream.rest(), "hello🍆");
    /// ```
    #[inline]
    pub fn peek_until_char(&self, mut f: impl FnMut(char) -> bool) -> &'a str {
        self.peek_while_char(|c| !f(c))
    }

    /// Consume bytes based on a predicate while it returns true.
    /// Returns a string before the consumption and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.take_while(|s| s.is_ascii_alphabetic()), "hello");
    /// assert_eq!(stream.current(), None);
    /// ```
    pub fn take_while(&mut self, f: impl FnMut(u8) -> bool) -> &'a str {
        let s = self.peek_while(f);
        self.offset += s.len();
        s
    }

    /// Consume bytes based on a predicate while it returns true.
    /// Returns a string before the consumption and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("🍆🍆🍆");
    ///
    /// assert_eq!(stream.current_char(), Some('🍆'));
    /// assert_eq!(stream.take_while_char(|c| c == '🍆'), "🍆🍆🍆");
    /// assert_eq!(stream.current_char(), None);
    /// ```
    pub fn take_while_char(&mut self, f: impl FnMut(char) -> bool) -> &'a str {
        let s = self.peek_while_char(f);
        self.offset += s.len();
        s
    }

    /// Consume bytes based on a predicate until it returns true.
    /// Returns a string before the consumption and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello!");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.take_until(|b| b == b'!'), "hello");
    /// assert_eq!(stream.current(), Some(b'!'));
    /// ```
    #[inline]
    pub fn take_until(&mut self, mut f: impl FnMut(u8) -> bool) -> &'a str {
        self.take_while(|c| !f(c))
    }

    /// Consume bytes based on a predicate until it returns true.
    /// Returns a string before the consumption and after.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello🍆");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.take_until_char(|c| c == '🍆'), "hello");
    /// assert_eq!(stream.current_char(), Some('🍆'));
    /// ```
    #[inline]
    pub fn take_until_char(&mut self, mut f: impl FnMut(char) -> bool) -> &'a str {
        self.take_while_char(|c| !f(c))
    }

    /// Look ahead by the `amount` of bytes.
    /// Returns a string before the lookahead and after.
    ///
    /// # Note
    ///
    /// If the amount exceeds the amount of available bytes, this will return
    /// the rest of the source.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello world");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.peek_for(5), "hello");
    ///
    /// for _ in 0..5 {
    ///     stream.next();
    /// }
    ///
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.peek_for(5), "world");
    /// assert_eq!(stream.next(), Some(b'w'));
    /// assert_eq!(stream.next(), Some(b'o'));
    /// assert_eq!(stream.peek_for(10), "rld");
    /// assert_eq!(stream.next(), Some(b'r'));
    /// assert_eq!(stream.next(), Some(b'l'));
    /// assert_eq!(stream.next(), Some(b'd'));
    /// ```
    #[inline]
    pub fn peek_for(&self, amount: usize) -> &'a str {
        let src = self.rest();

        if src.len() <= amount {
            return src;
        }

        &src[..amount]
    }

    /// Look ahead by the `amount` of characters.
    /// Returns a string before the lookahead and after.
    ///
    /// # Note
    ///
    /// If the amount exceeds the amount of available characters,
    /// this will return the rest of the source.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello 🍆🍆 🍆🍆🍆🍆");
    ///
    /// assert_eq!(stream.current(), Some(b'h'));
    /// assert_eq!(stream.peek_for_char(5), "hello");
    ///
    /// for _ in 0..5 {
    ///     stream.next();
    /// }
    ///
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.peek_for_char(2), "🍆🍆");
    /// assert_eq!(stream.peek_for_char(10), "🍆🍆 🍆🍆🍆🍆");
    /// ```
    #[inline]
    pub fn peek_for_char(&self, amount: usize) -> &'a str {
        let src = self.rest();
        let end = src
            .chars()
            .take(amount)
            .fold(0, |acc, c| acc + c.len_utf8());

        if src.len() <= end {
            return src;
        }

        &src[..end]
    }

    /// Advance onward by the `amount` of bytes.
    /// Returns a string before the advancement and after.
    ///
    /// # Note
    ///
    /// If the amount exceeds the amount of available bytes, this will return
    /// the rest of the source.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello world");
    ///
    /// assert_eq!(stream.advance(5), "hello");
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.advance(2), "wo");
    /// assert_eq!(stream.advance(5), "rld");
    /// assert!(stream.is_empty());
    /// ```
    #[inline]
    pub fn advance(&mut self, amount: usize) -> &'a str {
        let s = self.peek_for(amount);
        self.offset += s.len();
        s
    }

    /// Advance onward by the `amount` of bytes.
    /// Returns a string before the advancement and after.
    ///
    /// # Note
    ///
    /// If the amount exceeds the amount of available bytes, this will return
    /// the rest of the source.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::Stream;
    ///
    /// let mut stream = Stream::new("hello 🍆🍆 🍆🍆🍆");
    ///
    /// assert_eq!(stream.advance_char(5), "hello");
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.advance_char(2), "🍆🍆");
    /// assert_eq!(stream.next(), Some(b' '));
    /// assert_eq!(stream.advance_char(6), "🍆🍆🍆");
    /// assert!(stream.is_empty());
    /// ```
    #[inline]
    pub fn advance_char(&mut self, amount: usize) -> &'a str {
        let s = self.peek_for_char(amount);
        self.offset += s.len();
        s
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
        let s = self.peek_for_char(m.chars().count());

        if s == m {
            self.offset += s.len();

            true
        } else {
            false
        }
    }

    /// Set the offset to the `pos`.
    #[inline]
    pub fn set(&mut self, pos: usize) {
        self.offset = pos;
    }

    /// Increments the offset by the `amount`
    #[inline]
    pub fn increment(&mut self, amount: usize) {
        self.offset += amount;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    extern crate test;

    use alloc::vec::Vec;

    #[test]
    fn all_chars() {
        const STRING: &str = "hello a b c ! ?👀👁!!!";
        let mut v = Vec::with_capacity(STRING.len());
        let mut s = Stream::new(STRING);

        while let Some(c) = s.next() {
            v.push(c);
        }

        assert_eq!(v[0], b'h');
        assert_eq!(v[1], b'e');
        assert_eq!(v[2], b'l');
        assert_eq!(v[3], b'l');
        assert_eq!(v[4], b'o');
        assert_eq!(v[5], b' ');
        assert_eq!(v[6], b'a');
        assert_eq!(v[7], b' ');
        assert_eq!(v[8], b'b');
        assert_eq!(v[9], b' ');
        assert_eq!(v[10], b'c');
        assert_eq!(v[11], b' ');
        assert_eq!(v[12], b'!');
        assert_eq!(v[13], b' ');
        assert_eq!(v[14], b'?');
        assert_eq!(&v[15..19], "👀".as_bytes());
        assert_eq!(&v[19..23], "👁".as_bytes());
        assert_eq!(v[23], b'!');
        assert_eq!(v[24], b'!');
        assert_eq!(v[25], b'!');
        assert_eq!(v.len(), 26);

        // There are no other characters beyond index `26`
        assert_eq!(v.get(26), None);

        assert_eq!(core::str::from_utf8(&v), Ok(STRING));
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
        struct Token<'a> {
            kind: TokenKind,
            lit: &'a str,
        }

        impl<'a> Token<'a> {
            fn new(kind: TokenKind, lit: &'a str) -> Self {
                Self { kind, lit }
            }
        }

        return b.iter(|| {
            const SRC: &str = "(abc foo bar) ()() 1 2 3 4 5 6 7 8 9";

            let mut stream = Stream::new(SRC);

            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Paren, "(")));
            assert_eq!(
                lit(&mut stream),
                Some(Token::new(TokenKind::Identifier, "abc"))
            );
            assert_eq!(
                lit(&mut stream),
                Some(Token::new(TokenKind::Identifier, "foo"))
            );
            assert_eq!(
                lit(&mut stream),
                Some(Token::new(TokenKind::Identifier, "bar"))
            );
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::CParen, ")")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Paren, "(")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::CParen, ")")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Paren, "(")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::CParen, ")")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "1")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "2")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "3")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "4")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "5")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "6")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "7")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "8")));
            assert_eq!(lit(&mut stream), Some(Token::new(TokenKind::Number, "9")));
            assert_eq!(lit(&mut stream), None);
        });

        fn is_ident_start(b: u8) -> bool {
            b == b'_' || b.is_ascii_alphabetic()
        }

        fn is_ident_continue(b: u8) -> bool {
            is_ident_start(b) || b.is_ascii_digit()
        }

        fn lit<'a>(s: &mut Stream<'a>) -> Option<Token<'a>> {
            let b = s.current()?;

            if b.is_ascii_whitespace() {
                s.take_while(|b| b.is_ascii_whitespace());
                return lit(s);
            }

            if b.is_ascii_digit() {
                let lit = s.take_while(|b| b.is_ascii_digit());
                return Some(Token::new(TokenKind::Number, lit));
            }

            if is_ident_start(b) {
                let lit = s.take_while(|b| is_ident_continue(b));
                return Some(Token::new(TokenKind::Identifier, lit));
            }

            let kind = match b {
                b'(' => TokenKind::Paren,
                b')' => TokenKind::CParen,
                _ => TokenKind::Illegal,
            };

            let lit = &s.rest()[..1];
            s.next();

            Some(Token::new(kind, lit))
        }
    }
}
