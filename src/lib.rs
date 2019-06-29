//! A stream of chars for building such as a lexer. Making the step of "iteration between characters" considerably easier.
//! And providing certain utilites for making the code simpler.
//! Respects both ASCII and Unicode.
//!
//! Example, lexing identifiers, numbers and some punctuation marks:
//!
//! ```rust
//! use uwl::StringStream;
//! use uwl::StrExt;
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
//!         Token {
//!             kind,
//!             lit,
//!         }
//!     }
//! }
//!
//! fn lex<'a>(stream: &mut StringStream<'a>) -> Option<Token<'a>> {
//!     if stream.at_end() {
//!         return None;
//!     }
//!
//!     Some(match stream.current()? {
//!         // Ignore whitespace.
//!         s if s.is_whitespace() => {
//!             stream.next()?;
//!             return lex(stream);
//!         },
//!         s if s.is_alphabetic() => Token::new(TokenKind::Ident, stream.take_while(|s| s.is_alphabetic())),
//!         s if s.is_numeric() => Token::new(TokenKind::Number, stream.take_while(|s| s.is_numeric())),
//!         "?" => Token::new(TokenKind::Question, stream.next()?),
//!         "!" => Token::new(TokenKind::Exclamation, stream.next()?),
//!         "," => Token::new(TokenKind::Comma, stream.next()?),
//!         "." => Token::new(TokenKind::Point, stream.next()?),
//!         _ => Token::new(TokenKind::Illegal, stream.next()?),
//!     })
//! }
//!
//! fn main() {
//!     let mut stream = StringStream::new("Hello, world! ...world? Hello?");
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
#![allow(clippy::should_implement_trait)]

/// Brings over some `is_*` methods from `char` to `&str`,
/// and some methods for identifiers/symbols.
/// 
/// Look at [`char`]'s docs for more reference.
///
/// [`char`]: https://doc.rust-lang.org/stable/std/primitive.char.html
pub trait StrExt {
    /// Does the string consist of numbers? (0-9)
    fn is_numeric(&self) -> bool;
    /// Does the string consist of letters? (A-Z)
    fn is_alphabetic(&self) -> bool;
    /// Does the string consist of letters or numbers? (A-Z; 0-9)
    fn is_alphanumeric(&self) -> bool;
    /// Does the string consist of whitespace? (\n; \r; ' ')
    fn is_whitespace(&self) -> bool;
    /// Does the string consist of letters, numbers or underscores? (A-Z; 0-9; _)
    fn is_diglet(&self) -> bool;
    /// Does the string consist of letters, numbers or hyphens? (A-Z; 0-9; -)
    fn is_kebab(&self) -> bool;
}

impl<T: AsRef<str>> StrExt for T {
    #[inline]
    fn is_numeric(&self) -> bool {
        self.as_ref().chars().all(|c| c.is_numeric())
    }

    #[inline]
    fn is_alphanumeric(&self) -> bool {
        self.as_ref().chars().all(|c| c.is_alphanumeric())
    }

    #[inline]
    fn is_alphabetic(&self) -> bool {
        self.as_ref().chars().all(|c| c.is_alphabetic())
    }

    #[inline]
    fn is_whitespace(&self) -> bool {
        self.as_ref().chars().all(|c| c.is_whitespace())
    }

    #[inline]
    fn is_diglet(&self) -> bool {
        self.as_ref()
            .chars()
            .all(|c| c == '_' || c.is_alphanumeric())
    }

    #[inline]
    fn is_kebab(&self) -> bool {
        self.as_ref()
            .chars()
            .all(|c| c == '-' || c.is_alphanumeric())
    }
}

// Copied from stackoverflow
// # https://stackoverflow.com/questions/43278245/find-next-char-boundary-index-in-string-after-char
fn find_end(s: &str, i: usize) -> Option<usize> {
    if i > s.len() {
        return None;
    }

    let mut end = i + 1;
    while !s.is_char_boundary(end) {
        end += 1;
    }

    Some(end)
}

/// A stream of chars. Handles both ASCII and Unicode.
///
/// # Note
/// This stream returns *chars* as `&str`s. In instances like [`take_while`], the `&str` refers to actual multi-char substrings (e.g "foo").
///
/// [`take_while`]: #method.take_while
#[derive(Debug, Clone, Default)]
pub struct StringStream<'a> {
    offset: usize,
    /// The source this stream operates on.
    pub src: &'a str,
}

impl<'a> StringStream<'a> {
    /// Create a new stream from a source.
    #[inline]
    pub const fn new(src: &'a str) -> Self {
        StringStream { src, offset: 0 }
    }

    // Find the bound positions of a character, whether ASCII or Unicode.
    #[inline]
    fn char_pos(&self) -> Option<(usize, usize)> {
        if self.at_end() {
            return None;
        }

        Some((self.offset, find_end(self.src, self.offset)?))
    }

    /// Fetch the current char.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let stream = StringStream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some("h"));
    /// ```
    #[inline]
    pub fn current(&self) -> Option<&'a str> {
        let (start, end) = self.char_pos()?;

        Some(&self.src[start..end])
    }

    /// Advance to the next char
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some("h"));
    ///
    /// stream.next();
    /// assert_eq!(stream.current(), Some("e"));
    /// ```
    #[inline]
    pub fn next(&mut self) -> Option<&'a str> {
        let s = self.current()?;
        self.offset += s.len();

        Some(s)
    }

    /// Advance by x chars.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello world");
    ///
    /// assert_eq!(stream.advance(5), Some("hello"));
    /// stream.next();
    /// assert_eq!(stream.advance(5), Some("world"));
    /// assert!(stream.at_end());
    /// ```
    #[inline]
    pub fn advance(&mut self, much: usize) -> Option<&'a str> {
        if self.at_end() {
            None
        } else {
            let s = self.peek_for(much);
            self.offset += s.len();

            Some(s)
        }
    }

    /// Advance if the leading string matches to the expected input.
    /// Returns `true` on succession, `false` on failure.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello world");
    ///
    /// assert!(stream.eat("hello"));
    /// assert!(!stream.eat("not a space"));
    /// assert!(stream.eat(" "));
    /// assert_eq!(stream.rest(), "world");
    /// ```
    #[inline]
    pub fn eat(&mut self, m: &str) -> bool {
        if self.peek_for(m.chars().count()) == m {
            self.offset += m.len();

            true
        } else {
            false
        }
    }

    /// Lookahead by x chars. Returns the char it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some("h"));
    /// assert_eq!(stream.peek(1), Some("e"));
    /// assert_eq!(stream.current(), Some("h"));
    /// assert_eq!(stream.peek(2), Some("l"));
    /// assert_eq!(stream.current(), Some("h"));
    /// ```
    #[inline]
    pub fn peek(&self, ahead: usize) -> Option<&'a str> {
        self.peek_internal(ahead).1
    }

    /// Lookahead by x chars. Returns a substring up to the end it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello world");
    ///
    /// assert_eq!(stream.current(), Some("h"));
    /// assert_eq!(stream.peek_for(5), "hello");
    ///
    /// for _ in 0..5 {
    ///     stream.next();
    /// }
    ///
    /// assert_eq!(stream.next(), Some(" "));
    /// assert_eq!(stream.peek_for(5), "world");
    /// assert_eq!(stream.next(), Some("w"));
    /// assert_eq!(stream.next(), Some("o"));
    /// assert_eq!(stream.next(), Some("r"));
    /// assert_eq!(stream.next(), Some("l"));
    /// assert_eq!(stream.next(), Some("d"));
    /// ```
    #[inline]
    pub fn peek_for(&self, ahead: usize) -> &'a str {
        self.peek_internal(ahead).0
    }

    /// Lookahead for as long as `f` returns true. Returns a substring up to the end it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::{StringStream, StrExt};
    ///
    /// let mut stream = StringStream::new("hello _wo_r_l_4d");
    ///
    /// assert_eq!(stream.peek_while(|s| s.is_alphabetic()), "hello");
    /// assert_eq!(stream.rest(), "hello _wo_r_l_4d");
    /// stream.take_while(|s| s.is_alphabetic());
    /// stream.next();
    /// assert_eq!(stream.peek_while(|s| s.is_diglet()), "_wo_r_l_4d");
    /// assert_eq!(stream.rest(), "_wo_r_l_4d");
    /// ```
    #[inline]
    pub fn peek_while(&self, f: impl Fn(&str) -> bool) -> &'a str {
        self.clone().take_while(f)
    }

    /// Lookahead for as long as `f` does not return true. Returns a substring up to the end it landed on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello!");
    ///
    /// assert_eq!(stream.peek_until(|s| s == "!"), "hello");
    /// assert_eq!(stream.rest(), "hello!");
    /// ```
    #[inline]
    pub fn peek_until(&self, f: impl Fn(&str) -> bool) -> &'a str {
        self.peek_while(|s| !f(s))
    }

    fn peek_internal(&self, ahead: usize) -> (&'a str, Option<&'a str>) {
        if self.at_end() {
            return ("", None);
        }

        let mut copy = self.clone();

        let pos = copy.offset;

        for _ in 0..ahead {
            copy.next();
        }

        let s = &self.src[pos..copy.offset];
        let c = copy.current();

        (s, c)
    }

    /// Consume while true.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// // Import a few utility methods (for `is_alphabetic`)
    /// use uwl::StrExt;
    ///
    /// let mut stream = StringStream::new("hello");
    ///
    /// assert_eq!(stream.current(), Some("h"));
    /// assert_eq!(stream.take_while(|s| s.is_alphabetic()), "hello");
    /// assert_eq!(stream.current(), None);
    /// ```
    pub fn take_while(&mut self, f: impl Fn(&str) -> bool) -> &'a str {
        if self.at_end() {
            return "";
        }

        let start = self.offset;

        while let Some(s) = self.current() {
            if !f(s) {
                break;
            }

            self.offset += s.len();
        }

        &self.src[start..self.offset]
    }

    /// Consume until true.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("hello!");
    ///
    /// assert_eq!(stream.current(), Some("h"));
    /// assert_eq!(stream.take_until(|s| s == "!"), "hello");
    /// assert_eq!(stream.current(), Some("!"));
    /// ```
    #[inline]
    pub fn take_until(&mut self, f: impl Fn(&str) -> bool) -> &'a str {
        self.take_while(|s| !f(s))
    }

    /// Slice a portion from the stream by using rules defined by the formatting string
    ///
    /// - `{}` => the portion to return
    /// - `(x)` => optional text *x* that may be present, ignored
    /// - letters/numbers => text to expect
    ///
    /// To espace `{` or `(`, use them twice. For example, `((`/`{{`.
    /// This is not necessary for `}` or `)`.
    ///
    /// Whitespace between `{` and `}` is skipped.
    ///
    /// If parsing does not succeed, this won't advance.
    /// On `Err`, the expected string, or "parse failed", are returned.
    ///
    /// # Examples
    ///
    /// Get anything between html `h1` tags
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("<h1>hello world!</h1>");
    ///
    /// assert_eq!(stream.parse("<h1>{}</h1>"), Ok("hello world!"));
    /// ```
    ///
    /// Parse html tags
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("<h2></h2>");
    ///
    /// // the opening tag - <h2>
    /// assert_eq!(stream.parse("<(/){}>"), Ok("h2"));
    /// // the closing tag - </h2>
    /// assert_eq!(stream.parse("<(/){}>"), Ok("h2"));
    /// ```
    pub fn parse<'b>(&mut self, fmt: &'b str) -> Result<&'a str, &'b str> {
        enum Format<'a> {
            Expect(&'a str),
            Optional(&'a str),
            Parse(Option<&'a str>),
        }

        fn parse<'a>(stream: &mut StringStream<'a>) -> Option<Format<'a>> {
            if stream.at_end() {
                return None;
            }

            if stream.eat("((") {
                return Some(Format::Expect("("));
            }

            if stream.eat("{{") {
                return Some(Format::Expect("{"));
            }

            if stream.eat("(") {
                let e = stream.take_until(|s| s == ")");
                stream.eat(")");
                return Some(Format::Optional(e));
            }

            if stream.eat("{") {
                stream.take_while(|s| s.is_whitespace());
                stream.eat("}");

                return Some(Format::Parse(stream.current()));
            }

            Some(Format::Expect(stream.take_until(|s| s == "(" || s == "{")))
        }

        let pos = self.offset();
        let mut s = StringStream::new(fmt);

        let mut res = None;
        while let Some(fmt) = parse(&mut s) {
            match fmt {
                Format::Expect(e) => {
                    if !self.eat(e) {
                        return Err(e);
                    }
                }
                Format::Optional(e) => {
                    self.eat(e);
                }
                Format::Parse(e) => {
                    res = match e {
                        Some(e) => Some(self.take_until(|s| s == e)),
                        None => Some(self.rest()),
                    };
                }
            }
        }

        match res {
            Some(r) => Ok(r),
            None => {
                // Refresh the offset since we had failed.
                unsafe { self.set_unchecked(pos) };

                Err("parse failed")
            }
        }
    }

    /// Returns the remainder (after the offset).
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("foo bar");
    ///
    /// assert_eq!(stream.take_until(|s| s == " "), "foo");
    /// assert_eq!(stream.next(), Some(" "));
    /// assert_eq!(stream.rest(), "bar");
    #[inline]
    pub fn rest(&self) -> &'a str {
        &self.src[self.offset()..]
    }

    /// Determines the end of the input.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("a");
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

    /// The "offset"; the start of the current char.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("a 🍆");
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
    pub const fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the source the stream is operating on.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let stream = StringStream::new("Once upon a time... life");
    ///
    /// assert_eq!(stream.source(), "Once upon a time... life");
    /// ```
    #[inline]
    pub const fn source(&self) -> &'a str {
        self.src
    }

    /// The provided source's length. Returns the amount of bytes.
    ///
    /// # Example
    ///
    /// ```rust
    /// use uwl::StringStream;
    ///
    /// let mut stream = StringStream::new("abc🍆");
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
    /// use uwl::StringStream;
    /// 
    /// let stream = StringStream::new("");
    /// 
    /// assert!(stream.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Set the offset.
    ///
    /// Panics if the offset is in the middle of a unicode character, or exceeds the length of the input.
    pub fn set(&mut self, pos: usize) {
        if pos > self.src.len() {
            panic!("Position can't be longer than input");
        }

        if !self.src.is_char_boundary(pos) {
            panic!(
                "Invalid position. Cannot set the pos\
                 to be in the middle of a unicode character"
            );
        }

        self.offset = pos;
    }

    /// Set the offset without any checks.
    #[inline]
    pub unsafe fn set_unchecked(&mut self, pos: usize) {
        self.offset = pos;
    }

    /// Increment the offset by bytes.
    ///
    /// Panics if the offset appears to be in the middle of a unicode character.
    pub fn increment(&mut self, bytes: usize) {
        let incr = self.offset + bytes;
        if !self.src.is_char_boundary(incr) {
            panic!("offset in the middle of a character");
        }

        self.offset = incr;
    }

    /// Increment the offset by bytes without any checks.
    #[inline]
    pub unsafe fn increment_unchecked(&mut self, bytes: usize) {
        self.offset += bytes;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate std;
    use self::std::vec::Vec;

    #[test]
    fn all_chars() {
        const STRING: &str = "hello a b c ! ?👀👁!!!";
        let mut s = StringStream::new(STRING);

        let mut v = Vec::with_capacity(STRING.len());

        while let Some(s) = s.next() {
            v.push(s);
        }

        assert_eq!(&v[0], &"h");
        assert_eq!(&v[1], &"e");
        assert_eq!(&v[2], &"l");
        assert_eq!(&v[3], &"l");
        assert_eq!(&v[4], &"o");
        assert_eq!(&v[5], &" ");
        assert_eq!(&v[6], &"a");
        assert_eq!(&v[7], &" ");
        assert_eq!(&v[8], &"b");
        assert_eq!(&v[9], &" ");
        assert_eq!(&v[10], &"c");
        assert_eq!(&v[11], &" ");
        assert_eq!(&v[12], &"!");
        assert_eq!(&v[13], &" ");
        assert_eq!(&v[14], &"?");
        assert_eq!(&v[15], &"👀");
        assert_eq!(&v[16], &"👁");
        assert_eq!(&v[17], &"!");
        assert_eq!(&v[18], &"!");
        assert_eq!(&v[19], &"!");
        assert_eq!(v.len(), 20);

        // There are no other characters beyond index `19`
        assert_eq!(v.get(20), None);
    }

    #[test]
    fn peek() {
        const STRING: &str = "// a comment!";

        let mut s = StringStream::new(STRING);

        assert_eq!(s.current(), Some("/"));
        // Forsee into the future. By one char.
        assert_eq!(s.peek(1), Some("/"));

        // Although `peek` takes by `&mut self`, it shouldn't alter the order of our input we'll want to parse.
        assert_eq!(s.next(), Some("/"));
        assert_eq!(s.next(), Some("/"));

        assert_eq!(&s.src[s.offset()..], " a comment!")
    }
}
