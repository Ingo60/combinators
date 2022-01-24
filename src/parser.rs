use std::str::from_utf8;

pub trait Parser<S, R, E> {
    /// Run a parser. The result is a tuple, whose first component
    /// indicates the number of items consumed.
    /// The second is the actual result.
    ///
    /// Note that for utf-8 string parsers, the number of consumed items is bytes, not chars.
    /// Furthermore, the sub-slice of the input starting at that position is not
    /// neccesarily a valid string.
    ///
    /// This is because strings are represented as sequences of UTF-8 bytes, where characters may be represented in up to 4 bytes.
    ///
    /// For example, the
    ///
    /// Example:
    /// ```
    /// expect('e').then(expect('z')).parse_raw("èz".as_bytes())
    /// ```
    fn parse_raw(&self, src: &[S]) -> (usize, Result<R, E>);
    fn parse(&self, src: &[S]) -> Result<R, E> {
        let (_, it) = self.parse_raw(src);
        it
    }
}

/// # A sub-trait for parsers you want to run on `str` slices (aka strings).
///
/// You need to consider that str slices are in reality nothing more than u8 slices
/// that are guaranteed to contain valid UTF-8 byte sequences.
///
/// This means that the actual parsing works on u8 slices. The parser
/// needs to keep track of the current offset and will also record
/// the number of consumed bytes (**not** characters). All such
/// numbers will always point to the next valid utf8-sequence if there is any.
///
/// However, that doesn't mean it cannot point "inside" something you would normally
/// recognize as "a character". Look, briefly said, things are like this:
/// - a "character" (recognizable graphical symbol with some meaning, say è, like in *Cafè*)
/// can consist of a sequence of unicode code points.
/// - each such codepoint has an UTF-8 encoding that takes from 1 to 4 bytes.
///
/// ## The easy case
///
/// If the lexical grammar you need to parse consists of ASCII only characters, consider yourself lucky.
/// This is because each ASCII character's value is also the value of its unicode code point and each such
/// code point takes exactly 1 byte and it so happens that the value of that byte is the same as the ASCII code.
///
/// (Your parser may still report an error inside an international character that occurs in the input. See below.)
///
/// ## The asian case
///
/// I don't want even begin to think about the difficulties that will arise with text written in a system that isn't
/// based on the brilliant idea of the ancient phoenicians: a small set of symbols, called letters, that can be combined into
/// words and then sentences. I am just incapable of understanding how those systems even work that they use in asia,
/// therefore I'm not in a position to say whether our parsers can handle them.
///
/// ## The "phoenician" case
///
/// It doesn't matter what the set of letters is: cyrillic, greek, latin, they should all work fairly well.
///
/// I'm unsure how right-to-left written texts will fare. There is perhaps a way to reverse them somehow? I have no idea.
///
/// There is, however, the question
///
/// ## Why does the Unicode consortium hates programmers so much?
///
/// Here is some code to demonstrate that they do hate us:
///
/// ```
/// let ez1 = "èz"; // U+00E8 LATIN SMALL LETTER E WITH GRAVE, z
/// let ez2 = "èz"; // e, U+0300 COMBINING GRAVE ACCENT, z
///
/// assert_ne!(ez1, ez2);
/// ```
///
/// Now consider the following parsers and their outcome:
/// ```
/// println!(
///     "{:?} in {:?} \"{}\"",
///     expect('e').then(expect('z')).parse_str_raw(ez1),
///     ez1.as_bytes(),
///     ez1
/// );
/// (0, Err("'e' expected")) in [195, 168, 122] "èz"
/// ```
///
/// Ok, this is fine, so far. We looked for 'e' and found 'è'.
///
/// Can we parse that 'è' also?
///
/// ```
/// println!(
///     "{:?} in {:?} \"{}\"",
///     expect('è').then(expect('z')).parse_str_raw(ez1),
///     ez1.as_bytes(),
///     ez1
/// );
/// (3, Ok(('è', 'z'))) in [195, 168, 122] "èz"
/// ```
///
/// Yess! But wait, how about this:
///
/// ```
/// println!(
///     "{:?} in {:?} \"{}\"",
///     expect('è').then(expect('z')).parse_str_raw(ez2),
///     ez2.as_bytes(),
///     ez2
/// );
/// (0, Err("'è' ([195, 168]) expected")) in [101, 204, 128, 122] "èz"
/// ```
///
/// What's going on here? Isn't this the same string as before?
/// No, it isn't, as the `assert_ne` above and the printout of the byte arrays confirms.
/// Only the string representation seems to indicate they are the same.
///
/// Turns out, there are hundreds and hundreds of "characters" that can occur as a single unicode point
/// (e.g. U+00E8 LATIN SMALL LETTER E WITH GRAVE) or as a sequence of unicode points
/// (e.g. U+0065 LATIN SMALL LETTER E, U+0300 COMBINING GRAVE ACCENT). Hence the following works:
///
/// ```
/// println!(
///     "{:?} in {:?} \"{}\"",
///     expect('e')
///         .then(expect('\u{300}'))
///         .then(expect('z'))
///         .parse_str_raw(ez2),
///     ez2.as_bytes(),
///     ez2
/// );
/// (4, Ok((('e', '\u{300}'), 'z'))) in [101, 204, 128, 122] "èz"
/// ```
/// Interestingly, we have consumed 4 bytes and collected 3 "characters" from a string that apparently has a length of 2.
///
/// Also note that the initial 101 (hexadecimal 0x65) is
/// our old friend, the ordinary ASCII 'e'.
/// This can lead to the following situation:
///
/// ```
/// let (bytes, err) = expect('e').then(expect('z')).parse_str_raw(ez2);
/// println!(
///     "({}, {:?} remaining input {:?}",
///     bytes, err,
///     from_utf8(&ez2.as_bytes()[bytes..]),
/// );
/// (1, Err("'z' expected") remaining input Ok("\u{300}z")
/// ```
///
/// Here, the parser did consume the leading 'e' and got stuck "inside" the unicode 'è'.
///
/// ## Conclusion
///
///

pub trait StrParser<R, E>: Parser<u8, R, E> {
    fn parse_str_raw(&self, src: &str) -> (usize, Result<R, E>) {
        self.parse_raw(src.as_bytes())
    }
    fn parse_str(&self, src: &str) -> Result<R, E> {
        self.parse(src.as_bytes())
    }
}

type ParseResult<R, E> = (usize, Result<R, E>);
type ParserFunc<S, R, E> = Box<dyn Fn(&[S]) -> (usize, Result<R, E>)>;

// #[derive(Clone)]
struct _AB<S, RA, E, RB> {
    p1: Box<dyn Parser<S, RA, E>>,
    p2: Box<dyn Parser<S, RB, E>>,
    p3: Box<dyn Fn(&[S]) -> (usize, Result<RB, E>)>,
}

pub struct GenericP<S, R, E> {
    run: ParserFunc<S, R, E>,
}

impl<S, R, E> Clone for GenericP<S, R, E>
where
    S: 'static,
    E: 'static,
    R: 'static,
{
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<S, R, E> GenericP<S, R, E>
where
    S: 'static,
    R: 'static,
    E: 'static,
{
    /// `p.label("message")` causes the error message to be `"message"` when `p` fails.
    ///
    /// The error will be reported at the position where `p` was attempted,
    /// not necessarily at the position where `p` failed.
    ///
    ///
    /// > `expect('a').then(expect('b')).parse_str("a?")`
    ///
    /// will be `1:2 expected 'b', found "?"`, but
    /// > `expect('a').then(expect('b')).label("no ab today").parse_str("a?")`
    ///
    /// will be `1:1 no ab today, found "a?"`
    pub fn label(self, lbl: &'static str) -> GenericP<S, R, String> {
        let p = GenericP {
            run: Box::new(self.run),
        };
        GenericP {
            run: Box::new(move |array| match (p.run)(array) {
                (u, e) => (u, e.map_err(|_| lbl.to_string())),
            }),
        }
    }
    /// The monadic bind operation, in Rust generally known as `and_then`
    ///
    /// For `p.and_then(|r| ... code constructing a parser ...)` it operates as follows: first, `p` is run.
    /// When that fails, then the whole expression failes (as if the `.and_then(...)` wasn't present).
    /// Otherwise, the value produced by `p` is passed to the closure, which must construct another parser
    /// whose result is the overall one, be it failure or success.
    ///
    /// Very useful for combining the results of several parsers.
    ///
    pub fn and_then<T>(self, f: impl Fn(R) -> GenericP<S, T, E> + 'static) -> GenericP<S, T, E>
    where
        T: 'static,
    {
        GenericP {
            run: Box::new(move |array| match (self.run)(array) {
                (u, Ok(a)) => match (f(a).run)(&array[u..]) {
                    (v, Ok(b)) => (u + v, Ok(b)),
                    (v, Err(e)) => (u + v, Err(e)),
                },
                (u, Err(err)) => (u, Err(err)),
            }),
        }
    }

    /// `p.then(q)` is an abbrevation for `p.and_then(|_| q)`.
    /// The value produced by `p` is (intentionally) lost.
    /// If you want to keep both values, use `p.and(q)`.
    /// If you want only the value of `q`, use `p.before(q)`
    ///
    /// Here is an inspiring example, where we assume that `expr` parses some expression:
    /// ```
    /// let term = expect('(').then(expr.before(expect(')')))
    /// ```
    pub fn then<T>(self, r: GenericP<S, T, E>) -> GenericP<S, T, E>
    where
        T: 'static,
    {
        let p = GenericP {
            run: Box::new(self.run),
        };
        GenericP {
            run: Box::new(move |array| match (p.run)(array) {
                (u, Ok(_)) => match (r.run)(&array[u..]) {
                    (v, Ok(b)) => (u + v, Ok(b)),
                    (v, Err(e)) => (u + v, Err(e)),
                },
                (u, Err(e)) => (u, Err(e)),
            }),
        }
    }
    ///
    /// `p.and(q)` succeeds when both p and q succeed and it returns a tuple
    /// of the results of p and q.
    ///
    /// This is short for:
    /// `p.and_then(
    ///     |p_result| q.and_then (
    ///         |q_result| GenericP::pure((p_result, q_result))
    /// ))
    pub fn and<T>(self, r: GenericP<S, T, E>) -> GenericP<S, (R, T), E>
    where
        T: 'static,
    {
        let p = GenericP {
            run: Box::new(self.run),
        };
        GenericP {
            run: Box::new(move |array| match (p.run)(array) {
                (u, Ok(a)) => match (r.run)(&array[u..]) {
                    (v, Ok(b)) => (u + v, Ok((a, b))),
                    (v, Err(e)) => (u + v, Err(e)),
                },
                (u, Err(e)) => (u, Err(e)),
            }),
        }
    }

    ///
    /// `p.before(q)` succeeds when both p and q succeed and returns
    /// the result of p.
    ///
    /// This is short for:
    /// `p.and_then(
    ///     |p_result| q.and_then (
    ///         |q_result| GenericP::pure(p_result)
    /// ))
    pub fn before<T>(self, r: GenericP<S, T, E>) -> GenericP<S, R, E>
    where
        T: 'static,
    {
        let p = GenericP {
            run: Box::new(self.run),
        };
        GenericP {
            run: Box::new(move |array| match (p.run)(array) {
                (u, Ok(a)) => match (r.run)(&array[u..]) {
                    (v, Ok(_)) => (u + v, Ok(a)),
                    (v, Err(e)) => (u + v, Err(e)),
                },
                (u, Err(e)) => (u, Err(e)),
            }),
        }
    }
}

impl<S, R, E> Parser<S, R, E> for GenericP<S, R, E> {
    fn parse_raw(&self, src: &[S]) -> (usize, Result<R, E>) {
        (self.run)(src)
    }
}

impl<R, E> StrParser<R, E> for GenericP<u8, R, E> {}

pub fn map_result<R, E, T>(r: ParseResult<R, E>, f: impl Fn(R) -> T) -> ParseResult<T, E> {
    match r {
        (u, re) => (u, re.map(f)),
    }
}

/// expect and consume a certain character
pub fn expect(c: char) -> GenericP<u8, char, String> {
    if c.is_ascii() {
        GenericP {
            run: Box::new(move |array| {
                if array.len() > 0 && array[0] == c as u8 {
                    (1, Ok(c))
                } else {
                    (0, Err(format!("'{}' expected", c)))
                }
            }),
        }
    } else {
        GenericP {
            run: Box::new(move |array| {
                let n_bytes = c.len_utf8();
                let mut buffer = [0u8; 8];
                let encoded = c.encode_utf8(&mut buffer);
                if array.len() > 0 && array.starts_with(encoded.as_bytes()) {
                    (n_bytes, Ok(c))
                } else {
                    (
                        0,
                        Err(format!("'{}' ({:?}) expected", c, encoded.as_bytes())),
                    )
                }
            }),
        }
    }
}

pub fn satisfy(f: impl Fn(char) -> bool + 'static) -> GenericP<u8, char, String> {
    GenericP {
        run: Box::new(move |array| {
            match from_utf8(array) {
                Err(utf8) => (0, Err(format!("{}", utf8))),
                Ok(str) => match str.chars().next() {
                    None => (0, Err("unepected end of input".to_string())),
                    Some(c) if f(c) => (c.len_utf8(), Ok(c)),
                    Some(_) => (0, Err("no match".to_string())),
                },
            }
            // (42, Ok('c'))
        }),
    }
}

pub fn label<S, R>(lbl: &'static str, p: GenericP<S, R, String>) -> GenericP<S, R, String>
where
    S: 'static,
    R: 'static,
{
    GenericP {
        run: Box::new(move |array| {
            let err = lbl.clone();
            match (p.run)(array) {
                (u, e) => (u, e.map_err(|_| err.to_string())),
            }
        }),
    }
}

#[test]
pub fn test() {
    let ä = expect('Ä');
    let r = ä.parse("Äbc".as_bytes());
    let mut buffer = [0u8; 8];
    println!("{:?} {:?}", r, 'Ä'.encode_utf8(&mut buffer).as_bytes());
    let letter = label("expected letter", satisfy(|c| c >= 'a' && c <= 'z'));
    let letter2 = satisfy(|c| c >= 'a' && c <= 'z').label("expected letter2");
    let r = letter.parse(b" abc");
    println!("{:?}", r);
    let source = "aÄcd1".as_bytes();
    unsafe {
        use std::str;
        match (letter.run)(source) {
            (u, Ok(c)) => match (letter2.run)(&source[u..]) {
                (_, Ok(d)) => println!(
                    "The first two letters of '{}' are '{}{}'",
                    str::from_utf8_unchecked(source),
                    c,
                    d
                ),
                _ => {}
            },
            _ => {}
        };
    };
    let px = GenericP { run: letter.run };
    println!("{:?}", ä.and(px).parse_raw("Äxyz".as_bytes()));
    let ez1 = "èz"; // U+00E8 LATIN SMALL LETTER E WITH GRAVE, z
    let ez2 = "èz"; // e, U+0300 COMBINING GRAVE ACCENT, z

    assert_ne!(ez1, ez2);

    println!(
        "{:?} in {:?} \"{}\"",
        expect('e').and(expect('z')).parse_str_raw(ez1),
        ez1.as_bytes(),
        ez1
    );
    println!(
        "{:?} in {:?} \"{}\"",
        expect('è').and(expect('z')).parse_str_raw(ez1),
        ez1.as_bytes(),
        ez1
    );
    println!(
        "{:?} in {:?} \"{}\"",
        expect('è').and(expect('z')).parse_str_raw(ez2),
        ez2.as_bytes(),
        ez2
    );
    println!(
        "{:?} in {:?} \"{}\"",
        expect('e')
            .and(expect('\u{300}'))
            .and(expect('z'))
            .parse_str_raw(ez2),
        ez2.as_bytes(),
        ez2
    );
    let (bytes, err) = expect('e').and(expect('z')).parse_str_raw(ez2);
    println!(
        "({}, {:?} remaining input {:?}",
        bytes,
        err,
        from_utf8(&ez2.as_bytes()[bytes..]),
    );

    // let dbl = |p: GenericP<u8, char, String>| p.and_then(|_| p);
    let cc = expect('c').and(expect('c'));
    println!("{:?}", cc.parse_str_raw("c?"));
    println!("{:?}", cc.parse_str_raw("cc"));
}
