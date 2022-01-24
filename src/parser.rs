use std::borrow::Borrow;
use std::rc::Rc;
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
type ParserFunc<S, R, E> = Rc<dyn Fn(&[S]) -> (usize, Result<R, E>)>;

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
        GenericP {
            run: Rc::clone(&self.run),
        }
    }
}

impl<S, R, E> GenericP<S, R, E>
where
    S: 'static,
    R: 'static,
    E: 'static,
{
    /// Make a new parser from a lambda.
    /// This is mostly used internally.
    ///
    /// However, if one needs a primitive parser that cannot be expressed as combination
    /// of other parsers, this is what you're looking for.
    ///
    /// It is absolutely essential, though, to always report the correct number of input items consumed,
    /// otherwise your parser will not work well in combination with others.
    /// Please test your parsers also on empty inputs to see if they behave okay-ish.
    ///
    pub fn new(f: impl Fn(&[S]) -> ParseResult<R, E> + 'static) -> Self {
        GenericP { run: Rc::new(f) }
    }

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
    pub fn label(&self, lbl: &str) -> GenericP<S, R, String> {
        let p = self.clone();
        let msg = lbl.to_string(); // format!("{}", lbl);
        GenericP::new(move |array| match (p.run)(array) {
            (u, e) => (u, e.map_err(|_| msg.clone())),
        })
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
    pub fn and_then<T>(&self, f: impl Fn(R) -> GenericP<S, T, E> + 'static) -> GenericP<S, T, E>
    where
        T: 'static,
    {
        let p = self.clone();
        GenericP::new(move |array| match (p.run)(array) {
            (u, Ok(a)) => match (f(a).run)(&array[u..]) {
                (v, Ok(b)) => (u + v, Ok(b)),
                (v, Err(e)) => (u + v, Err(e)),
            },
            (u, Err(err)) => (u, Err(err)),
        })
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
    pub fn then<T>(&self, r: impl Borrow<GenericP<S, T, E>> + 'static) -> GenericP<S, T, E>
    where
        T: 'static,
    {
        let q = r.borrow().clone();
        self.and_then(move |_| q.clone())
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
    pub fn and<T>(&self, r: impl Borrow<GenericP<S, T, E>>) -> GenericP<S, (R, T), E>
    where
        T: 'static,
        R: Copy,
        T: Copy,
    {
        let q = r.borrow().clone();
        self.and_then(move |pv| q.and_then(move |qv| pure((pv, qv))))
        // let p = GenericP {
        //     run: Box::new(self.run),
        // };
        // GenericP {
        //     run: Box::new(move |array| match (p.run)(array) {
        //         (u, Ok(a)) => match (r.run)(&array[u..]) {
        //             (v, Ok(b)) => (u + v, Ok((a, b))),
        //             (v, Err(e)) => (u + v, Err(e)),
        //         },
        //         (u, Err(e)) => (u, Err(e)),
        //     }),
        // }
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
    pub fn before<T>(&self, r: impl Borrow<GenericP<S, T, E>>) -> GenericP<S, R, E>
    where
        T: 'static,
        R: Copy,
    {
        let q = r.borrow().clone();
        self.and_then(move |pv| q.and_then(move |_| pure(pv)))
    }

    /// `p.or(q)`
    ///  
    /// When `p` suceeds, this is the overall result.
    /// Otherwise, `q` is tried on the same input as `p` regardless whether `p` already consumed something.
    ///
    pub fn or(&self, r: impl Borrow<GenericP<S, R, E>>) -> GenericP<S, R, E> {
        let p = self.clone();
        let q = r.borrow().clone();
        GenericP::new(move |array| match (p.run)(array) {
            r @ (_, Ok(_)) => r,
            _other => (q.run)(array),
        })
    }

    /// `p.map(f)` is equivalent to `p.and_then(|v| pure(f(v)))`
    pub fn map<T>(&self, f: impl Fn(R) -> T + 'static) -> GenericP<S, T, E>
    where
        T: 'static,
    {
        let p = self.clone();
        GenericP::new(move |array| match (p.run)(array) {
            (u, Ok(v)) => (u, Ok(f(v))),
            (u, Err(e)) => (u, Err(e)),
        })
    }

    /// `p.map_err(f)` maps the error value when `p` fails.
    pub fn map_err<F>(&self, f: impl Fn(E) -> F + 'static) -> GenericP<S, R, F>
    where
        F: 'static,
    {
        let p = self.clone();
        GenericP::new(move |array| match (p.run)(array) {
            (u, Ok(v)) => (u, Ok(v)),
            (u, Err(e)) => (u, Err(f(e))),
        })
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

// ------------------------- primitive parsers -----------------------------------------

/// A parser that always succeeds and returns the supplied value.
/// Useful as last element in nested `and_then` constructs.
pub fn pure<S, R, E>(v: R) -> GenericP<S, R, E>
where
    S: 'static,
    R: Copy + 'static,
    E: 'static,
{
    let w = v;
    GenericP::new(move |_| (0, Ok(w)))
}

/// A parser that always fails without consuming anything. The error contains the supplied value.
pub fn fail<S, R, E>(e: E) -> GenericP<S, R, E>
where
    S: 'static,
    R: 'static,
    E: Copy + 'static,
{
    GenericP::new(move |_| (0, Err(e)))
}
///
/// A parser that succeeds if and only if the source slice is empty.
/// Does not consume any input.
///
/// If it fails (i.e. when there *is* more input), the result will be
/// ```
/// Err("input not exhausted")
/// ```
///
/// Useful in constructs like
///
/// ```
/// my_grammar.before(GenericP::end_of_input())
/// ```
///
/// where `my_grammar` would be some top level parser.
pub fn end_of_input<S>() -> GenericP<S, (), String>
where
    S: 'static,
{
    GenericP::new(|array: &[S]| {
        if array.len() == 0 {
            (0, Ok(()))
        } else {
            (0, Err("input not exhausted".to_string()))
        }
    })
}

/// expect and consume a certain character
pub fn expect(c: char) -> GenericP<u8, char, String> {
    if c.is_ascii() {
        GenericP::new(move |array| {
            if array.len() > 0 && array[0] == c as u8 {
                (1, Ok(c))
            } else {
                (0, Err(format!("'{}' expected", c)))
            }
        })
    } else {
        GenericP::new(move |array| {
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
        })
    }
}

/// Succeeds when the next character satisfies the given predicate and gives that character as result.
///
/// Fails on end of input or when the character fails the predicate, in which case nothing is consumed.
pub fn satisfy(f: impl Fn(char) -> bool + 'static) -> GenericP<u8, char, String> {
    GenericP::new(move |array| match from_utf8(array) {
        Err(utf8) => (0, Err(format!("{}", utf8))),
        Ok(str) => match str.chars().next() {
            None => (0, Err("unexpected end of input".to_string())),
            Some(c) if f(c) => (c.len_utf8(), Ok(c)),
            Some(_) => (0, Err("no match".to_string())),
        },
    })
}

#[test]
pub fn test() {
    let ä = expect('Ä');
    let r = ä.parse("Äbc".as_bytes());
    let mut buffer = [0u8; 8];
    println!("{:?} {:?}", r, 'Ä'.encode_utf8(&mut buffer).as_bytes());
    let letter = satisfy(|c| c >= 'a' && c <= 'z').label("expected letter");
    let r = letter.parse(b"x");
    println!("{:?}", r);

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
    let double = |x: GenericP<_, _, _>| x.clone().then(x);
    let c2 = double(expect('c'));
    println!("{:?}", cc.parse_str_raw("c?"));
    println!("{:?}", c2.parse_str_raw("cc"));
    let dc = expect('c').or(expect('d'));
    println!("{:?}", dc.parse_str_raw("cd"));
    println!("{:?}", dc.parse_str_raw("dc"));
    println!("{:?}", dc.parse_str_raw("?!"));
    println!("{:?}", dc.parse_str_raw(""));
}
