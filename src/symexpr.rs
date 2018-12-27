use std::iter::Peekable;
use std::str::FromStr;

/// Symbolic expression is either an atom or a list.
#[derive(Debug, PartialEq)]
pub enum Symexpr {
    Atom(Atom),
    List(List),
}

pub type Symbol = String;

/// Ergonomics, mostly. The preferred way to construct a symbolic expression
/// in-code without using parse().
impl Symexpr {
    pub fn string(s: String) -> Self {
        Symexpr::Atom(Atom::Str(s))
    }
    pub fn float(f: f64) -> Self {
        Symexpr::Atom(Atom::Float(f))
    }
    pub fn symbol(s: Symbol) -> Self {
        Symexpr::Atom(Atom::Symbol(s))
    }
    pub fn boolean(b: bool) -> Self {
        Symexpr::Atom(Atom::Bool(b))
    }
    pub fn list(l: Vec<Symexpr>) -> Self {
        Symexpr::List(List::from(l))
    }
}

/// An atom is nil (empty list), symbol, bool, string, or f64 float.
#[derive(Debug, PartialEq)]
pub enum Atom {
    Bool(bool),
    Symbol(Symbol),
    Str(String),
    Float(f64),
}

/// A list is an s-expr that is made of multiple s-expr's.
#[derive(Debug, PartialEq)]
pub struct List {
    pub contents: Vec<Symexpr>,
}

impl List {
    fn new() -> Self {
        List { contents: vec![] }
    }

    fn from(contents: Vec<Symexpr>) -> Self {
        List { contents }
    }
}

#[derive(Debug, PartialEq)]
pub enum ParseErrorKind {
    /// A string literal escapes nothing
    EscapeEOF,

    /// String is not closed (no end-quote)
    UnclosedString,

    /// List is not closed (no close-paren)
    UnclosedList,

    /// The first token encountered is a close-paren
    FirstTokenEndsList,

    /// Given a string that contains no tokens at all
    NothingToParse,

    /// Parsed a value, but there were extra symbols before the string ends
    ExtraTokensBeforeEOF,
}

#[derive(Debug)]
pub struct ParseError {
    kind: ParseErrorKind,
    location: Blame,
}

impl ParseError {
    fn new(location: Blame, kind: ParseErrorKind) -> Self {
        ParseError { kind, location }
    }
}

/// Indicates where in the input string this error originated from.
/// Useful only for debugging.
/// Since the lifetime resulting `Symexpr` is not constrained to be strictly
/// within the lifetime of the `str` it was parsed from, the values contained
/// here may not have a logical interpretation if the `str` is dropped before
/// the `Symexpr` is.
#[derive(Debug)]
pub struct Blame {
    start_byte: usize,
    end_byte: usize,
}
impl Blame {
    // TODO
    fn new() -> Self {
        return Blame {
            start_byte: 0,
            end_byte: 0,
        };
    }

    /// Constructor
    fn new_range(start_byte: usize, end_byte: usize) -> Self {
        if start_byte > end_byte {
            panic!("Invalid symexpr Blame range!");
        }
        Blame {
            start_byte,
            end_byte,
        }
    }

    /// Creates a new `Blame` that holds the first and second `Blame`s and
    /// everything in-between. Useful for getting the `Blame` of an entire
    /// list.
    pub fn superset(first: Blame, second: Blame) -> Self {
        Blame {
            start_byte: if first.start_byte < second.start_byte {
                first.start_byte
            } else {
                second.start_byte
            },
            end_byte: if first.end_byte > second.end_byte {
                first.end_byte
            } else {
                second.end_byte
            },
        }
    }
}

type ParseResult = Result<Symexpr, ParseError>;

#[derive(Debug, PartialEq)]
pub enum Token {
    // Usually open and close parens
    BeginList,
    EndList,

    // String literal
    StrLiteral(String),

    // Something else
    Misc(String),
}

/// Just gets rid of all the next whitespace
pub fn consume_whitespace_and_comments<I>(chars: &mut Peekable<I>)
where
    I: Iterator<Item = char>,
{
    while let Some(&cell) = chars.peek() {
        if cell.is_whitespace() {
            chars.next(); // Consume the whitespace
        } else {
            match cell {
                ';' => {
                    chars.next(); // Consume the ;
                    while let Some(cell) = chars.next() {
                        if cell == '\n' {
                            break;
                        }
                    }
                }
                _ => {
                    break;
                }
            }
        }
    }
}

/// Extracts the next string, assumes that the beginning quote was already
/// removed. TODO: Handles usual string escapes the same as Rust does.
fn extract_string_literal<I>(chars: &mut Peekable<I>) -> Option<Result<Token, ParseError>>
where
    I: Iterator<Item = char>,
{
    let mut retval = String::new();
    let mut ended_properly = false;
    while let Some(cell_ref) = chars.next() {
        match cell_ref {
            // End-quote escaping
            '\\' => {
                if let Some(next_char) = chars.next() {
                    if next_char == '"' {
                        retval.push('"'); // Add the quote
                    }
                    // Some other form of escape
                    else {
                        retval.push('\\');
                        retval.push(next_char);
                    }
                } else {
                    return Some(Err(ParseError::new(
                        Blame::new(),
                        ParseErrorKind::EscapeEOF,
                    )));
                }
            }

            '"' => {
                ended_properly = true;
                break;
            }

            _ => {
                retval.push(cell_ref);
            }
        }
    }

    if !ended_properly {
        Some(Err(ParseError::new(
            Blame::new(),
            ParseErrorKind::UnclosedString,
        )))
    } else {
        Some(Ok(Token::StrLiteral(retval)))
    }
}

/// Extracts the next token from the provided char iterator.
/// This does not include comments.
pub fn next_token<I>(chars: &mut Peekable<I>) -> Option<Result<Token, ParseError>>
where
    I: Iterator<Item = char>,
{
    //Remove any initial whitespace and comments
    consume_whitespace_and_comments(chars);

    // Based on the first non-whitespace char we enounter, there are different
    // tokens to acquire:
    if let Some(first_cell) = chars.next() {
        match first_cell {
            // Single symbols
            '(' => Some(Ok(Token::BeginList)),
            ')' => Some(Ok(Token::EndList)),

            // Begin a string
            '"' => extract_string_literal(chars),

            // Anything else
            _ => {
                let mut retval = first_cell.to_string();

                // Go until we reach another token or whitespace or the end
                while let Some(&cell_ref) = chars.peek() {
                    if cell_ref.is_whitespace() {
                        break;
                    }
                    match cell_ref {
                        '(' | ')' | '"' => {
                            break;
                        }
                        _ => {
                            retval.push(cell_ref);
                            chars.next();
                        }
                    }
                }

                Some(Ok(Token::Misc(retval)))
            }
        }
    }
    // Nothing after removing whitespace
    else {
        None
    }
}

pub struct TokenIter<I>
where
    I: Iterator<Item = char>,
{
    location: Blame,
    iter: Peekable<I>,
}

impl<I> TokenIter<I>
where
    I: Iterator<Item = char>,
{
    pub fn new(iter: Peekable<I>) -> Self {
        TokenIter {
            location: Blame::new(),
            iter,
        }
    }
}

impl<I> Iterator for TokenIter<I>
where
    I: Iterator<Item = char>,
{
    type Item = Result<Token, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        next_token(&mut self.iter)
    }
}

/// Takes a Chars iterator and returns a new iterator which tokenizes the
/// underlying string.
pub fn tokenize<I>(input: Peekable<I>) -> TokenIter<I>
where
    I: Iterator<Item = char>,
{
    TokenIter::new(input)
}

/// Internal function for parsing a list (assumes that the open paren was
/// already taken.)
fn parse_list<I>(input: &mut TokenIter<I>) -> ParseResult
where
    I: Iterator<Item = char>,
{
    let mut retval = List::new();
    loop {
        let next_elem = match input.next() {
            None => return Err(ParseError::new(Blame::new(), ParseErrorKind::UnclosedList)),
            Some(token) => {
                let token = token?;
                match token {
                    Token::EndList => break,
                    Token::BeginList => parse_list(input)?,
                    Token::StrLiteral(strlit) => parse_string_lit(strlit)?,
                    Token::Misc(strlit) => parse_misc(strlit)?,
                }
            }
        };

        retval.contents.push(next_elem);
    }
    Ok(Symexpr::List(retval))
}

///
fn parse_string_lit(input: String) -> ParseResult {
    Ok(Symexpr::Atom(Atom::Str(input)))
}

///
fn parse_misc(input: String) -> ParseResult {
    match input.as_ref() {
        "true" => Ok(Symexpr::Atom(Atom::Bool(true))),
        "false" => Ok(Symexpr::Atom(Atom::Bool(false))),
        _ => {
            if let Ok(num) = input.parse::<f64>() {
                Ok(Symexpr::Atom(Atom::Float(num)))
            } else {
                Ok(Symexpr::Atom(Atom::Symbol(input)))
            }
        }
    }
}

/// Public api for parsing tokens. Returns a single symexpr value.
/// Errors if there is not exactly one value to parse.
pub fn parse_tokens<I>(input: &mut TokenIter<I>) -> ParseResult
where
    I: Iterator<Item = char>,
{
    let retval = match input.next() {
        Some(result) => match result {
            Ok(token) => match token {
                Token::BeginList => parse_list(input),
                Token::EndList => Err(ParseError::new(
                    Blame::new(),
                    ParseErrorKind::FirstTokenEndsList,
                )),
                Token::StrLiteral(string_literal) => parse_string_lit(string_literal),
                Token::Misc(misc_string) => parse_misc(misc_string),
            },
            Err(error) => Err(error),
        },
        // Error if there are no symexpr values
        None => Err(ParseError::new(
            Blame::new(),
            ParseErrorKind::NothingToParse,
        )),
    };

    // Propogate errors
    let retval = retval?;

    // Check that there are no tokens left (More than one symexpr value)
    match input.next() {
        None => {}
        Some(_) => {
            return Err(ParseError::new(
                Blame::new(),
                ParseErrorKind::ExtraTokensBeforeEOF,
            ))
        }
    }

    Ok(retval)
}

pub fn parse_chars<I>(input: I) -> ParseResult
where
    I: Iterator<Item = char>,
{
    let mut tokens = tokenize(input.filter(|c| c != &'\r').peekable());
    parse_tokens(&mut tokens)
}

pub fn parse_string(input: &String) -> ParseResult {
    parse_chars(input.chars())
}

// Implementing the "standard" way to parse a string
impl FromStr for Symexpr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_chars(s.chars())
    }
}

#[cfg(test)]
mod test {

    use super::{
        consume_whitespace_and_comments, parse_chars, tokenize, Atom, List, ParseErrorKind, Symbol,
        Symexpr, Token,
    };

    #[test]
    fn parser_basics() {
        let input = "\"string literal.\"";
        let syme = parse_chars(input.chars()).unwrap();
        match syme {
            Symexpr::Atom(Atom::Str(val)) => assert_eq!(val, String::from("string literal.")),
            different => panic!("Got something else: {:?}", different),
        }

        let input = "(symbol)";
        let syme = parse_chars(input.chars()).unwrap();
        match syme {
            Symexpr::List(list) => {
                assert_eq!(
                    list.contents,
                    vec![Symexpr::Atom(Atom::Symbol(Symbol::from("symbol")))]
                );
            }
            different => panic!("Got something else: {:?}", different),
        }

        let input = "64.125";
        let syme = parse_chars(input.chars()).unwrap();
        match syme {
            Symexpr::Atom(Atom::Float(val)) => assert_eq!(val, 64.125),
            different => panic!("Got something else: {:?}", different),
        }

        let input = "true";
        let syme = parse_chars(input.chars()).unwrap();
        match syme {
            Symexpr::Atom(Atom::Bool(val)) => assert_eq!(val, true),
            different => panic!("Got something else: {:?}", different),
        }

        let input = "false";
        let syme = parse_chars(input.chars()).unwrap();
        match syme {
            Symexpr::Atom(Atom::Bool(val)) => assert_eq!(val, false),
            different => panic!("Got something else: {:?}", different),
        }
    }

    #[test]
    fn from_str_impl() {
        let syme = "true".parse::<Symexpr>().unwrap();
        assert_eq!(syme, Symexpr::Atom(Atom::Bool(true)));
    }

    #[test]
    fn parser_nested_list() {
        let input = "(symbol ((nest) nested (nesting)))";
        let syme = parse_chars(input.chars()).unwrap();

        assert_eq!(
            syme,
            Symexpr::List(List::from(vec![
                Symexpr::Atom(Atom::Symbol(Symbol::from("symbol"))),
                Symexpr::List(List::from(vec![
                    Symexpr::List(List::from(vec![Symexpr::Atom(Atom::Symbol(Symbol::from(
                        "nest",
                    )))])),
                    Symexpr::Atom(Atom::Symbol(Symbol::from("nested"))),
                    Symexpr::List(List::from(vec![Symexpr::Atom(Atom::Symbol(Symbol::from(
                        "nesting",
                    )))])),
                ])),
            ]))
        );
    }

    // TODO: some kind of macro for building in-line symbolic expressions

    #[test]
    fn tokenizer_basics() {
        let input = "(";
        let mut token_iter = tokenize(input.chars().peekable());
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::BeginList);
        let input = String::from(")");
        let mut token_iter = tokenize(input.chars().peekable());
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::EndList);
        let input = String::from("hello");
        let mut token_iter = tokenize(input.chars().peekable());
        assert_eq!(
            token_iter.next().unwrap().unwrap(),
            Token::Misc(String::from("hello"))
        );
        let input = String::from("\"world\"");
        let mut token_iter = tokenize(input.chars().peekable());
        assert_eq!(
            token_iter.next().unwrap().unwrap(),
            Token::StrLiteral(String::from("world"))
        );
    }

    #[test]
    fn tokenizer_simple() {
        let test_input = "(simple) ; comment
                          (\"string\") ;;;; many semicolons
                          (+ 1 ; comment interrupts
                           ; another comment
                           ; many lines of comments
                           )";

        let mut token_iter = tokenize(test_input.chars().peekable());

        assert_eq!(token_iter.next().unwrap().unwrap(), Token::BeginList);
        assert_eq!(
            token_iter.next().unwrap().unwrap(),
            Token::Misc(String::from("simple"))
        );
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::EndList);
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::BeginList);
        assert_eq!(
            token_iter.next().unwrap().unwrap(),
            Token::StrLiteral(String::from("string"))
        );
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::EndList);
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::BeginList);
        assert_eq!(
            token_iter.next().unwrap().unwrap(),
            Token::Misc(String::from("+"))
        );
        assert_eq!(
            token_iter.next().unwrap().unwrap(),
            Token::Misc(String::from("1"))
        );
        assert_eq!(token_iter.next().unwrap().unwrap(), Token::EndList);
        match token_iter.next() {
            Some(_) => panic!("Claimed there were still tokens!"),
            None => {} // We want an error
        }
    }

    #[test]
    fn tokenizer_endofstring() {
        let test_input = "\"unended string";
        let mut token_iter = tokenize(test_input.chars().peekable());
        match token_iter.next() {
            None => panic!("Claimed there were no more tokens!"),
            Some(Ok(_)) => panic!("Claimed everything was alright!"),
            Some(Err(_)) => {} // We want an error
        }
    }

    #[test]
    fn remove_whitespace() {
        let test_input = "\n\n\t   \r\n\r   ;hello ;;  \n world!";
        let mut iter = test_input.chars().peekable();
        consume_whitespace_and_comments(&mut iter);

        assert_eq!(iter.next().unwrap(), 'w');

        let test_input = "\n\n\t   \r\n\r   ;hello ;;  \n;;";
        let mut iter = test_input.chars().peekable();
        consume_whitespace_and_comments(&mut iter);

        match iter.next() {
            None => {}
            Some(_) => panic!("Claimed there was non-whitespace in here!"),
        }
    }

    #[test]
    fn test_errors() {
        let error = "\"\\".parse::<Symexpr>().err().unwrap();
        assert_eq!(error.kind, ParseErrorKind::EscapeEOF);
        let error = "(\"".parse::<Symexpr>().err().unwrap();
        assert_eq!(error.kind, ParseErrorKind::UnclosedString);
        let error = "(symbol (".parse::<Symexpr>().err().unwrap();
        assert_eq!(error.kind, ParseErrorKind::UnclosedList);
        let error = ")".parse::<Symexpr>().err().unwrap();
        assert_eq!(error.kind, ParseErrorKind::FirstTokenEndsList);
        let error = "".parse::<Symexpr>().err().unwrap();
        assert_eq!(error.kind, ParseErrorKind::NothingToParse);
        let error = "(hi)(".parse::<Symexpr>().err().unwrap();
        assert_eq!(error.kind, ParseErrorKind::ExtraTokensBeforeEOF);
    }

    #[test]
    fn test_ergonomics() {
        let foo = Symexpr::symbol(Symbol::from("Hello!"));
        assert_eq!("Hello!".parse::<Symexpr>().unwrap(), foo);
    }
}
