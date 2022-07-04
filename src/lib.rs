//! [![Version](https://img.shields.io/crates/v/nompdf)](https://crates.io/crates/nompdf)
//! [![Downloads](https://img.shields.io/crates/d/nompdf)](https://crates.io/crates/nompdf)
//! [![License](https://img.shields.io/crates/l/nompdf)](https://crates.io/crates/nompdf)
//! ![Rust](https://github.com/edg-l/nompdf/workflows/Rust/badge.svg)
//! [![Docs](https://docs.rs/nompdf/badge.svg)](https://docs.rs/nompdf)
//!
//! Work in progress.
//!
//! ## A PDF parser written in Rust using nom.
//!
//! Using [PDF Reference third edition](https://www.adobe.com/content/dam/acom/en/devnet/pdf/pdfs/pdf_reference_archives/PDFReference.pdf) as reference.

#![forbid(unsafe_code)]

use error::{PDFError, PDFResult};
use nom::branch::alt;
use nom::bytes::complete::{take_till, take_while, take_while1};
use nom::character::complete::hex_digit1;
use nom::combinator::{eof, map_res, recognize};
use nom::error::{Error, ErrorKind, ParseError};
use nom::number::complete;
use nom::sequence::{delimited, pair, tuple};
use nom::{bytes::complete::tag, character::complete::char, character::complete::digit1, IResult};
use std::{collections::HashMap, fmt::Debug, io::Read, ops::RangeInclusive};

pub mod error;

// TODO: change strings to use a new type and add methods to decode/encode to pdf string format.

/// What PDF considers white space characters.
pub const WHITE_SPACE_CHARS: [u8; 6] = [0x00, 0x09, 0x0A, 0x0C, 0x0D, 0x20];

#[derive(Debug, Clone, PartialEq, PartialOrd, Hash)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// A name object.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct NameObject<'a>(pub &'a str);

/// A PDF dictionary object.
pub type DictionaryObject<'a> = HashMap<NameObject<'a>, Object<'a>>;

pub type HexString<'a> = &'a str;

/// An indirect object reference.
/// Represented in PDFs like "12 0 R"
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct IndirectReference {
    pub number: u64,
    pub generation: u64,
}

/// The PDF header.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Header {
    /// The major version, usually 1.
    pub major: u32,
    /// The minor version, from 0 to 7.
    pub minor: u32,
}

#[derive(Debug, Clone)]
pub enum Object<'a> {
    Boolean(bool),
    Integer(i32),
    Real(f32),
    LiteralString(&'a str),
    HexadecimalString(HexString<'a>),
    Name(NameObject<'a>),
    Array(Vec<Object<'a>>),
    Dictionary(DictionaryObject<'a>),
    Stream(DictionaryObject<'a>, &'a [u8]),
    Null,
    /// An indirect object definition.
    Indirect {
        reference: IndirectReference,
        object: Box<Object<'a>>,
    },
}

/// Represents a cross reference entry.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct CrossReference {
    /// 10-digit byte offset in the decoded stream.
    pub offset: u64,
    /// 5-digit generation number.
    pub generation: u32,
    /// Whether the entry is free.
    pub free: bool,
}

/// A cross reference subsection
#[derive(Debug, Hash, Clone)]
pub struct SubSection {
    pub range: RangeInclusive<u64>,
    pub entries: Vec<CrossReference>,
}

/// The PDF trailer.
#[derive(Debug, Hash, Clone)]
pub struct Trailer<'a> {
    pub size: i64,
    pub prev: Option<IndirectReference>,
    pub root: IndirectReference,
    pub encrypt: Option<IndirectReference>,
    pub info: Option<IndirectReference>,
    pub id: Option<Either<IndirectReference, Vec<HexString<'a>>>>,
}

/// The parsed PDF file.
#[derive(Debug, Clone)]
pub struct PDF<'a> {
    pub header: Header,
    pub objects: Vec<Object<'a>>,
    pub cross_references: Vec<SubSection>,
    pub trailer: Trailer<'a>,
    /// Byte offset of last cross reference section.
    pub byte_offset: u64,
}

impl Header {
    fn parse(inp: &[u8]) -> PDFResult<Header> {
        let (inp, _) = tag(b"%PDF-")(inp)?;
        // Take a str digit and convert it to u32.

        let (inp, major) = take_digit_u32(inp)?;
        let (inp, _) = char('.')(inp)?;
        let (inp, minor) = take_digit_u32(inp)?;

        Ok((inp, Header { major, minor }))
    }
}

fn take_digit_u32(inp: &[u8]) -> PDFResult<u32> {
    let (inp, digit) = map_res(digit1, |digit| std::str::from_utf8(digit))(inp)?;
    let num = u32::from_str_radix(digit, 10).map_err(PDFError::ParseIntError)?;
    Ok((inp, num))
}

fn take_digit_i32(inp: &[u8]) -> PDFResult<i32> {
    let (inp, digit) = map_res(digit1, |digit| std::str::from_utf8(digit))(inp)?;
    let num = i32::from_str_radix(digit, 10).map_err(PDFError::ParseIntError)?;
    Ok((inp, num))
}

fn take_until_unbalanced(
    opening_bracket: u8,
    closing_bracket: u8,
) -> impl Fn(&[u8]) -> PDFResult<&[u8]> {
    move |i: &[u8]| {
        let mut bracket_counter = 0;

        for (index, x) in i.iter().enumerate() {
            match *x {
                x if x == opening_bracket => {
                    bracket_counter += 1;
                }
                x if x == closing_bracket => {
                    bracket_counter -= 1;
                }
                _ => {}
            }
            if bracket_counter == -1 {
                // We do not consume it.
                return Ok((&i[index..], &i[0..index]));
            };
        }

        if bracket_counter == 0 {
            Ok((b"", i))
        } else {
            Err(PDFError::NomError(ErrorKind::TakeUntil).into())
        }
    }
}

/// Returns everything until a whitespace is found.
#[inline]
fn till_whitespace(inp: &[u8]) -> PDFResult<&[u8]> {
    take_till(|c| WHITE_SPACE_CHARS.contains(&c))(inp)
}

/// Returns all the whitespace until a non-whitespace character is found.
#[inline]
fn skip_whitespace(inp: &[u8]) -> PDFResult<&[u8]> {
    take_while(|c| WHITE_SPACE_CHARS.contains(&c))(inp)
}

/// Most objects should be separated by whitespace or eof, this is needed to ensure "nullthisisbad"
/// doesn't simply match null for a null object and then ignores the rest of the word.
#[inline]
fn take_whitespace_eof(inp: &[u8]) -> PDFResult<&[u8]> {
    alt((eof, take_while1(|c| WHITE_SPACE_CHARS.contains(&c))))(inp)
}

// General rule of individual parsers: Assume there is no whitespace at the start.
impl<'a> Object<'a> {
    fn parse_bool(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, res) = alt((tag("true"), tag("false")))(inp)?;
        let value = res.eq_ignore_ascii_case(b"true");
        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::Boolean(value)))
    }

    // 123 43445 +17 −98 0
    fn parse_integer(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, value) = alt((
            recognize(pair(char('+'), digit1)),
            recognize(pair(char('-'), digit1)),
            recognize(digit1),
        ))(inp)?;

        let value_str = std::str::from_utf8(value).map_err(PDFError::InvalidUTF8)?;
        let num = i32::from_str_radix(value_str, 10).map_err(PDFError::ParseIntError)?;

        let (inp, _) = take_whitespace_eof(inp)?;

        Ok((inp, Object::Integer(num)))
    }

    fn parse_real(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, value) = complete::float(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;

        Ok((inp, Object::Real(value)))
    }

    fn parse_numeric(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp_outer, value) = till_whitespace(inp)?;

        let (_, obj) = alt((
            tuple((Object::parse_integer, eof)),
            tuple((Object::parse_real, eof)),
        ))(value)?;

        Ok((inp_outer, obj.0))
    }

    fn parse_literal_string(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, value) = delimited(char('('), take_until_unbalanced(b'(', b')'), char(')'))(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;
        let value_str = std::str::from_utf8(value).map_err(PDFError::InvalidUTF8)?;
        Ok((inp, Object::LiteralString(value_str)))
    }

    // <4E6F762073686D6F7A206B6120706F702E>
    /// If the final digit of a hexadecimal string is missing—that is, if there is an odd
    /// number of digits—the final digit is assumed to be 0.
    fn parse_hex_string(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, value) = delimited(char('<'), hex_digit1, char('>'))(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;
        let value_str = std::str::from_utf8(value).map_err(PDFError::InvalidUTF8)?;
        Ok((inp, Object::HexadecimalString(value_str)))
    }

    fn parse_name(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, _) = char('/')(inp)?;
        let (inp, value) = till_whitespace(inp)?;
        let (inp, _) = take_whitespace_eof(inp)?;
        let value_str = std::str::from_utf8(value).map_err(PDFError::InvalidUTF8)?;
        Ok((inp, Object::Name(NameObject(value_str))))
    }

    fn parse_array(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (original_inp, value) =
            delimited(char('['), take_until_unbalanced(b'[', b']'), char(']'))(inp)?;

        let mut objs = Vec::new();

        let (mut outer_inp, _) = take_while(|c| WHITE_SPACE_CHARS.contains(&c))(value)?;

        loop {
            let (inp, value) = alt((
                Object::parse_bool,
                Object::parse_numeric,
                Object::parse_name,
                Object::parse_literal_string,
                Object::parse_hex_string,
                Object::parse_array,
                Object::parse_dictionary,
            ))(outer_inp)?;

            objs.push(value);

            // skip whitespace
            let (inp, _) = skip_whitespace(inp)?;

            if inp.is_empty() {
                break;
            }

            outer_inp = inp;
        }

        Ok((original_inp, Object::Array(objs)))
    }

    fn parse_dictionary(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (original_inp, value) =
            delimited(char('<'), take_until_unbalanced(b'<', b'>'), char('>'))(inp)?;

        // Remove remaining <>
        let (_, value) = delimited(char('<'), take_until_unbalanced(b'<', b'>'), char('>'))(value)?;

        let mut dict = DictionaryObject::new();

        let (mut outer_inp, _) = skip_whitespace(value)?;

        loop {
            // Find the key (name)

            let (inp, key) = Object::parse_name(outer_inp)?;

            let name_obj = {
                if let Object::Name(name_obj) = key {
                    name_obj
                } else {
                    unreachable!()
                }
            };

            let (inp, value) = alt((
                Object::parse_bool,
                Object::parse_numeric,
                Object::parse_name,
                Object::parse_literal_string,
                Object::parse_hex_string,
                Object::parse_array,
                Object::parse_dictionary,
            ))(inp)?;

            dict.insert(name_obj, value);

            // skip whitespace
            let (inp, _) = skip_whitespace(inp)?;

            if inp.is_empty() {
                break;
            }

            outer_inp = inp;
        }

        Ok((original_inp, Object::Dictionary(dict)))
    }

    fn parse_stream(inp: &'a str) -> PDFResult<Object<'a>> {
        todo!()
    }

    fn parse_null(inp: &'a [u8]) -> PDFResult<Object<'a>> {
        let (inp, _) = tag(b"null")(inp)?;
        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::Null))
    }

    fn parse_indirect(inp: &'a str) -> PDFResult<Object<'a>> {
        todo!()
    }
}

pub fn parse<'a>(data: &'a impl Read) -> PDF {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::panic;
    use matches::assert_matches;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_header() {
        for minor in 0..=7 {
            let data = format!("%PDF-1.{}", minor);
            let (data, header) = Header::parse(data.as_bytes()).unwrap();
            assert_eq!(header.major, 1u32);
            assert_eq!(header.minor, minor);
            assert!(data.is_empty())
        }
    }

    #[test]
    fn test_object_bool() {
        let data = b"true";
        let (_, object) = Object::parse_bool(data).unwrap();
        assert_matches!(object, Object::Boolean(true));

        let data = b"false";
        let (_, object) = Object::parse_bool(data).unwrap();
        assert_matches!(object, Object::Boolean(false));

        let data = b"truee";
        Object::parse_bool(data).unwrap_err();

        let data = b"falsee";
        Object::parse_bool(data).unwrap_err();

        let data = b"afalse";
        Object::parse_bool(data).unwrap_err();
    }

    #[test]
    fn test_object_null() {
        let data = b"null";
        let (_, object) = Object::parse_null(data).unwrap();
        assert_matches!(object, Object::Null);

        let data = b"nulla";
        Object::parse_null(data).unwrap_err();

        let data = b"anull";
        Object::parse_null(data).unwrap_err();
    }

    #[test]
    fn test_object_integer() {
        fn test_value(inp: &[u8], expected: i32) {
            let (_, object) = Object::parse_integer(inp).unwrap();

            if let Object::Integer(x) = object {
                assert_eq!(x, expected);
            }
        }

        test_value(b"3", 3);
        test_value(b"+3", 3);
        test_value(b"0", 0);
        test_value(b"0   ", 0);

        let data = b"1 2 3";
        let (data, object) = Object::parse_integer(data).unwrap();
        assert_matches!(object, Object::Integer(1));

        let (data, object) = Object::parse_integer(&data).unwrap();
        assert_matches!(object, Object::Integer(2));

        let (_, object) = Object::parse_integer(&data).unwrap();
        assert_matches!(object, Object::Integer(3));

        Object::parse_integer(b"3a").unwrap_err();
        Object::parse_integer(b"-3a").unwrap_err();
        Object::parse_integer(b"a").unwrap_err();
        Object::parse_integer(b"a3").unwrap_err();
    }

    #[test]
    fn test_object_real() {
        fn test_value(inp: &[u8], expected: f32) {
            let (_, object) = Object::parse_real(inp).unwrap();

            if let Object::Real(x) = object {
                assert_eq!(x, expected);
            }
        }

        test_value(b"34.5", 34.5);
        test_value(b".5", 0.5);
        test_value(b"4.", 4.0);
        test_value(b"+123.6", 123.6);
        test_value(b"-.002", -0.002);
        test_value(b"0.0", 0.0);
        test_value(b"0.0    ", 0.0);

        Object::parse_real(b"0.0a").unwrap_err();
        Object::parse_real(b"a0.0").unwrap_err();
        Object::parse_real(b".0e").unwrap_err();
    }

    #[test]
    fn test_object_numeric() {
        fn test_value_real(inp: &[u8], expected: f32) {
            let (_, object) = Object::parse_numeric(inp).unwrap();

            if let Object::Real(x) = object {
                assert_eq!(x, expected);
            }
        }

        fn test_value_integer(inp: &[u8], expected: i32) {
            let (_, object) = Object::parse_integer(inp).unwrap();

            if let Object::Integer(x) = object {
                assert_eq!(x, expected);
            }
        }

        test_value_real(b"34.5", 34.5);
        test_value_real(b".5", 0.5);
        test_value_real(b"4.", 4.0);
        test_value_real(b"+123.6", 123.6);
        test_value_real(b"-.002", -0.002);
        test_value_real(b"0.0", 0.0);

        test_value_integer(b"3", 3);
        test_value_integer(b"+3", 3);
        test_value_integer(b"0", 0);
    }

    #[test]
    fn test_object_name() {
        fn test_value(inp: &[u8], expected: &str) {
            let (_, object) = Object::parse_name(inp).unwrap();
            assert_matches!(object, Object::Name(NameObject(expected)));
        }

        test_value(b"/Adobe", "Adobe");
        test_value(b"/Test ", "Test");
        test_value(b"/Test2     ", "Test2");
    }

    #[test]
    fn test_object_literal_string() {
        fn test_value(inp: &[u8], expected: &str) {
            let (_, object) = Object::parse_literal_string(inp).unwrap();
            assert_matches!(object, Object::LiteralString(expected));
        }

        test_value(b"(hello world)", "hello world");
        test_value(b"((hello world))", "(hello world)");
        test_value(b"(this (is) a test)", "this (is) a test");

        Object::parse_literal_string(b"(dsd").unwrap_err();
        Object::parse_literal_string(b"(dsd)a").unwrap_err();
        Object::parse_literal_string(b"(dsd)a ").unwrap_err();
    }

    #[test]
    fn test_object_hex_string() {
        fn test_value(inp: &[u8], expected: &str) {
            let (_, object) = Object::parse_hex_string(inp).unwrap();
            assert_matches!(object, Object::HexadecimalString(expected));
        }

        test_value(
            b"<4E6F762073686D6F7A206B6120706F702E>",
            "4E6F762073686D6F7A206B6120706F702E",
        );

        test_value(
            b"<4E6F762073686D6F7A206B6120706F702E>   ",
            "4E6F762073686D6F7A206B6120706F702E",
        );

        Object::parse_hex_string(b"<AAA>a").unwrap_err();
        Object::parse_hex_string(b"<AAA>a ").unwrap_err();
    }

    #[test]
    fn test_object_dict() {
        Object::parse_dictionary(b"<< /First true >>").unwrap();

        let (_, object) = Object::parse_dictionary(
            br#"<<  /First true
                /SubDict << /Hello (world) >>
            >>"#,
        )
        .unwrap();
        println!("{:#?}", object);
        // TODO: improve tests
    }

    #[test]
    fn test_object_array() {
        let (_, object) = Object::parse_array(b"[0 3.14 false (Ralph) /SomeName]").unwrap();

        match object {
            Object::Array(objects) => {
                let mut it = objects.iter();

                let obj = it.next().unwrap();
                assert_matches!(obj, Object::Integer(0));

                let obj = it.next().unwrap();
                if let Object::Real(x) = obj {
                    assert_eq!(*x, 3.14f32);
                } else {
                    panic!("should be a real object");
                }

                let obj = it.next().unwrap();
                assert_matches!(obj, Object::Boolean(false));

                let obj = it.next().unwrap();
                assert_matches!(obj, Object::LiteralString("Ralph"));

                let obj = it.next().unwrap();
                assert_matches!(obj, Object::Name(NameObject("SomeName")));
            }
            _ => panic!("must be an array"),
        }
    }

    #[test]
    fn test_object_array_nested() {
        let (_, object) = Object::parse_array(b"[0 [1 2 [3 4] 5] 6]").unwrap();

        println!("Result: {:#?}", object);

        match object {
            Object::Array(objects) => {
                let mut it = objects.iter();

                let obj = it.next().unwrap();
                assert_matches!(obj, Object::Integer(0));

                let obj = it.next().unwrap();
                if let Object::Array(objects) = obj {
                    let mut it = objects.iter();

                    let obj = it.next().unwrap();
                    assert_matches!(obj, Object::Integer(1));

                    let obj = it.next().unwrap();
                    assert_matches!(obj, Object::Integer(2));

                    let obj = it.next().unwrap();
                    if let Object::Array(objects) = obj {
                        let mut it = objects.iter();

                        let obj = it.next().unwrap();
                        assert_matches!(obj, Object::Integer(3));

                        let obj = it.next().unwrap();
                        assert_matches!(obj, Object::Integer(4));
                    } else {
                        panic!("should be an array");
                    }

                    let obj = it.next().unwrap();
                    assert_matches!(obj, Object::Integer(5));
                } else {
                    panic!("should be an array");
                }

                let obj = it.next().unwrap();
                assert_matches!(obj, Object::Integer(6));
            }
            _ => panic!("must be an array"),
        }
    }
}
