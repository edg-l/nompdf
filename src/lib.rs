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

use nom::branch::alt;
use nom::bytes::complete::{take_till, take_while, take_while1};
use nom::character::complete::hex_digit1;
use nom::combinator::{eof, map_res, recognize};
use nom::error::{Error, ErrorKind, ParseError};
use nom::number::complete;
use nom::sequence::{delimited, pair};
use nom::{bytes::complete::tag, character::complete::char, character::complete::digit1, IResult};
use std::{collections::HashMap, fmt::Debug, io::Read, ops::RangeInclusive};

// TODO: change strings to use a new type and add methods to decode/encode to pdf string format.

/// What PDF considers white space characters.
pub const WHITE_SPACE_CHARS: [char; 6] = [
    0x00 as char,
    0x09 as char,
    0x0A as char,
    0x0C as char,
    0x0D as char,
    0x20 as char,
];

#[derive(Debug, Clone, PartialEq, PartialOrd, Hash)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// A name object.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug)]
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
#[derive(Debug)]
pub struct PDF<'a> {
    pub header: Header,
    pub objects: Vec<Object<'a>>,
    pub cross_references: Vec<SubSection>,
    pub trailer: Trailer<'a>,
    /// Byte offset of last cross reference section.
    pub byte_offset: u64,
}

impl Header {
    fn from_str(inp: &str) -> IResult<&str, Header> {
        let (inp, _) = tag("%PDF-")(inp)?;
        let mut parse_digit = map_res(digit1, |s: &str| s.parse::<u32>());

        let (inp, major) = parse_digit(inp)?;
        let (inp, _) = char('.')(inp)?;
        let (inp, minor) = parse_digit(inp)?;

        Ok((inp, Header { major, minor }))
    }
}

// Adapted from https://stackoverflow.com/questions/70630556/parse-allowing-nested-parentheses-in-nom
// https://github.com/Geal/nom/issues/1253
pub fn take_until_unbalanced(
    opening_bracket: char,
    closing_bracket: char,
) -> impl Fn(&str) -> IResult<&str, &str> {
    move |i: &str| {
        let mut index = 0;
        let mut bracket_counter = 0;
        while let Some(n) = &i[index..].find(&[opening_bracket, closing_bracket, '\\'][..]) {
            index += n;
            let mut it = i[index..].chars();
            match it.next().unwrap_or_default() {
                c if c == '\\' => {
                    // Skip the escape char `\`.
                    index += '\\'.len_utf8();
                    // Skip also the following char.
                    let c = it.next().unwrap_or_default();
                    index += c.len_utf8();
                }
                c if c == opening_bracket => {
                    bracket_counter += 1;
                    index += opening_bracket.len_utf8();
                }
                c if c == closing_bracket => {
                    // Closing bracket.
                    bracket_counter -= 1;
                    index += closing_bracket.len_utf8();
                }
                // Can not happen.
                _ => unreachable!(),
            };
            // We found the unmatched closing bracket.
            if bracket_counter == -1 {
                // We do not consume it.
                index -= closing_bracket.len_utf8();
                return Ok((&i[index..], &i[0..index]));
            };
        }

        if bracket_counter == 0 {
            Ok(("", i))
        } else {
            Err(nom::Err::Error(Error::from_error_kind(
                i,
                ErrorKind::TakeUntil,
            )))
        }
    }
}

/// Returns everything until a whitespace is found.
#[inline]
fn till_whitespace(inp: &str) -> IResult<&str, &str> {
    take_till(|c: char| WHITE_SPACE_CHARS.contains(&c))(inp)
}

/// Returns all the whitespace until a non-whitespace character is found.
#[inline]
fn skip_whitespace(inp: &str) -> IResult<&str, &str> {
    take_while(|c: char| WHITE_SPACE_CHARS.contains(&c))(inp)
}

/// Most objects should be separated by whitespace or eof, this is needed to ensure "nullthisisbad"
/// doesn't simply match null for a null object and then ignores the rest of the word.
#[inline]
fn take_whitespace_eof(inp: &str) -> IResult<&str, &str> {
    alt((eof, take_while1(|c: char| WHITE_SPACE_CHARS.contains(&c))))(inp)
}

// General rule of individual parsers: Assume there is no whitespace at the start.
impl<'a> Object<'a> {
    fn parse_bool(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, res) = alt((tag("true"), tag("false")))(inp)?;
        let value = res.eq_ignore_ascii_case("true");
        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::Boolean(value)))
    }

    // 123 43445 +17 −98 0
    fn parse_integer(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, value) = map_res(
            alt((
                recognize(pair(tag("+"), digit1)),
                recognize(pair(tag("-"), digit1)),
                recognize(digit1),
            )),
            |s: &str| s.parse::<i32>(),
        )(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;

        Ok((inp, Object::Integer(value)))
    }

    fn parse_real(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, value) = complete::float(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;

        Ok((inp, Object::Real(value)))
    }

    fn parse_numeric(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, value) = till_whitespace(inp)?;

        if value.contains('.') {
            let (_, obj) = Object::parse_real(value)?;
            Ok((inp, obj))
        } else {
            let (_, obj) = Object::parse_integer(value)?;
            Ok((inp, obj))
        }
    }

    fn parse_literal_string(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, value) = delimited(tag("("), take_until_unbalanced('(', ')'), tag(")"))(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::LiteralString(value)))
    }

    // <4E6F762073686D6F7A206B6120706F702E>
    /// If the final digit of a hexadecimal string is missing—that is, if there is an odd
    /// number of digits—the final digit is assumed to be 0.
    fn parse_hex_string(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, value) = delimited(tag("<"), hex_digit1, tag(">"))(inp)?;

        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::HexadecimalString(value)))
    }

    fn parse_name(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, _) = tag("/")(inp)?;
        let (inp, value) = till_whitespace(inp)?;
        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::Name(NameObject(value))))
    }

    fn parse_array(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (original_inp, value) =
            delimited(tag("["), take_until_unbalanced('[', ']'), tag("]"))(inp)?;

        let mut objs = Vec::new();

        let (mut outer_inp, _) = take_while(|c: char| WHITE_SPACE_CHARS.contains(&c))(value)?;

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

    fn parse_dictionary(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (original_inp, value) =
            delimited(tag("<"), take_until_unbalanced('<', '>'), tag(">"))(inp)?;

        // Remove remaining <>
        let (_, value) = delimited(tag("<"), take_until_unbalanced('<', '>'), tag(">"))(value)?;

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

    fn parse_stream(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_null(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, _) = tag("null")(inp)?;
        let (inp, _) = take_whitespace_eof(inp)?;
        Ok((inp, Object::Null))
    }

    fn parse_indirect(inp: &'a str) -> IResult<&'a str, Object<'a>> {
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
            let (data, header) = Header::from_str(&data).unwrap();
            assert_eq!(header.major, 1u32);
            assert_eq!(header.minor, minor);
            assert!(data.is_empty())
        }
    }

    #[test]
    fn test_object_bool() {
        let data = "true";
        let (_, object) = Object::parse_bool(data).unwrap();
        assert_matches!(object, Object::Boolean(true));

        let data = "false";
        let (_, object) = Object::parse_bool(data).unwrap();
        assert_matches!(object, Object::Boolean(false));

        let data = "truee";
        Object::parse_bool(data).unwrap_err();

        let data = "falsee";
        Object::parse_bool(data).unwrap_err();

        let data = "afalse";
        Object::parse_bool(data).unwrap_err();
    }

    #[test]
    fn test_object_null() {
        let data = "null";
        let (_, object) = Object::parse_null(data).unwrap();
        assert_matches!(object, Object::Null);

        let data = "nulla";
        Object::parse_null(data).unwrap_err();

        let data = "anull";
        Object::parse_null(data).unwrap_err();
    }

    #[test]
    fn test_object_integer() {
        fn test_value(inp: &str, expected: i32) {
            let (_, object) = Object::parse_integer(inp).unwrap();

            if let Object::Integer(x) = object {
                assert_eq!(x, expected);
            }
        }

        test_value("3", 3);
        test_value("+3", 3);
        test_value("0", 0);
        test_value("0   ", 0);

        let data = "1 2 3";
        let (data, object) = Object::parse_integer(data).unwrap();
        assert_matches!(object, Object::Integer(1));

        let (data, object) = Object::parse_integer(&data).unwrap();
        assert_matches!(object, Object::Integer(2));

        let (_, object) = Object::parse_integer(&data).unwrap();
        assert_matches!(object, Object::Integer(3));

        Object::parse_integer("3a").unwrap_err();
        Object::parse_integer("-3a").unwrap_err();
        Object::parse_integer("a").unwrap_err();
        Object::parse_integer("a3").unwrap_err();
    }

    #[test]
    fn test_object_real() {
        fn test_value(inp: &str, expected: f32) {
            let (_, object) = Object::parse_real(inp).unwrap();

            if let Object::Real(x) = object {
                assert_eq!(x, expected);
            }
        }

        test_value("34.5", 34.5);
        test_value(".5", 0.5);
        test_value("4.", 4.0);
        test_value("+123.6", 123.6);
        test_value("-.002", -0.002);
        test_value("0.0", 0.0);
        test_value("0.0    ", 0.0);

        Object::parse_real("0.0a").unwrap_err();
        Object::parse_real("a0.0").unwrap_err();
        Object::parse_real(".0e").unwrap_err();
    }

    #[test]
    fn test_object_numeric() {
        fn test_value_real(inp: &str, expected: f32) {
            let (_, object) = Object::parse_numeric(inp).unwrap();

            if let Object::Real(x) = object {
                assert_eq!(x, expected);
            }
        }

        fn test_value_integer(inp: &str, expected: i32) {
            let (_, object) = Object::parse_integer(inp).unwrap();

            if let Object::Integer(x) = object {
                assert_eq!(x, expected);
            }
        }

        test_value_real("34.5", 34.5);
        test_value_real(".5", 0.5);
        test_value_real("4.", 4.0);
        test_value_real("+123.6", 123.6);
        test_value_real("-.002", -0.002);
        test_value_real("0.0", 0.0);

        test_value_integer("3", 3);
        test_value_integer("+3", 3);
        test_value_integer("0", 0);
    }

    #[test]
    fn test_object_name() {
        fn test_value(inp: &str, expected: &str) {
            let (_, object) = Object::parse_name(inp).unwrap();
            assert_matches!(object, Object::Name(NameObject(expected)));
        }

        test_value("/Adobe", "Adobe");
        test_value("/Test ", "Test");
        test_value("/Test2     ", "Test2");
    }

    #[test]
    fn test_object_literal_string() {
        fn test_value(inp: &str, expected: &str) {
            let (_, object) = Object::parse_literal_string(inp).unwrap();
            assert_matches!(object, Object::LiteralString(expected));
        }

        test_value("(hello world)", "hello world");
        test_value("((hello world))", "(hello world)");
        test_value("(this (is) a test)", "this (is) a test");

        Object::parse_literal_string("(dsd").unwrap_err();
        Object::parse_literal_string("(dsd)a").unwrap_err();
        Object::parse_literal_string("(dsd)a ").unwrap_err();
    }

    #[test]
    fn test_object_hex_string() {
        fn test_value(inp: &str, expected: &str) {
            let (_, object) = Object::parse_hex_string(inp).unwrap();
            assert_matches!(object, Object::HexadecimalString(expected));
        }

        test_value(
            "<4E6F762073686D6F7A206B6120706F702E>",
            "4E6F762073686D6F7A206B6120706F702E",
        );

        test_value(
            "<4E6F762073686D6F7A206B6120706F702E>   ",
            "4E6F762073686D6F7A206B6120706F702E",
        );

        Object::parse_hex_string("<AAA>a").unwrap_err();
        Object::parse_hex_string("<AAA>a ").unwrap_err();
    }

    #[test]
    fn test_object_dict() {
        Object::parse_dictionary("<< /First true >>").unwrap();

        let (_, object) = Object::parse_dictionary(
            r#"<<  /First true
                /SubDict << /Hello (world) >>
            >>"#,
        )
        .unwrap();
        println!("{:#?}", object);
        // TODO: improve tests
    }

    #[test]
    fn test_object_array() {
        let (_, object) = Object::parse_array("[0 3.14 false (Ralph) /SomeName]").unwrap();

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
        let (_, object) = Object::parse_array("[0 [1 2 [3 4] 5] 6]").unwrap();

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
