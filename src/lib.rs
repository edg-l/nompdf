use nom::branch::alt;
use nom::combinator::map_res;
use nom::{
    bytes::complete::tag,
    character::complete::{char, digit1},
    IResult,
};
use std::{collections::HashMap, fmt::Debug, io::Read, ops::RangeInclusive};

// TODO: change strings to use a new type and add methods to decode/encode to pdf string format.

/// What PDF considers white space characters.
pub const WHITE_SPACE_CHARS: [u8; 6] = [0x00, 0x09, 0x0A, 0x0C, 0x0D, 0x20];

#[derive(Debug, Clone, PartialEq, PartialOrd, Hash)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// A name object.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NameObject<'a>(pub &'a str);

/// A PDF dictionary object.
type DictionaryObject<'a> = HashMap<NameObject<'a>, Object<'a>>;

type HexString<'a> = &'a str;

/// An indirect object reference.
// Represented in PDFs like "12 0 R"
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

impl<'a> Object<'a> {
    fn parse_bool(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        let (inp, res) = alt((tag("true"), tag("false")))(inp)?;
        let value = res.eq_ignore_ascii_case("true");
        Ok((inp, Object::Boolean(value)))
    }

    fn parse_integer(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_real(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_literal_string(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_hex_string(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_name(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_array(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_dictionary(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_stream(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
    }

    fn parse_null(inp: &'a str) -> IResult<&'a str, Object<'a>> {
        todo!()
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
    use pretty_assertions::assert_eq;
    use matches::assert_matches;

    use super::*;

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
    }
}
