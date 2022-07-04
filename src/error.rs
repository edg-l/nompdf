use std::{str::Utf8Error, num::ParseIntError};

use nom::{
    error::{ErrorKind, FromExternalError, ParseError},
    IResult,
};

pub type PDFResult<'a, T> = IResult<&'a [u8], T, PDFError>;

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum PDFError {
    #[error("invalid utf8")]
    InvalidUTF8(#[from] Utf8Error),
    #[error("parse int error: {0:?}")]
    ParseIntError(#[from] ParseIntError),
    #[error("nom error: {0:?}")]
    NomError(ErrorKind),
}

impl From<PDFError> for nom::Err<PDFError> {
    fn from(e: PDFError) -> Self {
        nom::Err::Error(e)
    }
}

impl From<ErrorKind> for PDFError {
    fn from(e: ErrorKind) -> Self {
        PDFError::NomError(e)
    }
}

impl<I> ParseError<I> for PDFError {
    fn from_error_kind(_input: I, kind: ErrorKind) -> Self {
        Self::NomError(kind)
    }
    fn append(_input: I, kind: ErrorKind, _other: Self) -> Self {
        Self::NomError(kind)
    }
}

impl<T> FromExternalError<T, Utf8Error> for PDFError {
    fn from_external_error(_: T, _: ErrorKind, e: Utf8Error) -> Self {
        Self::InvalidUTF8(e)
    }
}
