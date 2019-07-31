#![allow(unused_macros)]
//! Nomplus is an extension to nom.
//!
//! It provides some parsers and combinators that I find useful in parsing languages.
//!
//! Whitespace parsing is based on plus_space0 and plus_space1 parsers.
//! They default to eating spaces and tabs. But the macro will happilly
//! take any function in the current namespace, so you can either `use` them
//! or redefine them.
//! We use use macro especially to permit this overriding.

use nom::error::{ParseError};
use nom::{Err,InputTakeAtPosition,AsChar,IResult};
use nom::character::complete::{space0,space1};


/// Default space eating parser that points to complete::space0.
/// Redefine to change the behaviour of macros below
pub fn plus_space0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E> 
where T: InputTakeAtPosition,
      <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
    space0(input)
}

/// Default space eating parser that points to complete::space1.
/// Redefine to change the behaviour of macros below
pub fn plus_space1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where T: InputTakeAtPosition,
      <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
    space1(input)
}

/// Surround the given parser with space parsing (using plus_space0 space eater)
///
/// Typical example:
/// ```text
///   sp!(tag("tag"))
/// ```
#[macro_export]
macro_rules! sp {
    ($parser:expr) => {
        nom::sequence::delimited(plus_space0,$parser,plus_space0)
    };
}

/// Surround the given parser with space parsing, with at least one space after the parser 
/// (using plus_space0 first then plus_space1)
///
/// Typical example:
/// ```text
///   sp1!(tag("tag"))
/// ```
#[macro_export]
macro_rules! sp1 {
    ($parser:expr) => {
        nom::sequence::delimited(plus_space0,$parser,plus_space1)
    };
}

/// A bit like do_parse!
///
/// Transforms:
/// ```text
///     {
///         variable: combinator(parser);
///         ...
///     } => Object { variable, ... }
/// ```
/// Into a series of sequential calls like this:
/// ```text
///     |i|
///     let(i,variable) = combinator(parser)(i)?;
///     let (i,_) = strip_spaces_and_comment(i)?
///     ...
///     Ok((i,Object { variable, ... }))
/// ```
///
/// The result is a closure parser that can be used in place of any other parser
///
/// We don't use a list or a tuple for sequence parsing because we want to
/// use some intermediary result at some steps (for example for error management).
///
/// Typical example: 
/// ```text
///   sequence!( 
///     {
///       x: tag("tag");
///       y: tag("y");
///     } => (x,y)
///   )
/// ```
#[macro_export]
macro_rules! sequence {
    ( { $($f:ident : $parser:expr;)* } => $output:expr ) => {
        move |i| {
            $(
                let (i,$f) = $parser (i)?;
            )*
            Ok((i, $output))
        }
    };
}
/// wsequence is the same a sequence, but we automatically insert space parsing between each call
/// (using plus_space0)
/// Note that spaces are eaten at the end of this parser but not at the beginning.
#[macro_export]
macro_rules! wsequence {
    ( { $($f:ident : $parser:expr;)* } => $output:expr ) => {
        move |i| {
            $(
                let (i,$f) = $parser (i)?;
                let (i,_) = plus_space0(i)?;
            )*
            Ok((i, $output))
        }
    };
}

/// Transforms an error to a failure generated with the given closure
/// 
/// Example with the ErrorKind:
/// ```text
///   cut_with(tag("tag"), |(i,e)| (i,ErrorKind::Something))
/// ```
/// Equivalent to cut:
/// ```text
///   cut_with(tag("tag"), |e| e)
/// ```
pub fn cut_with<I, O, E1: ParseError<I>, E2: ParseError<I>, F, E>(parser: F, erf: E) -> impl Fn(I) -> IResult<I, O, E2>
where
  F: Fn(I) -> IResult<I, O, E1>,
  E: Fn(E1) -> E2,
{
  move |input: I| {
    match parser(input) {
      Err(Err::Failure(e)) => Err(Err::Failure(erf(e))),
      Err(Err::Error(e)) => Err(Err::Failure(erf(e))),
      Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
      Ok(rest) => Ok(rest),
    }
  }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::error::*;
    use nom::multi::*;
    use nom::sequence::*;
    use nom::character::complete::*;
    use nom::bytes::complete::*;

    type Result<'a, O> = IResult<&'a str, O, (&'a str, ErrorKind)>;
 
    // Provide a 2nd implementation of plus_space0
    fn other_space0<'a>(input: &'a str) -> Result<'a, &'a str>
    {
        // with @ as a separator because why not
        let (i,_) = many0(tag("@"))(input)?;
        Ok((i,""))
    }
    // Provide a 2nd implementation of plus_space1
    fn other_space1<'a>(input: &'a str) -> Result<'a, &'a str>
    {
        let (i,_) = many1(tag("@"))(input)?;
        Ok((i,""))
    }

    // Force typing of result to make assert compile
    fn spair<'a,O1,O2,F,G>(first: F, second: G) -> 
        impl Fn(&'a str) -> Result<'a, (O1, O2)> 
        where F: Fn(&'a str) -> Result<'a, O1>,
              G: Fn(&'a str) -> Result<'a, O2>, 
    {
        pair(first,second)
    }

    #[test]
    fn test_default_sp() {
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("xy"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("x y"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("   x \t y \n"),
                   Ok(("\n",("x","y")))
        );
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("x@y"),
                   Err(Err::Error(("@y", ErrorKind::Alpha)))
        );
    }

    #[test]
    fn test_other_sp() {
        use other_space0 as plus_space0;
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("xy"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("x@y"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("@x@@y@"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp!(tag("x")),sp!(alpha1))("x y"),
                   Err(Err::Error((" y", ErrorKind::Alpha)))
        );
    }

    #[test]
    fn test_default_sp1() {
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("xy"),
                   Err(Err::Error(("y", ErrorKind::Space)))
        );
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("x y"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("   x \t y \n"),
                   Ok(("\n",("x","y")))
        );
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("x@y"),
                   Err(Err::Error(("@y", ErrorKind::Space)))
        );
    }

    #[test]
    fn test_other_sp1() {
        use other_space0 as plus_space0;
        use other_space1 as plus_space1;
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("xy"),
                   Err(Err::Error(("y", ErrorKind::Tag)))
        );
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("x@y"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("@x@@y@"),
                   Ok(("",("x","y")))
        );
        assert_eq!(spair(sp1!(tag("x")),sp!(alpha1))("x y"),
                   Err(Err::Error((" y", ErrorKind::Tag)))
        );
    }

    fn fsequence<'a>(input: &'a str) -> Result<'a, (&'a str, &'a str)> {
        sequence!({
            x: tag("x");
            y: alpha1;
        } => (x,y)) (input)
    }
    fn fwsequence<'a>(input: &'a str) -> Result<'a, (&'a str, &'a str)> {
        wsequence!({
            x: tag("x");
            y: alpha1;
        } => (x,y)) (input)
    }
    fn fwsequence1<'a>(input: &'a str) -> Result<'a, (&'a str, &'a str)> {
        wsequence!({
            x: sp1!(tag("x"));
            y: alpha1;
        } => (x,y)) (input)
    }

    #[test]
    fn test_sequence() {
        assert_eq!(fsequence("xy"),
                   Ok(("",("x","y")))
        );
        assert_eq!(fsequence("x y"),
                   Err(Err::Error((" y", ErrorKind::Alpha)))
        );
    }

    #[test]
    fn test_wsequence() {
        assert_eq!(fwsequence("xy"),
                   Ok(("",("x","y")))
        );
        assert_eq!(fwsequence1("xy"),
                   Err(Err::Error(("y", ErrorKind::Space)))
        );
        assert_eq!(fwsequence("x y"),
                   Ok(("",("x","y")))
        );
        assert_eq!(fwsequence1("x y"),
                   Ok(("",("x","y")))
        );
    }

    #[test]
    fn test_cut_with() {
        assert_eq!(cut_with(pair(tag("x"),tag("y")), |(_,e)| (i,ErrorKind::TooLarge))("xy"),
                  Ok(("",("x","y")))
        );
        assert_eq!(cut_with(pair(tag("x"),tag("y")), |(_,e)| (i,ErrorKind::TooLarge))("xz"),
                  Err(Err::Failure(("z", ErrorKind::TooLarge)))
        );
    }
}

