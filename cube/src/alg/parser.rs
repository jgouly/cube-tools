use crate::alg::{Amount, Direction, Face, Move};
use std::convert::TryFrom;

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct ParseError;

fn split_first(a: &str) -> Option<(char, &str)> {
  let mut chars = a.chars();
  chars.next().map(|c| (c, chars.as_str()))
}

fn parse_move_suffix(input: &str) -> ((Amount, Direction), &str) {
  let (amt, input) = match split_first(input) {
    Some(('2', rest)) => (Amount::Double, rest),
    _ => (Amount::Single, input),
  };

  let (dir, input) = match split_first(input) {
    Some(('\'', rest)) => (Direction::AntiClockwise, rest),
    _ => (Direction::Clockwise, input),
  };

  ((amt, dir), input)
}

fn parse_move(input: &str) -> Result<(Move, &str), ParseError> {
  match split_first(input) {
    Some((c, rest)) => {
      if let Ok(face) = Face::try_from(c) {
        let ((amt, dir), rest) = parse_move_suffix(rest);
        Ok((Move::Face(face, amt, dir), rest))
      } else {
        Err(ParseError)
      }
    }
    None => unreachable!("parse_move called with whitespace only!"),
  }
}

type Alg = Vec<Move>;

pub fn parse_alg(input: &str) -> Result<Alg, ParseError> {
  let mut input = input;
  std::iter::from_fn(|| {
    input = input.trim_start();
    if input.len() == 0 {
      return None;
    }
    let result = parse_move(input);
    if let Ok((_, new_input)) = &result {
      input = new_input;
    };
    Some(result.map(|r| r.0))
  })
  .collect()
}

#[cfg(test)]
mod tests {
  use super::*;
  use {Amount::*, Direction::*, Face::*};

  #[test]
  fn moves() {
    let faces = [(U, "U"), (R, "R")];
    for f in &faces {
      assert_eq!(
        Ok((Move::Face(f.0, Amount::Single, Direction::Clockwise), "")),
        parse_move(f.1)
      );
    }
  }

  #[test]
  fn simple_algs() {
    assert_eq!(Ok(vec![]), parse_alg(" "));

    assert_eq!(
      Ok(vec![
        Move::Face(R, Single, Clockwise),
        Move::Face(U, Single, Clockwise),
      ]),
      parse_alg(" R U ")
    );

    assert_eq!(
      Ok(vec![
        Move::Face(R, Double, Clockwise),
        Move::Face(U, Single, AntiClockwise),
        Move::Face(D, Double, AntiClockwise),
      ]),
      parse_alg("R2 U' D2'")
    );
  }

  #[test]
  fn invalid() {
    assert_eq!(Err(ParseError), parse_alg("a"));
    assert_eq!(Err(ParseError), parse_alg("R '"));
    assert_eq!(Err(ParseError), parse_alg("R 2"));
    assert_eq!(Err(ParseError), parse_alg("R'2"));
    assert_eq!(Err(ParseError), parse_alg("R3"));
  }
}
