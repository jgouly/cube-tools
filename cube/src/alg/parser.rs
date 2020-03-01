use crate::alg::{Alg, Amount, Direction, Face, Move};
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

#[derive(Copy, Clone, Debug)]
enum EndOfInputMode {
  None,
  Separator,
  RightBracket,
}

fn parse_single_move(
  input: &str,
  mode: EndOfInputMode,
) -> Result<(Option<Move>, &str), ParseError> {
  let (c, next_input) = split_first(input).unwrap();
  if let Ok(face) = Face::try_from(c) {
    let ((amt, dir), input) = parse_move_suffix(next_input);
    Ok((Some(Move::Face(face, amt, dir)), input))
  } else {
    match (c, mode) {
      (':', EndOfInputMode::Separator) => Ok((None, input)),
      (',', EndOfInputMode::Separator) => Ok((None, input)),
      (']', EndOfInputMode::RightBracket) => Ok((None, input)),
      _ => Err(ParseError),
    }
  }
}

fn parse_alg_inner(
  input: &str,
  mode: EndOfInputMode,
) -> Result<(Alg, &str), ParseError> {
  match &input[0..1] {
    "[" => {
      let (c, input) = split_first(input).ok_or(ParseError)?;
      assert_eq!('[', c);
      let (a, input) = parse_alg_inner(input, EndOfInputMode::Separator)?;
      let (sep, input) = split_first(input).ok_or(ParseError)?;
      assert!(sep == ',' || sep == ':');
      let (b, input) =
        parse_alg_inner(input.trim_start(), EndOfInputMode::RightBracket)?;
      let (c, input) = split_first(input).ok_or(ParseError)?;
      assert_eq!(']', c);
      let a = Box::new(a);
      let b = Box::new(b);
      match sep {
        ',' => Ok((Alg::Comm(a, b), input)),
        ':' => Ok((Alg::Conj(a, b), input)),
        _ => unreachable!(),
      }
    }
    _ => {
      let mut input = input;

      let res = std::iter::from_fn(|| {
        input = input.trim_start();
        if input.len() == 0 {
          return None;
        }

        let result = parse_single_move(input, mode);

        if let Ok((_, new_input)) = &result {
          input = new_input;
        };

        result.map(|r| r.0).transpose()
      })
      .collect::<Result<Vec<Move>, ParseError>>()?;
      Ok((Alg::Seq(res), input))
    }
  }
}

pub fn parse_alg(input: &str) -> Result<Alg, ParseError> {
  let input = input.trim_start();
  if input.len() == 0 {
    return Ok(Alg::Seq(vec![]));
  }
  parse_alg_inner(input, EndOfInputMode::None).map(|r| {
    assert!(r.1.trim_start().len() == 0);
    r.0
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use {Amount::*, Direction::*, Face::*};

  #[test]
  fn moves() {
    let faces = [U, R, F, D, B, L];
    for &f in &faces {
      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Single, Clockwise)])),
        parse_alg(&format!("{:?}", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Single, AntiClockwise)])),
        parse_alg(&format!("{:?}'", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Double, Clockwise)])),
        parse_alg(&format!("{:?}2", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Double, AntiClockwise)])),
        parse_alg(&format!("{:?}2'", f))
      );
    }
  }

  #[test]
  fn simple_algs() {
    assert_eq!(Ok(Alg::Seq(vec![])), parse_alg(" "));

    assert_eq!(
      Ok(Alg::Seq(vec![
        Move::Face(R, Single, Clockwise),
        Move::Face(U, Single, Clockwise),
      ])),
      parse_alg(" R U ")
    );

    assert_eq!(
      Ok(Alg::Seq(vec![
        Move::Face(R, Double, Clockwise),
        Move::Face(U, Single, AntiClockwise),
        Move::Face(D, Double, AntiClockwise),
      ])),
      parse_alg("R2 U' D2'")
    );
  }

  #[test]
  fn commutators() {
    assert_eq!(
      Ok(Alg::Comm(
        Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise)])),
        Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise)])),
      )),
      parse_alg("[R, U]")
    );
    assert!(parse_alg(" [ R  ,U  ] ").is_ok());

    assert_eq!(
      Ok(Alg::Comm(
        Box::new(Alg::Comm(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise)])),
          Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise)])),
        )),
        Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise)]))
      )),
      parse_alg("[[R, U], U]")
    );

    assert_eq!(
      Ok(Alg::Comm(
        Box::new(Alg::Seq(vec![Move::Face(U, Double, Clockwise)])),
        Box::new(Alg::Comm(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, AntiClockwise)])),
          Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise)])),
        ))
      )),
      parse_alg("[U2, [R', U]]")
    );
  }

  #[test]
  fn conjugates() {
    assert_eq!(
      Ok(Alg::Conj(
        Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise)])),
        Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise)])),
      )),
      parse_alg("[R: U]")
    );
  }

  #[test]
  fn invalid() {
    assert_eq!(Err(ParseError), parse_alg("a"));
    assert_eq!(Err(ParseError), parse_alg("R '"));
    assert_eq!(Err(ParseError), parse_alg("R 2"));
    assert_eq!(Err(ParseError), parse_alg("R'2"));
    assert_eq!(Err(ParseError), parse_alg("R3"));
    assert_eq!(Err(ParseError), parse_alg("R,"));
    assert_eq!(Err(ParseError), parse_alg("R:"));
    assert_eq!(Err(ParseError), parse_alg("[a"));
    assert_eq!(Err(ParseError), parse_alg("[R, U"));
    assert_eq!(Err(ParseError), parse_alg("[R, U["));
    assert_eq!(Err(ParseError), parse_alg("[R] U]"));
  }
}