use crate::alg::{Alg, Amount, Direction, Face, Move, Rotation, Slice, Width};
use std::convert::TryFrom;

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct ParseError;

fn split_first(a: &str) -> Option<(char, &str)> {
  let mut chars = a.chars();
  chars.next().map(|c| (c, chars.as_str()))
}

fn parse_move_suffix(input: &str) -> ((Amount, Direction, Width), &str) {
  let (width, input) = match split_first(input) {
    Some(('w', rest)) => (Width::Two, rest),
    _ => (Width::One, input),
  };

  let (amt, input) = match split_first(input) {
    Some(('2', rest)) => (Amount::Double, rest),
    _ => (Amount::Single, input),
  };

  let (dir, input) = match split_first(input) {
    Some(('\'', rest)) => (Direction::AntiClockwise, rest),
    _ => (Direction::Clockwise, input),
  };

  ((amt, dir, width), input)
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
    let ((amt, dir, width), input) = parse_move_suffix(next_input);
    Ok((Some(Move::Face(face, amt, dir, width)), input))
  } else if let Ok(slice) = Slice::try_from(c) {
    let ((amt, dir, width), input) = parse_move_suffix(next_input);
    match width {
      Width::One => Ok((Some(Move::Slice(slice, amt, dir)), input)),
      _ => Err(ParseError),
    }
  } else if let Ok(rotation) = Rotation::try_from(c) {
    let ((amt, dir, width), input) = parse_move_suffix(next_input);
    match width {
      Width::One => Ok((Some(Move::Rotation(rotation, amt, dir)), input)),
      _ => Err(ParseError),
    }
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
  if input.len() == 0 {
    return Err(ParseError);
  }

  match input.chars().next().unwrap() {
    '[' => {
      let (c, input) = split_first(input).ok_or(ParseError)?;
      assert_eq!('[', c);
      let (a, input) = parse_alg_inner(input, EndOfInputMode::Separator)?;
      let (sep, input) = split_first(input).ok_or(ParseError)?;
      assert!(sep == ',' || sep == ':');
      let (b, input) =
        parse_alg_inner(input.trim_start(), EndOfInputMode::RightBracket)?;
      let (c, input) = split_first(input).ok_or(ParseError)?;
      if c != ']' {
        return Err(ParseError);
      }

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

        // If there is a '[', let it be parsed as another
        // part of an Alg::Compound.
        if input.chars().next() == Some('[') {
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

  let (alg, input) = parse_alg_inner(input, EndOfInputMode::None)?;

  if input.trim_start().len() == 0 {
    return Ok(alg);
  }

  let mut algs = vec![alg];
  let mut input = input.trim_start();

  while input.len() > 0 {
    let (alg, remaining) = parse_alg_inner(input, EndOfInputMode::None)?;
    algs.push(alg);
    input = remaining.trim_start();
  }

  Ok(Alg::Compound(algs))
}

#[cfg(test)]
mod tests {
  use super::*;
  use {Amount::*, Direction::*, Face::*, Rotation::*, Slice::*, Width::*};

  #[test]
  fn moves() {
    let faces = [U, R, F, D, B, L];
    for &f in &faces {
      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Single, Clockwise, One)])),
        parse_alg(&format!("{:?}", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Single, AntiClockwise, One)])),
        parse_alg(&format!("{:?}'", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Double, Clockwise, One)])),
        parse_alg(&format!("{:?}2", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Double, AntiClockwise, One)])),
        parse_alg(&format!("{:?}2'", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Single, Clockwise, Two)])),
        parse_alg(&format!("{:?}w", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Single, AntiClockwise, Two)])),
        parse_alg(&format!("{:?}w'", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Double, Clockwise, Two)])),
        parse_alg(&format!("{:?}w2", f))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Face(f, Double, AntiClockwise, Two)])),
        parse_alg(&format!("{:?}w2'", f))
      );
    }

    let slices = [E, M, S];
    for &s in &slices {
      assert_eq!(
        Ok(Alg::Seq(vec![Move::Slice(s, Single, Clockwise)])),
        parse_alg(&format!("{:?}", s))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Slice(s, Single, AntiClockwise)])),
        parse_alg(&format!("{:?}'", s))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Slice(s, Double, Clockwise)])),
        parse_alg(&format!("{:?}2", s))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Slice(s, Double, AntiClockwise)])),
        parse_alg(&format!("{:?}2'", s))
      );

      assert_eq!(Err(ParseError), parse_alg(&format!("{:?}w", s)));
    }

    assert_eq!(
      Ok(Alg::Seq(vec![Move::Rotation(
        Rotation::X,
        Single,
        Clockwise
      )])),
      parse_alg("x")
    );

    let rotations = [X, Y, Z];
    for &s in &rotations {
      assert_eq!(
        Ok(Alg::Seq(vec![Move::Rotation(s, Single, Clockwise)])),
        parse_alg(&format!("{:?}", s))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Rotation(s, Single, AntiClockwise)])),
        parse_alg(&format!("{:?}'", s))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Rotation(s, Double, Clockwise)])),
        parse_alg(&format!("{:?}2", s))
      );

      assert_eq!(
        Ok(Alg::Seq(vec![Move::Rotation(s, Double, AntiClockwise)])),
        parse_alg(&format!("{:?}2'", s))
      );

      assert_eq!(Err(ParseError), parse_alg(&format!("{:?}w", s)));
    }
  }

  #[test]
  fn simple_algs() {
    assert_eq!(Ok(Alg::Seq(vec![])), parse_alg(" "));

    assert_eq!(
      Ok(Alg::Seq(vec![
        Move::Face(R, Single, Clockwise, One),
        Move::Face(U, Single, Clockwise, One),
      ])),
      parse_alg(" R U ")
    );

    assert_eq!(
      Ok(Alg::Seq(vec![
        Move::Face(R, Double, Clockwise, One),
        Move::Face(U, Single, AntiClockwise, One),
        Move::Face(D, Double, AntiClockwise, One),
      ])),
      parse_alg("R2 U' D2'")
    );
  }

  #[test]
  fn commutators() {
    assert_eq!(
      Ok(Alg::Comm(
        Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise, One)])),
        Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)])),
      )),
      parse_alg("[R, U]")
    );
    assert!(parse_alg(" [ R  ,U  ] ").is_ok());

    assert_eq!(
      Ok(Alg::Comm(
        Box::new(Alg::Comm(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise, One)])),
          Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)])),
        )),
        Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)]))
      )),
      parse_alg("[[R, U], U]")
    );

    assert_eq!(
      Ok(Alg::Comm(
        Box::new(Alg::Seq(vec![Move::Face(U, Double, Clockwise, One)])),
        Box::new(Alg::Comm(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, AntiClockwise, One)])),
          Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)])),
        ))
      )),
      parse_alg("[U2, [R', U]]")
    );
  }

  #[test]
  fn conjugates() {
    assert_eq!(
      Ok(Alg::Conj(
        Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise, One)])),
        Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)])),
      )),
      parse_alg("[R: U]")
    );
  }

  #[test]
  fn compound() {
    assert_eq!(
      Ok(Alg::Compound(vec![
        Alg::Conj(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise, One)])),
          Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)])),
        ),
        Alg::Conj(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, AntiClockwise, One)])),
          Box::new(Alg::Seq(vec![Move::Face(F, Single, Clockwise, One)])),
        )
      ])),
      parse_alg("[R: U] [R': F]")
    );

    assert_eq!(
      Ok(Alg::Compound(vec![
        Alg::Seq(vec![Move::Face(R, Single, Clockwise, One)]),
        Alg::Comm(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, Clockwise, One)])),
          Box::new(Alg::Seq(vec![Move::Face(U, Single, Clockwise, One)])),
        ),
        Alg::Conj(
          Box::new(Alg::Seq(vec![Move::Face(R, Single, AntiClockwise, One)])),
          Box::new(Alg::Seq(vec![Move::Face(F, Single, Clockwise, One)])),
        ),
        Alg::Seq(vec![Move::Face(D, Single, Clockwise, One)]),
      ])),
      parse_alg("R [R, U] [R': F] D")
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
    assert_eq!(Err(ParseError), parse_alg("["));
    assert_eq!(Err(ParseError), parse_alg("[R, U"));
    assert_eq!(Err(ParseError), parse_alg("[R, U["));
    assert_eq!(Err(ParseError), parse_alg("[R] U]"));
    assert_eq!(Err(ParseError), parse_alg("R’"));
    assert_eq!(Err(ParseError), parse_alg("’"));
  }
}
