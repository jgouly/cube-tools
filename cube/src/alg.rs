use crate::{Face, Slice};

mod parser;
pub use parser::parse_alg;

/// The amount of a move.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Amount {
  Single,
  Double,
}

impl std::fmt::Display for Amount {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Amount::Single => Ok(()),
      Amount::Double => write!(f, "2"),
    }
  }
}

/// The direction of a move.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Direction {
  Clockwise,
  AntiClockwise,
}

impl Direction {
  fn invert(self) -> Direction {
    match self {
      Direction::Clockwise => Direction::AntiClockwise,
      Direction::AntiClockwise => Direction::Clockwise,
    }
  }
}

impl std::fmt::Display for Direction {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Direction::Clockwise => Ok(()),
      Direction::AntiClockwise => write!(f, "'"),
    }
  }
}

/// Represents a move of the cube.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Move {
  Face(Face, Amount, Direction),
  Slice(Slice, Amount, Direction),
}

impl Move {
  fn invert(&self) -> Move {
    match self {
      Move::Face(f, amt, dir) => Move::Face(*f, *amt, dir.invert()),
      Move::Slice(s, amt, dir) => Move::Slice(*s, *amt, dir.invert()),
    }
  }
}

impl std::fmt::Display for Move {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Move::Face(face, amt, dir) => write!(f, "{:?}{}{}", face, amt, dir),
      Move::Slice(slice, amt, dir) => write!(f, "{:?}{}{}", slice, amt, dir),
    }
  }
}

#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Alg {
  Seq(Vec<Move>),
  Comm(Box<Alg>, Box<Alg>),
  Conj(Box<Alg>, Box<Alg>),
}

impl Alg {
  fn seq_as_vec(self) -> Vec<Move> {
    if let Alg::Seq(moves) = self {
      moves
    } else {
      unreachable!()
    }
  }

  /// Expand an Alg into an Alg::Seq.
  pub fn expand(&self) -> Alg {
    let mut moves = vec![];
    match self {
      Alg::Seq(inner) => moves = inner.clone(),
      Alg::Comm(a, b) => {
        let a = a.expand().seq_as_vec();
        let b = b.expand().seq_as_vec();
        moves.extend(a.clone());
        moves.extend(b.clone());
        moves.extend(a.iter().rev().map(|m| m.invert()));
        moves.extend(b.iter().rev().map(|m| m.invert()));
      }
      Alg::Conj(a, b) => {
        let a = a.expand().seq_as_vec();
        let b = b.expand().seq_as_vec();
        moves.extend(a.clone());
        moves.extend(b);
        moves.extend(a.iter().rev().map(|m| m.invert()));
      }
    }
    Alg::Seq(moves)
  }

  pub fn invert(&self) -> Alg {
    match self {
      Alg::Seq(inner) => {
        Alg::Seq(inner.iter().rev().map(|m| m.invert()).collect())
      }
      Alg::Comm(a, b) => Alg::Comm(b.clone(), a.clone()),
      Alg::Conj(a, b) => Alg::Conj(a.clone(), Box::new(b.invert())),
    }
  }

  pub fn iter(&self) -> impl Iterator<Item = Move> {
    self.expand().seq_as_vec().into_iter()
  }
}

impl std::fmt::Display for Alg {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Alg::Seq(moves) => write!(
        f,
        "{}",
        moves
          .iter()
          .map(|m| format!("{} ", m))
          .collect::<String>()
          .trim_end()
      ),
      Alg::Comm(a, b) => write!(f, "[{}, {}]", a, b),
      Alg::Conj(a, b) => write!(f, "[{}: {}]", a, b),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use parser::parse_alg;
  use std::string::ToString;

  #[test]
  fn display() {
    assert_eq!("R", parse_alg("R").unwrap().to_string());
    assert_eq!("U2", parse_alg("U2").unwrap().to_string());
    assert_eq!("D2'", parse_alg("D2'").unwrap().to_string());
    assert_eq!("L'", parse_alg("L'").unwrap().to_string());
    assert_eq!("E", parse_alg("E").unwrap().to_string());
    assert_eq!("M2", parse_alg("M2").unwrap().to_string());
    assert_eq!("S'", parse_alg("S'").unwrap().to_string());

    assert_eq!("[R, U]", parse_alg("[R,U]").unwrap().to_string());
    assert_eq!("[D: U]", parse_alg("[ D   :U ]").unwrap().to_string());
  }

  #[test]
  fn expand() {
    let comm = parse_alg("[R, U]").unwrap();
    assert_eq!(parse_alg("R U R' U'").unwrap(), comm.expand());

    let conj = parse_alg("[R: U]").unwrap();
    assert_eq!(parse_alg("R U R'").unwrap(), conj.expand());

    let alg = parse_alg("[D: [R, U]]").unwrap();
    assert_eq!(parse_alg("D R U R' U' D'").unwrap(), alg.expand());

    let alg = parse_alg("[R': [R, U]]").unwrap();
    assert_eq!(parse_alg("R' R U R' U' R").unwrap(), alg.expand());
  }

  #[test]
  fn invert() {
    let alg = parse_alg("R U R'").unwrap();
    assert_eq!(parse_alg("R U' R'").unwrap(), alg.invert());

    let alg = parse_alg("[R, U]").unwrap();
    assert_eq!(parse_alg("[U, R]").unwrap(), alg.invert());

    let alg = parse_alg("[F: [R, U]]").unwrap();
    assert_eq!(parse_alg("[F: [U, R]]").unwrap(), alg.invert());

    let alg = parse_alg("[F: R U R']").unwrap();
    assert_eq!(parse_alg("[F: R U' R']").unwrap(), alg.invert());
  }
}
