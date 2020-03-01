use crate::Face;

mod parser;
pub use parser::parse_alg;

/// The amount of a move.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Amount {
  Single,
  Double,
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

/// Represents a move of the cube.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Move {
  Face(Face, Amount, Direction),
}

impl Move {
  fn invert(&self) -> Move {
    match self {
      Move::Face(f, amt, dir) => Move::Face(*f, *amt, dir.invert()),
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
}

#[cfg(test)]
mod tests {
  use super::*;
  use parser::parse_alg;

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
}
