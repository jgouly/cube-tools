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
#[derive(Clone, Copy, Debug, PartialEq)]
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

fn cancel_amt_and_dir(
  a0: Amount,
  d0: Direction,
  a1: Amount,
  d1: Direction,
) -> Option<(Amount, Direction)> {
  match (a0, a1) {
    (Amount::Single, Amount::Single) => {
      if d0 == d1 {
        Some((Amount::Double, d0))
      } else {
        None
      }
    }
    (Amount::Double, Amount::Double) => None,
    (Amount::Single, Amount::Double) => {
      if d0 == Direction::Clockwise {
        Some((Amount::Single, Direction::AntiClockwise))
      } else {
        Some((Amount::Single, Direction::Clockwise))
      }
    }
    (Amount::Double, Amount::Single) => {
      if d1 == Direction::Clockwise {
        Some((Amount::Single, Direction::AntiClockwise))
      } else {
        Some((Amount::Single, Direction::Clockwise))
      }
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Width {
  One,
  Two,
}

impl std::fmt::Display for Width {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Width::One => Ok(()),
      Width::Two => write!(f, "w"),
    }
  }
}

/// Represents a move of the cube.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Move {
  Face(Face, Amount, Direction, Width),
  Slice(Slice, Amount, Direction),
}

impl Move {
  fn amount(&self) -> Amount {
    match self {
      Move::Face(_, a, _, _) => *a,
      Move::Slice(_, a, _) => *a,
    }
  }

  fn direction(&self) -> Direction {
    match self {
      Move::Face(_, _, d, _) => *d,
      Move::Slice(_, _, d) => *d,
    }
  }

  fn invert(&self) -> Move {
    match self {
      Move::Face(f, amt, dir, width) => {
        Move::Face(*f, *amt, dir.invert(), *width)
      }
      Move::Slice(s, amt, dir) => Move::Slice(*s, *amt, dir.invert()),
    }
  }

  fn is_same_movement(&self, m: &Move) -> bool {
    match (self, m) {
      (Move::Face(f0, _, _, w0), Move::Face(f1, _, _, w1))
        if f0 == f1 && w0 == w1 =>
      {
        true
      }
      (Move::Slice(s0, _, _), Move::Slice(s1, _, _)) if s0 == s1 => true,
      _ => false,
    }
  }

  fn cancel(&self, m: &Move) -> Option<Option<Move>> {
    if self.is_same_movement(m) {
      if let Some((a, d)) = cancel_amt_and_dir(
        self.amount(),
        self.direction(),
        m.amount(),
        m.direction(),
      ) {
        match self {
          Move::Face(f, _, _, w) => Some(Some(Move::Face(*f, a, d, *w))),
          Move::Slice(s, _, _) => Some(Some(Move::Slice(*s, a, d))),
        }
      } else {
        Some(None)
      }
    } else {
      None
    }
  }
}

impl std::fmt::Display for Move {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Move::Face(face, amt, dir, width) => {
        write!(f, "{:?}{}{}{}", face, width, amt, dir)
      }
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
  Pair(Box<Alg>, Box<Alg>),
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
      Alg::Pair(a, b) => {
        let a = a.expand().seq_as_vec();
        let b = b.expand().seq_as_vec();
        moves.extend(a);
        moves.extend(b);
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
      Alg::Pair(a, b) => Alg::Pair(Box::new(b.invert()), Box::new(a.invert())),
    }
  }

  pub fn cancel(&self) -> Alg {
    match self {
      Alg::Seq(inner) => {
        let mut result = Vec::<Move>::with_capacity(inner.len());
        if inner.len() != 0 {
          for m in inner {
            match result.last().map(|l| l.cancel(m)) {
              Some(Some(Some(m))) => {
                *result.last_mut().unwrap() = m;
              }
              Some(Some(None)) => {
                result.pop();
              }
              Some(None) | None => {
                result.push(m.clone());
              }
            }
          }
        }
        Alg::Seq(result)
      }
      Alg::Comm(a, b) => Alg::Comm(Box::new(a.cancel()), Box::new(b.cancel())),
      Alg::Conj(a, b) => Alg::Conj(Box::new(a.cancel()), Box::new(b.cancel())),
      Alg::Pair(a, b) => Alg::Pair(Box::new(a.cancel()), Box::new(b.cancel())),
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
      Alg::Pair(a, b) => write!(f, "{} {}", a, b),
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
    assert_eq!("Rw", parse_alg("Rw").unwrap().to_string());

    assert_eq!("[R, U]", parse_alg("[R,U]").unwrap().to_string());
    assert_eq!("[D: U]", parse_alg("[ D   :U ]").unwrap().to_string());
    assert_eq!(
      "[U, L] [R, U]",
      parse_alg("[U,   L][  R,U]").unwrap().to_string()
    );
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

    let pair = parse_alg("[D, L][R, U]").unwrap();
    assert_eq!(parse_alg("D L D' L' R U R' U'").unwrap(), pair.expand());
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

    let alg = parse_alg("[F, R] [R, U]").unwrap();
    assert_eq!(parse_alg("[U, R] [R, F]").unwrap(), alg.invert());
  }

  #[test]
  fn same_movement() {
    let m0 =
      Move::Face(Face::U, Amount::Single, Direction::Clockwise, Width::One);
    let m1 =
      Move::Face(Face::R, Amount::Single, Direction::Clockwise, Width::One);
    let m2 = Move::Face(
      Face::R,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    assert!(m0.is_same_movement(&m0));
    assert!(!m0.is_same_movement(&m1));
    assert!(!m1.is_same_movement(&m0));
    assert!(m1.is_same_movement(&m2));
  }

  #[test]
  fn cancel_move() {
    let m0 =
      Move::Face(Face::U, Amount::Single, Direction::Clockwise, Width::One);
    let m1 =
      Move::Face(Face::R, Amount::Single, Direction::Clockwise, Width::One);
    let m2 = Move::Face(
      Face::R,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    assert_eq!(
      Some(Some(Move::Face(
        Face::U,
        Amount::Double,
        Direction::Clockwise,
        Width::One
      ))),
      m0.cancel(&m0)
    );
    assert_eq!(None, m0.cancel(&m1));
    assert_eq!(None, m1.cancel(&m0));
    assert_eq!(Some(None), m1.cancel(&m2));
  }

  #[test]
  fn cancel_alg() {
    macro_rules! assert_cancel {
      ($expected: expr, $input: expr) => {
        assert_eq!(
          parse_alg($expected).unwrap(),
          parse_alg($input).unwrap().cancel()
        );
      };
    }

    assert_cancel!("R2", "R R");
    assert_cancel!("", "R R'");
    assert_cancel!("", "R2 R2");
    assert_cancel!("R2", "R U U' R");
    assert_cancel!("R2", "U U' R R");
    assert_cancel!("R'", "R R2");
    assert_cancel!("R'", "R R2'");
    assert_cancel!("R'", "R2 R");
    assert_cancel!("R'", "R2' R");
    assert_cancel!("[R2, U]", "[R R, U]");

    assert_eq!(
      parse_alg("R2' U R D R' U' R D' R").unwrap(),
      parse_alg("[R': [R' U R, D]]").unwrap().expand().cancel()
    );
  }
}
