use std::convert::TryFrom;

mod alg;
mod corner_pos;
mod edge_pos;
mod piece;
mod random_state;
mod sticker_cube;

pub use alg::{parse_alg, Alg, Move};
pub use corner_pos::CornerPos;
pub use edge_pos::EdgePos;
pub use piece::Piece;
pub use random_state::*;
pub use sticker_cube::StickerCube;

/// Represents a face of a cube.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Face {
  U,
  R,
  F,
  D,
  B,
  L,
}

impl Face {
  pub fn is_opposite(self, f: Face) -> bool {
    match (self, f) {
      (Face::U, Face::D) | (Face::D, Face::U) => true,
      (Face::R, Face::L) | (Face::L, Face::R) => true,
      (Face::F, Face::B) | (Face::B, Face::F) => true,
      _ => false,
    }
  }
}

impl TryFrom<char> for Face {
  type Error = ();

  fn try_from(c: char) -> Result<Self, Self::Error> {
    match c {
      'U' => Ok(Face::U),
      'R' => Ok(Face::R),
      'F' => Ok(Face::F),
      'D' => Ok(Face::D),
      'B' => Ok(Face::B),
      'L' => Ok(Face::L),
      _ => Err(()),
    }
  }
}

/// Represents a slice of a cube.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Slice {
  E,
  M,
  S,
}

impl TryFrom<char> for Slice {
  type Error = ();

  fn try_from(c: char) -> Result<Self, Self::Error> {
    match c {
      'E' => Ok(Slice::E),
      'M' => Ok(Slice::M),
      'S' => Ok(Slice::S),
      _ => Err(()),
    }
  }
}

/// Represents a particular centre position on a cube.
#[derive(Clone, Copy, Debug)]
enum CentrePos {
  U,
  R,
  F,
  D,
  B,
  L,
}

fn num_inversions<P: PartialOrd>(perm: &[P]) -> usize {
  let mut num = 0;
  for i in 0..perm.len() - 1 {
    for j in i + 1..perm.len() {
      if perm[i] > perm[j] {
        num += 1;
      }
    }
  }
  num
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_num_inversions() {
    assert_eq!(0, num_inversions(&[0, 1, 2, 3, 4, 5]));
    assert_eq!(1, num_inversions(&[0, 1, 3, 2, 4, 5]));
    assert_eq!(2, num_inversions(&[0, 1, 4, 2, 3, 5]));
  }
}
