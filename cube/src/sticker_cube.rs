use crate::alg::{Amount, Direction, Move};
use crate::{CentrePos, CornerPos, EdgePos, Face};
use std::convert::TryFrom;
use std::ops::{Index, IndexMut};

/// Abstract stickers on a [StickerCube].
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sticker {
  S0,
  S1,
  S2,
  S3,
  S4,
  S5,
}

/// Represents a 3x3x3 cube by storing stickers.
///
/// This representation includes centre pieces so it can
/// represent slice turns and rotations.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct StickerCube {
  centres: [Sticker; 6],
  corners: [Sticker; 24],
  edges: [Sticker; 24],
}

impl StickerCube {
  /// Construct a solved [StickerCube].
  pub fn solved() -> Self {
    use Sticker::*;
    let edges = [
      S0, S2, S0, S5, S0, S4, S0, S1, S3, S2, S3, S5, S3, S4, S3, S1, S2, S1,
      S2, S5, S4, S5, S4, S1,
    ];
    let corners = [
      S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5, S2,
      S3, S4, S5, S3, S1, S4,
    ];
    Self {
      centres: [S0, S1, S2, S3, S4, S5],
      corners,
      edges,
    }
  }

  fn corners_solved(&self) -> bool {
    use CornerPos::*;
    let sticker_check = |pos: &[CornerPos], centre: CentrePos| {
      pos.iter().map(|&c| self[c]).all(|e| e == self[centre])
    };
    sticker_check(&[URF, UFL, ULB, UBR], CentrePos::U)
      && sticker_check(&[RFU, RUB, RBD, RDF], CentrePos::R)
      && sticker_check(&[FUR, FLU, FRD, FDL], CentrePos::F)
      && sticker_check(&[DFR, DLF, DBL, DRB], CentrePos::D)
      && sticker_check(&[BRU, BUL, BLD, BDR], CentrePos::B)
      && sticker_check(&[LUF, LBU, LDB, LFD], CentrePos::L)
  }

  fn edges_solved(&self) -> bool {
    use EdgePos::*;
    let sticker_check = |pos: &[EdgePos], centre: CentrePos| {
      pos.iter().map(|&c| self[c]).all(|e| e == self[centre])
    };
    sticker_check(&[UF, UL, UB, UR], CentrePos::U)
      && sticker_check(&[RU, RB, RD, RF], CentrePos::R)
      && sticker_check(&[FU, FR, FD, FL], CentrePos::F)
      && sticker_check(&[DF, DL, DB, DR], CentrePos::D)
      && sticker_check(&[BU, BL, BD, BR], CentrePos::B)
      && sticker_check(&[LU, LF, LD, LB], CentrePos::L)
  }

  /// Returns `true` if the cube is solved.
  pub fn is_solved(&self) -> bool {
    self.corners_solved() && self.edges_solved()
  }

  /// Returns the [CornerPos] at position `c`.
  pub fn corner(&self, c: CornerPos) -> CornerPos {
    let s0 = self[c];
    let s1 = self[c.clockwise_pos()];
    let s2 = self[c.anti_clockwise_pos()];
    let f0 = self.sticker_to_face(s0);
    let f1 = self.sticker_to_face(s1);
    let f2 = self.sticker_to_face(s2);
    CornerPos::try_from((f0, f1, f2)).unwrap()
  }

  /// Returns the [EdgePos] at position `e`.
  pub fn edge(&self, e: EdgePos) -> EdgePos {
    let s0 = self[e];
    let s1 = self[e.flip()];
    let f0 = self.sticker_to_face(s0);
    let f1 = self.sticker_to_face(s1);
    EdgePos::try_from((f0, f1)).unwrap()
  }

  fn sticker_to_face(&self, s: Sticker) -> Face {
    match s {
      _ if s == self[CentrePos::U] => Face::U,
      _ if s == self[CentrePos::R] => Face::R,
      _ if s == self[CentrePos::F] => Face::F,
      _ if s == self[CentrePos::D] => Face::D,
      _ if s == self[CentrePos::B] => Face::B,
      _ if s == self[CentrePos::L] => Face::L,
      _ => unreachable!("{:?}", s),
    }
  }

  /// Apply a move.
  pub fn do_move_mut(&mut self, m: Move) {
    match m {
      Move::Face(f, amt, dir) => {
        let amt = match (amt, dir) {
          (Amount::Single, Direction::Clockwise) => 1,
          (Amount::Single, Direction::AntiClockwise) => 3,
          (Amount::Double, _) => 2,
        };

        for _ in 0..amt {
          match f {
            Face::U => self.do_u(),
            Face::R => unimplemented!(),
            Face::F => unimplemented!(),
            Face::D => unimplemented!(),
            Face::B => unimplemented!(),
            Face::L => unimplemented!(),
          }
        }
      }
    }
  }

  fn do_u(&mut self) {
    use EdgePos::*;
    cycle4(UF, UL, UB, UR, self);
    cycle4(FU, LU, BU, RU, self);

    use CornerPos::*;
    cycle4(URF, UFL, ULB, UBR, self);
    cycle4(RFU, FLU, LBU, BRU, self);
    cycle4(FUR, LUF, BUL, RUB, self);
  }
}

fn cycle4<T>(p0: T, p1: T, p2: T, p3: T, cube: &mut StickerCube)
where
  T: Copy,
  StickerCube: IndexMut<T, Output = Sticker>,
{
  let op0 = cube[p0];
  let op1 = cube[p1];
  let op2 = cube[p2];
  let op3 = cube[p3];
  cube[p0] = op3;
  cube[p1] = op0;
  cube[p2] = op1;
  cube[p3] = op2;
}

macro_rules! pos_index {
  ($ty: ty, $field: ident) => {
    impl Index<$ty> for StickerCube {
      type Output = Sticker;

      fn index(&self, edge: $ty) -> &Self::Output {
        &self.$field[edge as usize]
      }
    }

    impl IndexMut<$ty> for StickerCube {
      fn index_mut(&mut self, edge: $ty) -> &mut Self::Output {
        &mut self.$field[edge as usize]
      }
    }
  };
}

pos_index!(EdgePos, edges);
pos_index!(CentrePos, centres);
pos_index!(CornerPos, corners);

#[cfg(test)]
mod tests {
  use super::*;
  use {CornerPos::*, EdgePos::*, Sticker::*};

  #[test]
  fn is_solved() {
    let c = StickerCube::solved();
    assert!(c.is_solved());
  }

  #[test]
  fn edge_lookup() {
    let c = StickerCube::solved();

    for e in EdgePos::iter() {
      assert_eq!(e, c.edge(e));
    }
  }

  #[test]
  fn corner_lookup() {
    let cu = StickerCube::solved();

    for c in CornerPos::iter() {
      assert_eq!(c, cu.corner(c));
    }
  }

  #[test]
  fn face_u() {
    let u = Move::Face(Face::U, Amount::Single, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(u);

    assert_eq!(UR, c.edge(UF));
    assert_eq!(UF, c.edge(UL));
    assert_eq!(UL, c.edge(UB));
    assert_eq!(UB, c.edge(UR));

    assert_eq!(UBR, c.corner(URF));
    assert_eq!(URF, c.corner(UFL));
    assert_eq!(UFL, c.corner(ULB));
    assert_eq!(ULB, c.corner(UBR));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S4, S1, S0, S1, S2, S0, S2, S5, S0, S5, S4, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S1, S0, S2, S0, S5, S0, S4, S3, S2, S3, S5, S3, S4, S3, S1, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_uprime() {
    let uprime = Move::Face(Face::U, Amount::Single, Direction::AntiClockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(uprime);

    assert_eq!(UL, c.edge(UF));
    assert_eq!(UB, c.edge(UL));
    assert_eq!(UR, c.edge(UB));
    assert_eq!(UF, c.edge(UR));

    assert_eq!(UFL, c.corner(URF));
    assert_eq!(ULB, c.corner(UFL));
    assert_eq!(UBR, c.corner(ULB));
    assert_eq!(URF, c.corner(UBR));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S2, S5, S0, S5, S4, S0, S4, S1, S0, S1, S2, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S5, S0, S4, S0, S1, S0, S2, S3, S2, S3, S5, S3, S4, S3, S1, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_u2() {
    let u2 = Move::Face(Face::U, Amount::Double, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(u2);

    assert_eq!(UB, c.edge(UF));
    assert_eq!(UR, c.edge(UL));
    assert_eq!(UF, c.edge(UB));
    assert_eq!(UL, c.edge(UR));

    assert_eq!(ULB, c.corner(URF));
    assert_eq!(UBR, c.corner(UFL));
    assert_eq!(URF, c.corner(ULB));
    assert_eq!(UFL, c.corner(UBR));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S5, S4, S0, S4, S1, S0, S1, S2, S0, S2, S5, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S4, S0, S1, S0, S2, S0, S5, S3, S2, S3, S5, S3, S4, S3, S1, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }
}
