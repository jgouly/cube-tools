use crate::alg::{Amount, Direction, Move, Width};
use crate::{CentrePos, CornerPos, EdgePos, Face, Slice};
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
#[derive(Clone, Debug)]
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

  pub fn set_corner(&mut self, e0: CornerPos, e1: CornerPos) {
    let (f0, f1, f2) = e1.into();
    self[e0] = self.face_to_sticker(f0);
    self[e0.clockwise_pos()] = self.face_to_sticker(f1);
    self[e0.anti_clockwise_pos()] = self.face_to_sticker(f2);
  }

  /// Returns the [EdgePos] at position `e`.
  pub fn edge(&self, e: EdgePos) -> EdgePos {
    let s0 = self[e];
    let s1 = self[e.flip()];
    let f0 = self.sticker_to_face(s0);
    let f1 = self.sticker_to_face(s1);
    EdgePos::try_from((f0, f1)).unwrap()
  }

  pub fn set_edge(&mut self, e0: EdgePos, e1: EdgePos) {
    let (f0, f1) = e1.into();
    self[e0] = self.face_to_sticker(f0);
    self[e0.flip()] = self.face_to_sticker(f1);
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

  fn face_to_sticker(&self, f: Face) -> Sticker {
    match f {
      Face::U => self[CentrePos::U],
      Face::R => self[CentrePos::R],
      Face::F => self[CentrePos::F],
      Face::D => self[CentrePos::D],
      Face::B => self[CentrePos::B],
      Face::L => self[CentrePos::L],
    }
  }

  /// Apply a move.
  pub fn do_move_mut(&mut self, m: Move) {
    match m {
      Move::Face(f, amt, dir, width) => {
        let amt = match (amt, dir) {
          (Amount::Single, Direction::Clockwise) => 1,
          (Amount::Single, Direction::AntiClockwise) => 3,
          (Amount::Double, _) => 2,
        };

        for _ in 0..amt {
          match (f, width) {
            (Face::U, Width::One) => self.do_u(),
            (Face::U, Width::Two) => self.do_uw(),
            (Face::R, Width::One) => self.do_r(),
            (Face::R, Width::Two) => self.do_rw(),
            (Face::F, Width::One) => self.do_f(),
            (Face::F, Width::Two) => self.do_fw(),
            (Face::D, Width::One) => self.do_d(),
            (Face::D, Width::Two) => self.do_dw(),
            (Face::B, Width::One) => self.do_b(),
            (Face::B, Width::Two) => self.do_bw(),
            (Face::L, Width::One) => self.do_l(),
            (Face::L, Width::Two) => self.do_lw(),
          }
        }
      }

      Move::Slice(s, amt, dir) => {
        let amt = match (amt, dir) {
          (Amount::Single, Direction::Clockwise) => 1,
          (Amount::Single, Direction::AntiClockwise) => 3,
          (Amount::Double, _) => 2,
        };

        for _ in 0..amt {
          match s {
            Slice::E => self.do_e(),
            Slice::M => self.do_m(),
            Slice::S => self.do_s(),
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

  fn do_r(&mut self) {
    use EdgePos::*;
    cycle4(UR, BR, DR, FR, self);
    cycle4(RU, RB, RD, RF, self);

    use CornerPos::*;
    cycle4(URF, BRU, DRB, FRD, self);
    cycle4(RFU, RUB, RBD, RDF, self);
    cycle4(FUR, UBR, BDR, DFR, self);
  }

  fn do_f(&mut self) {
    use EdgePos::*;
    cycle4(UF, RF, DF, LF, self);
    cycle4(FU, FR, FD, FL, self);

    use CornerPos::*;
    cycle4(URF, RDF, DLF, LUF, self);
    cycle4(RFU, DFR, LFD, UFL, self);
    cycle4(FUR, FRD, FDL, FLU, self);
  }

  fn do_d(&mut self) {
    use EdgePos::*;
    cycle4(DF, DR, DB, DL, self);
    cycle4(FD, RD, BD, LD, self);

    use CornerPos::*;
    cycle4(DFR, DRB, DBL, DLF, self);
    cycle4(FRD, RBD, BLD, LFD, self);
    cycle4(RDF, BDR, LDB, FDL, self);
  }

  fn do_b(&mut self) {
    use EdgePos::*;
    cycle4(UB, LB, DB, RB, self);
    cycle4(BU, BL, BD, BR, self);

    use CornerPos::*;
    cycle4(UBR, LBU, DBL, RBD, self);
    cycle4(BRU, BUL, BLD, BDR, self);
    cycle4(RUB, ULB, LDB, DRB, self);
  }

  fn do_l(&mut self) {
    use EdgePos::*;
    cycle4(UL, FL, DL, BL, self);
    cycle4(LU, LF, LD, LB, self);

    use CornerPos::*;
    cycle4(UFL, FDL, DBL, BUL, self);
    cycle4(FLU, DLF, BLD, ULB, self);
    cycle4(LUF, LFD, LDB, LBU, self);
  }

  fn do_e(&mut self) {
    use EdgePos::*;
    cycle4(FR, RB, BL, LF, self);
    cycle4(RF, BR, LB, FL, self);

    use CentrePos::*;
    cycle4(F, R, B, L, self);
  }

  fn do_m(&mut self) {
    use EdgePos::*;
    cycle4(UF, FD, DB, BU, self);
    cycle4(FU, DF, BD, UB, self);

    use CentrePos::*;
    cycle4(U, F, D, B, self);
  }

  fn do_s(&mut self) {
    use EdgePos::*;
    cycle4(UR, RD, DL, LU, self);
    cycle4(RU, DR, LD, UL, self);

    use CentrePos::*;
    cycle4(U, R, D, L, self);
  }

  fn do_uw(&mut self) {
    self.do_u();
    self.do_e();
    self.do_e();
    self.do_e();
  }

  fn do_rw(&mut self) {
    self.do_r();
    self.do_m();
    self.do_m();
    self.do_m();
  }

  fn do_fw(&mut self) {
    self.do_f();
    self.do_s();
  }

  fn do_dw(&mut self) {
    self.do_d();
    self.do_e();
  }

  fn do_bw(&mut self) {
    self.do_b();
    self.do_s();
    self.do_s();
    self.do_s();
  }

  fn do_lw(&mut self) {
    self.do_l();
    self.do_m();
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
  fn piece_set() {
    {
      let mut c = StickerCube::solved();
      c.set_corner(URF, UBR);
      assert_eq!(UBR, c.corner(URF));

      c.set_corner(URF, RFU);
      assert_eq!(RFU, c.corner(URF));
    }

    {
      let mut c = StickerCube::solved();
      c.set_edge(UF, UB);
      assert_eq!(UB, c.edge(UF));

      c.set_edge(UF, FU);
      assert_eq!(FU, c.edge(UF));
    }
  }

  #[test]
  fn face_u() {
    let u =
      Move::Face(Face::U, Amount::Single, Direction::Clockwise, Width::One);
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
    let uprime = Move::Face(
      Face::U,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
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
    let u2 =
      Move::Face(Face::U, Amount::Double, Direction::Clockwise, Width::One);
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

  #[test]
  fn face_r() {
    let r =
      Move::Face(Face::R, Amount::Single, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(r);

    assert_eq!(FR, c.edge(UR));
    assert_eq!(DR, c.edge(FR));
    assert_eq!(BR, c.edge(DR));
    assert_eq!(UR, c.edge(BR));

    assert_eq!(FRD, c.corner(URF));
    assert_eq!(BDR, c.corner(DFR));
    assert_eq!(BRU, c.corner(DRB));
    assert_eq!(FUR, c.corner(UBR));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S2, S1, S3, S0, S2, S5, S0, S5, S4, S2, S0, S1, S4, S3, S1, S3, S5,
          S2, S3, S4, S5, S4, S1, S0
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S2, S1, S3, S2, S3, S5, S3, S4, S4, S1, S3,
          S1, S2, S5, S4, S5, S0, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_rprime() {
    let rprime = Move::Face(
      Face::R,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    let mut c = StickerCube::solved();
    c.do_move_mut(rprime);

    assert_eq!(BR, c.edge(UR));
    assert_eq!(UR, c.edge(FR));
    assert_eq!(FR, c.edge(DR));
    assert_eq!(DR, c.edge(BR));

    assert_eq!(BRU, c.corner(URF));
    assert_eq!(FUR, c.corner(DFR));
    assert_eq!(FRD, c.corner(DRB));
    assert_eq!(BDR, c.corner(UBR));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S4, S1, S0, S0, S2, S5, S0, S5, S4, S4, S3, S1, S2, S0, S1, S3, S5,
          S2, S3, S4, S5, S2, S1, S3
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S4, S1, S3, S2, S3, S5, S3, S4, S2, S1, S0,
          S1, S2, S5, S4, S5, S3, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_r2() {
    let r2 =
      Move::Face(Face::R, Amount::Double, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(r2);

    assert_eq!(DR, c.edge(UR));
    assert_eq!(BR, c.edge(FR));
    assert_eq!(UR, c.edge(DR));
    assert_eq!(FR, c.edge(BR));

    assert_eq!(DRB, c.corner(URF));
    assert_eq!(UBR, c.corner(DFR));
    assert_eq!(URF, c.corner(DRB));
    assert_eq!(DFR, c.corner(UBR));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S3, S1, S4, S0, S2, S5, S0, S5, S4, S3, S2, S1, S0, S4, S1, S3, S5,
          S2, S3, S4, S5, S0, S1, S2
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S3, S1, S3, S2, S3, S5, S3, S4, S0, S1, S4,
          S1, S2, S5, S4, S5, S2, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_f() {
    let f =
      Move::Face(Face::F, Amount::Single, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(f);

    assert_eq!(LF, c.edge(UF));
    assert_eq!(UF, c.edge(RF));
    assert_eq!(RF, c.edge(DF));
    assert_eq!(DF, c.edge(LF));

    assert_eq!(LUF, c.corner(URF));
    assert_eq!(URF, c.corner(RDF));
    assert_eq!(RDF, c.corner(DLF));
    assert_eq!(DLF, c.corner(LUF));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S5, S0, S2, S5, S2, S3, S0, S5, S4, S0, S4, S1, S1, S2, S0, S1, S3,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S5, S2, S0, S5, S0, S4, S0, S1, S1, S2, S3, S5, S3, S4, S3, S1, S2,
          S0, S2, S3, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_fprime() {
    let fprime = Move::Face(
      Face::F,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    let mut c = StickerCube::solved();
    c.do_move_mut(fprime);

    assert_eq!(RF, c.edge(UF));
    assert_eq!(DF, c.edge(RF));
    assert_eq!(LF, c.edge(DF));
    assert_eq!(UF, c.edge(LF));

    assert_eq!(RDF, c.corner(URF));
    assert_eq!(DLF, c.corner(RDF));
    assert_eq!(LUF, c.corner(DLF));
    assert_eq!(URF, c.corner(LUF));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S1, S3, S2, S1, S2, S0, S0, S5, S4, S0, S4, S1, S5, S2, S3, S5, S0,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S1, S2, S0, S5, S0, S4, S0, S1, S5, S2, S3, S5, S3, S4, S3, S1, S2,
          S3, S2, S0, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_f2() {
    let f2 =
      Move::Face(Face::F, Amount::Double, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(f2);

    assert_eq!(DF, c.edge(UF));
    assert_eq!(LF, c.edge(RF));
    assert_eq!(UF, c.edge(DF));
    assert_eq!(RF, c.edge(LF));

    assert_eq!(DLF, c.corner(URF));
    assert_eq!(UFL, c.corner(DFR));
    assert_eq!(URF, c.corner(DLF));
    assert_eq!(DFR, c.corner(UFL));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S3, S5, S2, S3, S2, S1, S0, S5, S4, S0, S4, S1, S0, S2, S5, S0, S1,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S3, S2, S0, S5, S0, S4, S0, S1, S0, S2, S3, S5, S3, S4, S3, S1, S2,
          S5, S2, S1, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_d() {
    let d =
      Move::Face(Face::D, Amount::Single, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(d);

    assert_eq!(DL, c.edge(DF));
    assert_eq!(DB, c.edge(DL));
    assert_eq!(DR, c.edge(DB));
    assert_eq!(DF, c.edge(DR));

    assert_eq!(DLF, c.corner(DFR));
    assert_eq!(DBL, c.corner(DLF));
    assert_eq!(DRB, c.corner(DBL));
    assert_eq!(DFR, c.corner(DRB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S5, S2, S3, S4,
          S5, S3, S1, S4, S3, S2, S1
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S0, S1, S3, S5, S3, S4, S3, S1, S3, S2, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_dprime() {
    let dprime = Move::Face(
      Face::D,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    let mut c = StickerCube::solved();
    c.do_move_mut(dprime);

    assert_eq!(DR, c.edge(DF));
    assert_eq!(DF, c.edge(DL));
    assert_eq!(DL, c.edge(DB));
    assert_eq!(DB, c.edge(DR));

    assert_eq!(DRB, c.corner(DFR));
    assert_eq!(DFR, c.corner(DLF));
    assert_eq!(DLF, c.corner(DBL));
    assert_eq!(DBL, c.corner(DRB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S1, S4, S3, S2,
          S1, S3, S5, S2, S3, S4, S5
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S0, S1, S3, S1, S3, S2, S3, S5, S3, S4, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_d2() {
    let d2 =
      Move::Face(Face::D, Amount::Double, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(d2);

    assert_eq!(DB, c.edge(DF));
    assert_eq!(DR, c.edge(DL));
    assert_eq!(DF, c.edge(DB));
    assert_eq!(DL, c.edge(DR));

    assert_eq!(DBL, c.corner(DFR));
    assert_eq!(DRB, c.corner(DLF));
    assert_eq!(DFR, c.corner(DBL));
    assert_eq!(DLF, c.corner(DRB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S4, S5, S3, S1,
          S4, S3, S2, S1, S3, S5, S2
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S0, S1, S3, S4, S3, S1, S3, S2, S3, S5, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_b() {
    let b =
      Move::Face(Face::B, Amount::Single, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(b);

    assert_eq!(RB, c.edge(UB));
    assert_eq!(UB, c.edge(LB));
    assert_eq!(LB, c.edge(DB));
    assert_eq!(DB, c.edge(RB));

    assert_eq!(RBD, c.corner(UBR));
    assert_eq!(UBR, c.corner(LBU));
    assert_eq!(LBU, c.corner(DBL));
    assert_eq!(DBL, c.corner(RBD));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S1, S0, S4, S1, S4, S3, S3, S2, S1, S3, S5,
          S2, S5, S4, S0, S5, S3, S4
        ],
        edges: [
          S0, S2, S0, S5, S1, S4, S0, S1, S3, S2, S3, S5, S5, S4, S3, S1, S2,
          S1, S2, S5, S4, S0, S4, S3
        ]
      },
      c
    );
  }

  #[test]
  fn face_bprime() {
    let bprime = Move::Face(
      Face::B,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    let mut c = StickerCube::solved();
    c.do_move_mut(bprime);

    assert_eq!(LB, c.edge(UB));
    assert_eq!(DB, c.edge(LB));
    assert_eq!(RB, c.edge(DB));
    assert_eq!(UB, c.edge(RB));

    assert_eq!(LBU, c.corner(UBR));
    assert_eq!(DBL, c.corner(LBU));
    assert_eq!(RBD, c.corner(DBL));
    assert_eq!(UBR, c.corner(RBD));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S5, S3, S4, S5, S4, S0, S3, S2, S1, S3, S5,
          S2, S1, S4, S3, S1, S0, S4
        ],
        edges: [
          S0, S2, S0, S5, S5, S4, S0, S1, S3, S2, S3, S5, S1, S4, S3, S1, S2,
          S1, S2, S5, S4, S3, S4, S0
        ]
      },
      c
    );
  }

  #[test]
  fn face_b2() {
    let b2 =
      Move::Face(Face::B, Amount::Double, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(b2);

    assert_eq!(DB, c.edge(UB));
    assert_eq!(RB, c.edge(LB));
    assert_eq!(UB, c.edge(DB));
    assert_eq!(LB, c.edge(RB));

    assert_eq!(DBL, c.corner(UBR));
    assert_eq!(DRB, c.corner(ULB));
    assert_eq!(UBR, c.corner(DBL));
    assert_eq!(ULB, c.corner(DRB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S3, S1, S4, S3, S4, S5, S3, S2, S1, S3, S5,
          S2, S0, S4, S1, S0, S5, S4
        ],
        edges: [
          S0, S2, S0, S5, S3, S4, S0, S1, S3, S2, S3, S5, S0, S4, S3, S1, S2,
          S1, S2, S5, S4, S1, S4, S5
        ]
      },
      c
    );
  }

  #[test]
  fn face_l() {
    let l =
      Move::Face(Face::L, Amount::Single, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(l);

    assert_eq!(BL, c.edge(UL));
    assert_eq!(UL, c.edge(FL));
    assert_eq!(FL, c.edge(DL));
    assert_eq!(DL, c.edge(BL));

    assert_eq!(BUL, c.corner(UFL));
    assert_eq!(FLU, c.corner(DLF));
    assert_eq!(FDL, c.corner(DBL));
    assert_eq!(BLD, c.corner(ULB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S4, S0, S5, S4, S5, S3, S0, S4, S1, S3, S2, S1, S2, S5,
          S0, S2, S3, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S4, S5, S0, S4, S0, S1, S3, S2, S2, S5, S3, S4, S3, S1, S2,
          S1, S0, S5, S3, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_lprime() {
    let lprime = Move::Face(
      Face::L,
      Amount::Single,
      Direction::AntiClockwise,
      Width::One,
    );
    let mut c = StickerCube::solved();
    c.do_move_mut(lprime);

    assert_eq!(FL, c.edge(UL));
    assert_eq!(DL, c.edge(FL));
    assert_eq!(BL, c.edge(DL));
    assert_eq!(UL, c.edge(BL));

    assert_eq!(FDL, c.corner(UFL));
    assert_eq!(BLD, c.corner(DLF));
    assert_eq!(BUL, c.corner(DBL));
    assert_eq!(FLU, c.corner(ULB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S2, S3, S5, S2, S5, S0, S0, S4, S1, S3, S2, S1, S4, S5,
          S3, S4, S0, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S2, S5, S0, S4, S0, S1, S3, S2, S4, S5, S3, S4, S3, S1, S2,
          S1, S3, S5, S0, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn face_l2() {
    let l2 =
      Move::Face(Face::L, Amount::Double, Direction::Clockwise, Width::One);
    let mut c = StickerCube::solved();
    c.do_move_mut(l2);

    assert_eq!(DL, c.edge(UL));
    assert_eq!(BL, c.edge(FL));
    assert_eq!(UL, c.edge(DL));
    assert_eq!(FL, c.edge(BL));

    assert_eq!(DBL, c.corner(UFL));
    assert_eq!(ULB, c.corner(DLF));
    assert_eq!(UFL, c.corner(DBL));
    assert_eq!(DLF, c.corner(ULB));

    assert_eq!(
      StickerCube {
        centres: [S0, S1, S2, S3, S4, S5],
        corners: [
          S0, S1, S2, S3, S4, S5, S3, S5, S2, S0, S4, S1, S3, S2, S1, S0, S5,
          S4, S0, S2, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S3, S5, S0, S4, S0, S1, S3, S2, S0, S5, S3, S4, S3, S1, S2,
          S1, S4, S5, S2, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn slice_e() {
    let e = Move::Slice(Slice::E, Amount::Single, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(e);

    assert_eq!(FR, c.edge(FR));
    assert_eq!(FL, c.edge(FL));
    assert_eq!(BL, c.edge(BL));
    assert_eq!(BR, c.edge(BR));

    assert_eq!(UR, c.edge(UF));
    assert_eq!(UF, c.edge(UL));
    assert_eq!(UL, c.edge(UB));
    assert_eq!(UB, c.edge(UR));

    assert_eq!(
      StickerCube {
        centres: [S0, S2, S5, S3, S1, S4],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S0, S1, S3, S2, S3, S5, S3, S4, S3, S1, S5,
          S2, S5, S4, S1, S4, S1, S2
        ]
      },
      c
    );
  }

  #[test]
  fn slice_eprime() {
    let eprime =
      Move::Slice(Slice::E, Amount::Single, Direction::AntiClockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(eprime);

    assert_eq!(FR, c.edge(FR));
    assert_eq!(FL, c.edge(FL));
    assert_eq!(BL, c.edge(BL));
    assert_eq!(BR, c.edge(BR));

    assert_eq!(UL, c.edge(UF));
    assert_eq!(UB, c.edge(UL));
    assert_eq!(UR, c.edge(UB));
    assert_eq!(UF, c.edge(UR));

    assert_eq!(
      StickerCube {
        centres: [S0, S4, S1, S3, S5, S2],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S0, S1, S3, S2, S3, S5, S3, S4, S3, S1, S1,
          S4, S1, S2, S5, S2, S5, S4
        ]
      },
      c
    );
  }

  #[test]
  fn slice_e2() {
    let e2 = Move::Slice(Slice::E, Amount::Double, Direction::AntiClockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(e2);

    assert_eq!(FR, c.edge(FR));
    assert_eq!(FL, c.edge(FL));
    assert_eq!(BL, c.edge(BL));
    assert_eq!(BR, c.edge(BR));

    assert_eq!(UB, c.edge(UF));
    assert_eq!(UR, c.edge(UL));
    assert_eq!(UF, c.edge(UB));
    assert_eq!(UL, c.edge(UR));

    assert_eq!(
      StickerCube {
        centres: [S0, S5, S4, S3, S2, S1],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S0, S5, S0, S4, S0, S1, S3, S2, S3, S5, S3, S4, S3, S1, S4,
          S5, S4, S1, S2, S1, S2, S5
        ]
      },
      c
    );
  }

  #[test]
  fn slice_m() {
    let m = Move::Slice(Slice::M, Amount::Single, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(m);

    assert_eq!(UF, c.edge(UF));
    assert_eq!(DF, c.edge(DF));
    assert_eq!(DB, c.edge(DB));
    assert_eq!(UB, c.edge(UB));

    assert_eq!(FL, c.edge(UL));
    assert_eq!(FR, c.edge(UR));
    assert_eq!(BL, c.edge(DL));
    assert_eq!(BR, c.edge(DR));

    assert_eq!(
      StickerCube {
        centres: [S4, S1, S0, S2, S3, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S4, S0, S0, S5, S4, S3, S0, S1, S2, S0, S3, S5, S2, S3, S3, S1, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn slice_mprime() {
    let mprime =
      Move::Slice(Slice::M, Amount::Single, Direction::AntiClockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(mprime);

    assert_eq!(UF, c.edge(UF));
    assert_eq!(DF, c.edge(DF));
    assert_eq!(DB, c.edge(DB));
    assert_eq!(UB, c.edge(UB));

    assert_eq!(BL, c.edge(UL));
    assert_eq!(BR, c.edge(UR));
    assert_eq!(FL, c.edge(DL));
    assert_eq!(FR, c.edge(DR));

    assert_eq!(
      StickerCube {
        centres: [S2, S1, S3, S4, S0, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S2, S3, S0, S5, S2, S0, S0, S1, S4, S3, S3, S5, S4, S0, S3, S1, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn slice_m2() {
    let m2 = Move::Slice(Slice::M, Amount::Double, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(m2);

    assert_eq!(UF, c.edge(UF));
    assert_eq!(DF, c.edge(DF));
    assert_eq!(DB, c.edge(DB));
    assert_eq!(UB, c.edge(UB));

    assert_eq!(DL, c.edge(UL));
    assert_eq!(DR, c.edge(UR));
    assert_eq!(UL, c.edge(DL));
    assert_eq!(UR, c.edge(DR));

    assert_eq!(
      StickerCube {
        centres: [S3, S1, S4, S0, S2, S5],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S3, S4, S0, S5, S3, S2, S0, S1, S0, S4, S3, S5, S0, S2, S3, S1, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn slice_s() {
    let s = Move::Slice(Slice::S, Amount::Single, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(s);

    assert_eq!(UR, c.edge(UR));
    assert_eq!(DR, c.edge(DR));
    assert_eq!(DL, c.edge(DL));
    assert_eq!(UL, c.edge(UL));

    assert_eq!(RF, c.edge(UF));
    assert_eq!(RB, c.edge(UB));
    assert_eq!(LF, c.edge(DF));
    assert_eq!(LB, c.edge(DB));

    assert_eq!(
      StickerCube {
        centres: [S5, S0, S2, S1, S4, S3],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S5, S3, S0, S4, S5, S0, S3, S2, S1, S3, S3, S4, S1, S0, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn slice_sprime() {
    let sprime =
      Move::Slice(Slice::S, Amount::Single, Direction::AntiClockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(sprime);

    assert_eq!(UR, c.edge(UR));
    assert_eq!(DR, c.edge(DR));
    assert_eq!(DL, c.edge(DL));
    assert_eq!(UL, c.edge(UL));

    assert_eq!(LF, c.edge(UF));
    assert_eq!(LB, c.edge(UB));
    assert_eq!(RF, c.edge(DF));
    assert_eq!(RB, c.edge(DB));

    assert_eq!(
      StickerCube {
        centres: [S1, S3, S2, S5, S4, S0],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S1, S0, S0, S4, S1, S3, S3, S2, S5, S0, S3, S4, S5, S3, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  #[test]
  fn slice_s2() {
    let s2 = Move::Slice(Slice::S, Amount::Double, Direction::Clockwise);
    let mut c = StickerCube::solved();
    c.do_move_mut(s2);

    assert_eq!(UR, c.edge(UR));
    assert_eq!(DR, c.edge(DR));
    assert_eq!(DL, c.edge(DL));
    assert_eq!(UL, c.edge(UL));

    assert_eq!(DF, c.edge(UF));
    assert_eq!(DB, c.edge(UB));
    assert_eq!(UF, c.edge(DF));
    assert_eq!(UB, c.edge(DB));

    assert_eq!(
      StickerCube {
        centres: [S3, S5, S2, S0, S4, S1],
        corners: [
          S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S2, S1, S3, S5,
          S2, S3, S4, S5, S3, S1, S4
        ],
        edges: [
          S0, S2, S3, S1, S0, S4, S3, S5, S3, S2, S0, S1, S3, S4, S0, S5, S2,
          S1, S2, S5, S4, S5, S4, S1
        ]
      },
      c
    );
  }

  macro_rules! wide_move_test {
    ($test_name: ident, $face: expr, $cw_cube: expr, $anti_cw_cube: expr, $double_cube: expr) => {
      #[test]
      fn $test_name() {
        let clockwise =
          Move::Face($face, Amount::Single, Direction::Clockwise, Width::Two);
        let mut c = StickerCube::solved();
        c.do_move_mut(clockwise);

        assert_eq!($cw_cube, c);

        let anti_clockwise = Move::Face(
          $face,
          Amount::Single,
          Direction::AntiClockwise,
          Width::Two,
        );
        let mut c = StickerCube::solved();
        c.do_move_mut(anti_clockwise);

        assert_eq!($anti_cw_cube, c);

        let double =
          Move::Face($face, Amount::Double, Direction::Clockwise, Width::Two);
        let mut c = StickerCube::solved();
        c.do_move_mut(double);

        assert_eq!($double_cube, c);
      }
    };
  }

  wide_move_test!(
    wide_u,
    Face::U,
    StickerCube {
      centres: [S0, S4, S1, S3, S5, S2],
      corners: [
        S0, S4, S1, S0, S1, S2, S0, S2, S5, S0, S5, S4, S3, S2, S1, S3, S5, S2,
        S3, S4, S5, S3, S1, S4
      ],
      edges: [
        S0, S1, S0, S2, S0, S5, S0, S4, S3, S2, S3, S5, S3, S4, S3, S1, S1, S4,
        S1, S2, S5, S2, S5, S4
      ]
    },
    StickerCube {
      centres: [S0, S2, S5, S3, S1, S4],
      corners: [
        S0, S2, S5, S0, S5, S4, S0, S4, S1, S0, S1, S2, S3, S2, S1, S3, S5, S2,
        S3, S4, S5, S3, S1, S4
      ],
      edges: [
        S0, S5, S0, S4, S0, S1, S0, S2, S3, S2, S3, S5, S3, S4, S3, S1, S5, S2,
        S5, S4, S1, S4, S1, S2
      ]
    },
    StickerCube {
      centres: [S0, S5, S4, S3, S2, S1],
      corners: [
        S0, S5, S4, S0, S4, S1, S0, S1, S2, S0, S2, S5, S3, S2, S1, S3, S5, S2,
        S3, S4, S5, S3, S1, S4
      ],
      edges: [
        S0, S4, S0, S1, S0, S2, S0, S5, S3, S2, S3, S5, S3, S4, S3, S1, S4, S5,
        S4, S1, S2, S1, S2, S5
      ]
    }
  );

  wide_move_test!(
    wide_r,
    Face::R,
    StickerCube {
      centres: [S2, S1, S3, S4, S0, S5],
      corners: [
        S2, S1, S3, S0, S2, S5, S0, S5, S4, S2, S0, S1, S4, S3, S1, S3, S5, S2,
        S3, S4, S5, S4, S1, S0
      ],
      edges: [
        S2, S3, S0, S5, S2, S0, S2, S1, S4, S3, S3, S5, S4, S0, S4, S1, S3, S1,
        S2, S5, S4, S5, S0, S1
      ]
    },
    StickerCube {
      centres: [S4, S1, S0, S2, S3, S5],
      corners: [
        S4, S1, S0, S0, S2, S5, S0, S5, S4, S4, S3, S1, S2, S0, S1, S3, S5, S2,
        S3, S4, S5, S2, S1, S3
      ],
      edges: [
        S4, S0, S0, S5, S4, S3, S4, S1, S2, S0, S3, S5, S2, S3, S2, S1, S0, S1,
        S2, S5, S4, S5, S3, S1
      ]
    },
    StickerCube {
      centres: [S3, S1, S4, S0, S2, S5],
      corners: [
        S3, S1, S4, S0, S2, S5, S0, S5, S4, S3, S2, S1, S0, S4, S1, S3, S5, S2,
        S3, S4, S5, S0, S1, S2
      ],
      edges: [
        S3, S4, S0, S5, S3, S2, S3, S1, S0, S4, S3, S5, S0, S2, S0, S1, S4, S1,
        S2, S5, S4, S5, S2, S1
      ]
    }
  );

  wide_move_test!(
    wide_f,
    Face::F,
    StickerCube {
      centres: [S5, S0, S2, S1, S4, S3],
      corners: [
        S5, S0, S2, S5, S2, S3, S0, S5, S4, S0, S4, S1, S1, S2, S0, S1, S3, S2,
        S3, S4, S5, S3, S1, S4
      ],
      edges: [
        S5, S2, S5, S3, S0, S4, S5, S0, S1, S2, S1, S3, S3, S4, S1, S0, S2, S0,
        S2, S3, S4, S5, S4, S1
      ]
    },
    StickerCube {
      centres: [S1, S3, S2, S5, S4, S0],
      corners: [
        S1, S3, S2, S1, S2, S0, S0, S5, S4, S0, S4, S1, S5, S2, S3, S5, S0, S2,
        S3, S4, S5, S3, S1, S4
      ],
      edges: [
        S1, S2, S1, S0, S0, S4, S1, S3, S5, S2, S5, S0, S3, S4, S5, S3, S2, S3,
        S2, S0, S4, S5, S4, S1
      ]
    },
    StickerCube {
      centres: [S3, S5, S2, S0, S4, S1],
      corners: [
        S3, S5, S2, S3, S2, S1, S0, S5, S4, S0, S4, S1, S0, S2, S5, S0, S1, S2,
        S3, S4, S5, S3, S1, S4
      ],
      edges: [
        S3, S2, S3, S1, S0, S4, S3, S5, S0, S2, S0, S1, S3, S4, S0, S5, S2, S5,
        S2, S1, S4, S5, S4, S1
      ]
    }
  );

  wide_move_test!(
    wide_d,
    Face::D,
    StickerCube {
      centres: [S0, S2, S5, S3, S1, S4],
      corners: [
        S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S5, S2, S3, S4, S5,
        S3, S1, S4, S3, S2, S1
      ],
      edges: [
        S0, S2, S0, S5, S0, S4, S0, S1, S3, S5, S3, S4, S3, S1, S3, S2, S5, S2,
        S5, S4, S1, S4, S1, S2
      ]
    },
    StickerCube {
      centres: [S0, S4, S1, S3, S5, S2],
      corners: [
        S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S1, S4, S3, S2, S1,
        S3, S5, S2, S3, S4, S5
      ],
      edges: [
        S0, S2, S0, S5, S0, S4, S0, S1, S3, S1, S3, S2, S3, S5, S3, S4, S1, S4,
        S1, S2, S5, S2, S5, S4
      ]
    },
    StickerCube {
      centres: [S0, S5, S4, S3, S2, S1],
      corners: [
        S0, S1, S2, S0, S2, S5, S0, S5, S4, S0, S4, S1, S3, S4, S5, S3, S1, S4,
        S3, S2, S1, S3, S5, S2
      ],
      edges: [
        S0, S2, S0, S5, S0, S4, S0, S1, S3, S4, S3, S1, S3, S2, S3, S5, S4, S5,
        S4, S1, S2, S1, S2, S5
      ]
    }
  );

  wide_move_test!(
    wide_b,
    Face::B,
    StickerCube {
      centres: [S1, S3, S2, S5, S4, S0],
      corners: [
        S0, S1, S2, S0, S2, S5, S1, S0, S4, S1, S4, S3, S3, S2, S1, S3, S5, S2,
        S5, S4, S0, S5, S3, S4
      ],
      edges: [
        S0, S2, S1, S0, S1, S4, S1, S3, S3, S2, S5, S0, S5, S4, S5, S3, S2, S1,
        S2, S5, S4, S0, S4, S3
      ]
    },
    StickerCube {
      centres: [S5, S0, S2, S1, S4, S3],
      corners: [
        S0, S1, S2, S0, S2, S5, S5, S3, S4, S5, S4, S0, S3, S2, S1, S3, S5, S2,
        S1, S4, S3, S1, S0, S4
      ],
      edges: [
        S0, S2, S5, S3, S5, S4, S5, S0, S3, S2, S1, S3, S1, S4, S1, S0, S2, S1,
        S2, S5, S4, S3, S4, S0
      ]
    },
    StickerCube {
      centres: [S3, S5, S2, S0, S4, S1],
      corners: [
        S0, S1, S2, S0, S2, S5, S3, S1, S4, S3, S4, S5, S3, S2, S1, S3, S5, S2,
        S0, S4, S1, S0, S5, S4
      ],
      edges: [
        S0, S2, S3, S1, S3, S4, S3, S5, S3, S2, S0, S1, S0, S4, S0, S5, S2, S1,
        S2, S5, S4, S1, S4, S5
      ]
    }
  );

  wide_move_test!(
    wide_l,
    Face::L,
    StickerCube {
      centres: [S4, S1, S0, S2, S3, S5],
      corners: [
        S0, S1, S2, S4, S0, S5, S4, S5, S3, S0, S4, S1, S3, S2, S1, S2, S5, S0,
        S2, S3, S5, S3, S1, S4
      ],
      edges: [
        S4, S0, S4, S5, S4, S3, S0, S1, S2, S0, S2, S5, S2, S3, S3, S1, S2, S1,
        S0, S5, S3, S5, S4, S1
      ]
    },
    StickerCube {
      centres: [S2, S1, S3, S4, S0, S5],
      corners: [
        S0, S1, S2, S2, S3, S5, S2, S5, S0, S0, S4, S1, S3, S2, S1, S4, S5, S3,
        S4, S0, S5, S3, S1, S4
      ],
      edges: [
        S2, S3, S2, S5, S2, S0, S0, S1, S4, S3, S4, S5, S4, S0, S3, S1, S2, S1,
        S3, S5, S0, S5, S4, S1
      ]
    },
    StickerCube {
      centres: [S3, S1, S4, S0, S2, S5],
      corners: [
        S0, S1, S2, S3, S4, S5, S3, S5, S2, S0, S4, S1, S3, S2, S1, S0, S5, S4,
        S0, S2, S5, S3, S1, S4
      ],
      edges: [
        S3, S4, S3, S5, S3, S2, S0, S1, S0, S4, S0, S5, S0, S2, S3, S1, S2, S1,
        S4, S5, S2, S5, S4, S1
      ]
    }
  );
}
