use crate::{CentrePos, CornerPos, EdgePos, Face};
use std::convert::TryFrom;
use std::ops::Index;

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
}

macro_rules! pos_index {
  ($ty: ty, $field: ident) => {
    impl Index<$ty> for StickerCube {
      type Output = Sticker;

      fn index(&self, edge: $ty) -> &Self::Output {
        &self.$field[edge as usize]
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
}
