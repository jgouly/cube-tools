use crate::Face;
use std::convert::TryFrom;

/// Represents a particular corner position on a cube.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CornerPos {
  URF,
  RFU,
  FUR,
  UFL,
  FLU,
  LUF,
  ULB,
  LBU,
  BUL,
  UBR,
  BRU,
  RUB,
  DFR,
  FRD,
  RDF,
  DLF,
  LFD,
  FDL,
  DBL,
  BLD,
  LDB,
  DRB,
  RBD,
  BDR,
}

impl CornerPos {
  /// An [Iterator] over the [CornerPos] variants in order.
  pub fn iter() -> impl Iterator<Item = CornerPos> {
    use CornerPos::*;
    static CORNERS: [CornerPos; 24] = [
      URF, RFU, FUR, UFL, FLU, LUF, ULB, LBU, BUL, UBR, BRU, RUB, DFR, FRD,
      RDF, DLF, LFD, FDL, DBL, BLD, LDB, DRB, RBD, BDR,
    ];
    CORNERS.iter().copied()
  }

  /// The corner position clockwise.
  pub fn clockwise_pos(self) -> Self {
    let (a, b, c) = self.into();
    Self::try_from((b, c, a)).unwrap()
  }

  /// The corner position anti clockwise.
  pub fn anti_clockwise_pos(self) -> Self {
    let (a, b, c) = self.into();
    Self::try_from((c, a, b)).unwrap()
  }
}

impl TryFrom<(Face, Face, Face)> for CornerPos {
  type Error = ();

  fn try_from(faces: (Face, Face, Face)) -> Result<CornerPos, ()> {
    use Face::*;
    match faces {
      (U, R, F) => Ok(Self::URF),
      (R, F, U) => Ok(Self::RFU),
      (F, U, R) => Ok(Self::FUR),
      (U, F, L) => Ok(Self::UFL),
      (F, L, U) => Ok(Self::FLU),
      (L, U, F) => Ok(Self::LUF),
      (U, L, B) => Ok(Self::ULB),
      (L, B, U) => Ok(Self::LBU),
      (B, U, L) => Ok(Self::BUL),
      (U, B, R) => Ok(Self::UBR),
      (B, R, U) => Ok(Self::BRU),
      (R, U, B) => Ok(Self::RUB),
      (D, F, R) => Ok(Self::DFR),
      (F, R, D) => Ok(Self::FRD),
      (R, D, F) => Ok(Self::RDF),
      (D, L, F) => Ok(Self::DLF),
      (L, F, D) => Ok(Self::LFD),
      (F, D, L) => Ok(Self::FDL),
      (D, B, L) => Ok(Self::DBL),
      (B, L, D) => Ok(Self::BLD),
      (L, D, B) => Ok(Self::LDB),
      (D, R, B) => Ok(Self::DRB),
      (R, B, D) => Ok(Self::RBD),
      (B, D, R) => Ok(Self::BDR),
      _ => Err(()),
    }
  }
}

impl From<CornerPos> for (Face, Face, Face) {
  fn from(c: CornerPos) -> (Face, Face, Face) {
    use Face::*;
    match c {
      CornerPos::URF => (U, R, F),
      CornerPos::RFU => (R, F, U),
      CornerPos::FUR => (F, U, R),
      CornerPos::UFL => (U, F, L),
      CornerPos::FLU => (F, L, U),
      CornerPos::LUF => (L, U, F),
      CornerPos::ULB => (U, L, B),
      CornerPos::LBU => (L, B, U),
      CornerPos::BUL => (B, U, L),
      CornerPos::UBR => (U, B, R),
      CornerPos::BRU => (B, R, U),
      CornerPos::RUB => (R, U, B),
      CornerPos::DFR => (D, F, R),
      CornerPos::FRD => (F, R, D),
      CornerPos::RDF => (R, D, F),
      CornerPos::DLF => (D, L, F),
      CornerPos::LFD => (L, F, D),
      CornerPos::FDL => (F, D, L),
      CornerPos::DBL => (D, B, L),
      CornerPos::BLD => (B, L, D),
      CornerPos::LDB => (L, D, B),
      CornerPos::DRB => (D, R, B),
      CornerPos::RBD => (R, B, D),
      CornerPos::BDR => (B, D, R),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn corner_twists() {
    let corners = CornerPos::iter().collect::<Vec<_>>();
    let mut triplets = corners.chunks(3);
    while let Some([c0, c1, c2]) = triplets.next() {
      assert_eq!(*c1, c0.clockwise_pos());
      assert_eq!(*c2, c1.clockwise_pos());
      assert_eq!(*c0, c2.clockwise_pos());

      assert_eq!(*c2, c0.anti_clockwise_pos());
      assert_eq!(*c0, c1.anti_clockwise_pos());
      assert_eq!(*c1, c2.anti_clockwise_pos());
    }
  }

  #[test]
  fn exhaustive_corner_from() {
    for c0 in CornerPos::iter() {
      let (f0, f1, f2) = c0.into();
      let c1 = CornerPos::try_from((f0, f1, f2)).unwrap();
      assert_eq!(c1, c0);
    }
  }
}
