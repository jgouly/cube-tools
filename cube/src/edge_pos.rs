use crate::Face;
use std::convert::TryFrom;

/// Represents a particular edge position on a cube.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EdgePos {
  UF,
  FU,
  UL,
  LU,
  UB,
  BU,
  UR,
  RU,
  DF,
  FD,
  DL,
  LD,
  DB,
  BD,
  DR,
  RD,
  FR,
  RF,
  FL,
  LF,
  BL,
  LB,
  BR,
  RB,
}

impl EdgePos {
  /// An [Iterator] over the [EdgePos] variants in order.
  pub fn iter() -> impl Iterator<Item = EdgePos> {
    use EdgePos::*;
    static EDGES: [EdgePos; 24] = [
      UF, FU, UL, LU, UB, BU, UR, RU, DF, FD, DL, LD, DB, BD, DR, RD, FR, RF,
      FL, LF, BL, LB, BR, RB,
    ];
    EDGES.iter().copied()
  }

  pub fn flip(self) -> Self {
    match self {
      Self::UF => Self::FU,
      Self::FU => Self::UF,
      Self::UL => Self::LU,
      Self::LU => Self::UL,
      Self::UB => Self::BU,
      Self::BU => Self::UB,
      Self::UR => Self::RU,
      Self::RU => Self::UR,
      Self::DF => Self::FD,
      Self::FD => Self::DF,
      Self::DL => Self::LD,
      Self::LD => Self::DL,
      Self::DB => Self::BD,
      Self::BD => Self::DB,
      Self::DR => Self::RD,
      Self::RD => Self::DR,
      Self::FR => Self::RF,
      Self::RF => Self::FR,
      Self::FL => Self::LF,
      Self::LF => Self::FL,
      Self::BL => Self::LB,
      Self::LB => Self::BL,
      Self::BR => Self::RB,
      Self::RB => Self::BR,
    }
  }
}

impl TryFrom<(Face, Face)> for EdgePos {
  type Error = ();

  fn try_from(faces: (Face, Face)) -> Result<Self, Self::Error> {
    use Face::*;
    match faces {
      (U, F) => Ok(Self::UF),
      (F, U) => Ok(Self::FU),
      (U, L) => Ok(Self::UL),
      (L, U) => Ok(Self::LU),
      (U, B) => Ok(Self::UB),
      (B, U) => Ok(Self::BU),
      (U, R) => Ok(Self::UR),
      (R, U) => Ok(Self::RU),
      (D, F) => Ok(Self::DF),
      (F, D) => Ok(Self::FD),
      (D, L) => Ok(Self::DL),
      (L, D) => Ok(Self::LD),
      (D, B) => Ok(Self::DB),
      (B, D) => Ok(Self::BD),
      (D, R) => Ok(Self::DR),
      (R, D) => Ok(Self::RD),
      (F, R) => Ok(Self::FR),
      (R, F) => Ok(Self::RF),
      (F, L) => Ok(Self::FL),
      (L, F) => Ok(Self::LF),
      (B, L) => Ok(Self::BL),
      (L, B) => Ok(Self::LB),
      (B, R) => Ok(Self::BR),
      (R, B) => Ok(Self::RB),
      _ => Err(()),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn edge_flips() {
    let edges = EdgePos::iter().collect::<Vec<_>>();
    let mut pairs = edges.chunks(2);
    while let Some([e0, e1]) = pairs.next() {
      assert_eq!(*e1, e0.flip());
      assert_eq!(*e0, e1.flip());
    }
  }

  #[test]
  fn try_from() {
    assert_eq!(Ok(EdgePos::UF), EdgePos::try_from((Face::U, Face::F)));
    assert_eq!(Ok(EdgePos::FU), EdgePos::try_from((Face::F, Face::U)));
    assert_eq!(Err(()), EdgePos::try_from((Face::U, Face::U)));
    assert_eq!(Err(()), EdgePos::try_from((Face::D, Face::U)));
  }
}
