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

  /// An [Iterator] over the oriented [EdgePos] variants in order.
  pub fn oriented_iter() -> impl Iterator<Item = EdgePos> {
    use EdgePos::*;
    static EDGES: [EdgePos; 12] =
      [UF, UL, UB, UR, DF, DL, DB, DR, FR, FL, BL, BR];
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

  pub fn orient(self) -> Self {
    match self {
      Self::UF => Self::UF,
      Self::FU => Self::UF,
      Self::UL => Self::UL,
      Self::LU => Self::UL,
      Self::UB => Self::UB,
      Self::BU => Self::UB,
      Self::UR => Self::UR,
      Self::RU => Self::UR,
      Self::DF => Self::DF,
      Self::FD => Self::DF,
      Self::DL => Self::DL,
      Self::LD => Self::DL,
      Self::DB => Self::DB,
      Self::BD => Self::DB,
      Self::DR => Self::DR,
      Self::RD => Self::DR,
      Self::FR => Self::FR,
      Self::RF => Self::FR,
      Self::FL => Self::FL,
      Self::LF => Self::FL,
      Self::BL => Self::BL,
      Self::LB => Self::BL,
      Self::BR => Self::BR,
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

impl From<EdgePos> for (Face, Face) {
  fn from(c: EdgePos) -> (Face, Face) {
    use Face::*;
    match c {
      EdgePos::UF => (U, F),
      EdgePos::FU => (F, U),
      EdgePos::UL => (U, L),
      EdgePos::LU => (L, U),
      EdgePos::UB => (U, B),
      EdgePos::BU => (B, U),
      EdgePos::UR => (U, R),
      EdgePos::RU => (R, U),
      EdgePos::DF => (D, F),
      EdgePos::FD => (F, D),
      EdgePos::DL => (D, L),
      EdgePos::LD => (L, D),
      EdgePos::DB => (D, B),
      EdgePos::BD => (B, D),
      EdgePos::DR => (D, R),
      EdgePos::RD => (R, D),
      EdgePos::FR => (F, R),
      EdgePos::RF => (R, F),
      EdgePos::FL => (F, L),
      EdgePos::LF => (L, F),
      EdgePos::BL => (B, L),
      EdgePos::LB => (L, B),
      EdgePos::BR => (B, R),
      EdgePos::RB => (R, B),
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

  #[test]
  fn exhaustive_edge_from() {
    for e0 in EdgePos::iter() {
      let (f0, f1) = e0.into();
      let e1 = EdgePos::try_from((f0, f1)).unwrap();
      assert_eq!(e1, e0);
    }
  }

  #[test]
  fn exhaustive_edge_orient() {
    for (e0, e1) in EdgePos::oriented_iter()
      .flat_map(|c| std::iter::repeat(c).take(2))
      .zip(EdgePos::iter())
    {
      assert_eq!(e0, e0.orient());
      assert_eq!(e0, e1.orient());
    }
  }
}
