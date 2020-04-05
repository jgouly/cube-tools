use crate::StickerCube;
use crate::{CornerPos, EdgePos};

pub trait Piece: PartialEq + Copy {
  const NUM_ORIENTATIONS: usize;
  fn oriented_iter() -> Box<dyn Iterator<Item = Self>>;
  fn lookup(cube: &StickerCube, p: Self) -> Self;
  fn set(cube: &mut StickerCube, p0: Self, p1: Self);
  fn orient(&self) -> Self;
  fn rotate(&self) -> Self;
  fn num_rotations(&self) -> usize;
  fn solved(cube: &StickerCube) -> bool;
}

impl Piece for EdgePos {
  const NUM_ORIENTATIONS: usize = 2;

  fn oriented_iter() -> Box<dyn Iterator<Item = Self>> {
    Box::new(Self::oriented_iter())
  }

  fn lookup(cube: &StickerCube, p: Self) -> Self {
    cube.edge(p)
  }

  fn set(cube: &mut StickerCube, p0: Self, p1: Self) {
    cube.set_edge(p0, p1)
  }

  fn orient(&self) -> Self {
    (*self).orient()
  }

  fn rotate(&self) -> Self {
    self.flip()
  }

  fn num_rotations(&self) -> usize {
    if self == &self.orient() {
      0
    } else {
      1
    }
  }

  fn solved(cube: &StickerCube) -> bool {
    cube.edges_solved()
  }
}

impl Piece for CornerPos {
  const NUM_ORIENTATIONS: usize = 3;

  fn oriented_iter() -> Box<dyn Iterator<Item = Self>> {
    Box::new(Self::oriented_iter())
  }

  fn lookup(cube: &StickerCube, p: Self) -> Self {
    cube.corner(p)
  }

  fn set(cube: &mut StickerCube, p0: Self, p1: Self) {
    cube.set_corner(p0, p1)
  }

  fn orient(&self) -> Self {
    (*self).orient()
  }

  fn rotate(&self) -> Self {
    self.anti_clockwise_pos()
  }

  fn num_rotations(&self) -> usize {
    if self == &self.orient() {
      0
    } else if self.anti_clockwise_pos() == self.orient() {
      1
    } else {
      assert_eq!(self.clockwise_pos(), self.orient());
      2
    }
  }

  fn solved(cube: &StickerCube) -> bool {
    cube.corners_solved()
  }
}
#[cfg(test)]
mod tests {
  use super::*;
  use crate::{CornerPos::*, EdgePos::*};

  #[test]
  fn piece_rotations() {
    assert_eq!(FUR, URF.rotate());
    assert_eq!(URF, RFU.rotate());

    assert_eq!(FU, UF.rotate());

    assert_eq!(0, URF.num_rotations());
    assert_eq!(1, RFU.num_rotations());
    assert_eq!(2, FUR.num_rotations());

    assert_eq!(0, UR.num_rotations());
    assert_eq!(1, LB.num_rotations());
  }

  #[test]
  fn test_num_orientations() {
    let mut e = EdgePos::UF;
    for _ in 0..EdgePos::NUM_ORIENTATIONS {
      e = e.rotate();
    }
    assert_eq!(EdgePos::UF, e);

    let mut c = CornerPos::URF;
    for _ in 0..CornerPos::NUM_ORIENTATIONS {
      c = c.rotate();
    }
    assert_eq!(CornerPos::URF, c);
  }
}
