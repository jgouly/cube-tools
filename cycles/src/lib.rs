use cube::StickerCube;
use cube::{CornerPos, EdgePos};

pub trait Piece: PartialEq + Copy {
  fn oriented_iter() -> Box<dyn Iterator<Item = Self>>;
  fn lookup(cube: &StickerCube, p: Self) -> Self;
  fn set(cube: &mut StickerCube, p0: Self, p1: Self);
  fn orient(&self) -> Self;
  fn rotate(&self) -> Self;
  fn num_rotations(&self) -> usize;
  fn solved(cube: &StickerCube) -> bool;
}

impl Piece for EdgePos {
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

pub fn get_piece_cycles<T: Piece>(c: &StickerCube) -> Vec<Vec<T>> {
  let mut unsolved = Vec::with_capacity(12);
  let mut cycles = vec![];

  for p in T::oriented_iter() {
    if T::lookup(c, p) != p {
      unsolved.push(p);
    }
  }

  while unsolved.len() > 0 {
    let mut cur_cycle = vec![];
    let buffer = unsolved[0];
    cur_cycle.push(buffer);

    let mut current_piece = buffer;

    loop {
      current_piece = T::lookup(c, current_piece);

      unsolved.remove(
        unsolved
          .iter()
          .position(|p| p == &current_piece.orient())
          .unwrap(),
      );

      // The buffer is solved, end of the current cycle.
      if current_piece == buffer {
        break;
      }

      cur_cycle.push(current_piece);

      // The buffer is in place but flipped, end of the current cycle.
      if current_piece.orient() == buffer {
        break;
      }
    }

    cycles.push(cur_cycle);
  }

  cycles
}

pub fn cycle_len<P: Piece>(cycle: &[P]) -> usize {
  assert!(!cycle.is_empty());
  let offset = if Some(cycle[0].orient()) == cycle.last().map(|p| p.orient()) {
    1
  } else {
    0
  };
  cycle.len() - offset
}

#[cfg(test)]
mod tests {
  use super::*;
  use cube::parse_alg;
  use cube::{CornerPos::*, EdgePos::*};

  #[test]
  fn edge_cycles() {
    let c = StickerCube::solved();
    let cycles = get_piece_cycles::<EdgePos>(&c);
    assert_eq!(Vec::<Vec<EdgePos>>::new(), cycles);

    macro_rules! test_alg_cycles {
      ($alg: expr, $edge_cycles: expr, $corner_cycles: expr) => {
        let alg = parse_alg($alg).unwrap();

        let mut c = StickerCube::solved();
        for m in alg.iter() {
          c.do_move_mut(m);
        }

        let cycles = get_piece_cycles::<EdgePos>(&c);
        assert_eq!($edge_cycles, cycles);

        let cycles = get_piece_cycles::<CornerPos>(&c);
        assert_eq!($corner_cycles, cycles);
      };
    }

    test_alg_cycles!(
      "R2 U R U R' U' R' U' R' U R'",
      vec![vec![UF, UR, UL]],
      Vec::<Vec<CornerPos>>::new()
    );
    test_alg_cycles!(
      "R",
      vec![vec![UR, FR, DR, BR]],
      vec![vec![URF, FRD, DRB, BRU]]
    );
    test_alg_cycles!(
      "R2",
      vec![vec![UR, DR], vec![FR, BR]],
      vec![vec![URF, DRB], vec![UBR, DFR]]
    );
    test_alg_cycles!(
      "R' U2 R2 U R' U' R' U2 L F R F' L'",
      vec![vec![UF, FU], vec![UR, RU]],
      Vec::<Vec<CornerPos>>::new()
    );
    test_alg_cycles!(
      "R U R' U' R' F R2 U' R' U' R U R' F'",
      vec![vec![UL, UR]],
      vec![vec![URF, UBR]]
    );
  }

  #[test]
  fn test_len() {
    assert_eq!(1, cycle_len(&[UF, FU]));
    assert_eq!(2, cycle_len(&[UF, UL]));
    assert_eq!(3, cycle_len(&[UF, UL, UR]));
    assert_eq!(3, cycle_len(&[UF, UL, UR, FU]));

    assert_eq!(1, cycle_len(&[URF, FUR]));
    assert_eq!(2, cycle_len(&[URF, UFL]));
    assert_eq!(3, cycle_len(&[URF, UFL, ULB]));
    assert_eq!(3, cycle_len(&[URF, UFL, ULB, FUR]));
  }

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
}
