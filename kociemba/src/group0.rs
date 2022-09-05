use crate::ids::*;
use crate::{
  factorial, pruning_table::init_prune_table,
  transition_table::init_transition_table, Coord, PieceCube,
};
use cube::{EdgePos, Face, Move, StickerCube};

// The G0 EO coordinate is an 11-bit number where each bit corresponds
// to the orientation of the edge at that index. The 12th edge's orientation
// is calculated based on the first 11 edge orientations.
pub(crate) struct EOCoord;

impl Coord for EOCoord {
  const NUM_ELEMS: usize = 2048; // 2 ^ 11

  fn set_coord(cube: &mut PieceCube, eo: usize) {
    assert!(eo < Self::NUM_ELEMS);

    let mut eo = eo;
    for i in (0..11).rev() {
      cube.eo[i] = (eo & 1) as u8;
      cube.eo[11] ^= (eo & 1) as u8;
      eo >>= 1;
    }

    debug_assert!(StickerCube::from(cube.clone()).is_valid());
  }

  fn get_coord(cube: &PieceCube) -> usize {
    cube.eo[..11]
      .iter()
      .fold(0, |acc, &cur| (acc | cur as usize) << 1)
      >> 1
  }
}

// The G0 CO coordinate is 7 digit base-3 number where each digit corresponds
// to the orientation of the corner at that index. The 8th corner's orientation
// is calculated based on the first 7 corner orientations.
pub(crate) struct COCoord;

impl Coord for COCoord {
  const NUM_ELEMS: usize = 2187; // 3 ^ 7

  fn set_coord(cube: &mut PieceCube, co: usize) {
    assert!(co < Self::NUM_ELEMS);

    let mut co = co;
    for i in (0..7).rev() {
      cube.co[i] = (co % 3) as u8;
      co /= 3;
      cube.co[7] = ((cube.co[7] + 3) - cube.co[i]) % 3;
    }

    debug_assert!(StickerCube::from(cube.clone()).is_valid());
  }

  fn get_coord(cube: &PieceCube) -> usize {
    cube.co[..7]
      .iter()
      .fold(0usize, |acc, &cur| (acc * 3) + (cur as usize))
  }
}

// The binomial coefficient: C(N, K).
fn choose(n: usize, k: usize) -> usize {
  factorial(n) / (factorial(k) * factorial(n - k))
}

// The G0 UD1 coordinate encodes the position of the four E-slice
// edges (FR, FL, BL, BR).
// The actual permutation of the slice edges is ignored.
pub(crate) struct UD1Coord;

impl Coord for UD1Coord {
  const NUM_ELEMS: usize = 495; // 12 choose 4

  // Setting the position of the E-slice edges based on the coordinate.
  //
  // Calculating the positions starts from position 11, and iterates
  // down to position 0. At every position (N) the binomial coefficient,
  // C(N, K), is calculated.
  // If C(N, K) is larger than the current coordinate, N is a slice edge and K
  // is reduced by 1.
  // If C(N, K) is less than or equal to the coordinate, the coordinate is
  // reduced by C(N, K).
  // K is initially 3 and is reduced by 1 for each slide edge at
  // a position > N. When K becomes negative, the coordinate processing is
  // calculation is complete.
  // This means that edges at a lower position than the 4th slice edge are
  // ignored.
  //
  // Example:
  //
  //   Coordinate = 321
  //
  //   N = 11, K = 3, Coord = 321, C(11, 3) = 165
  //   N = 10, K = 3, Coord = 156, C(10, 3) = 120
  //   N = 9, K = 3, Coord = 36, C(9, 3) = 84, 84 > 36, N is a slice edge
  //   N = 8, K = 2, Coord = 36, C(8, 2) = 28
  //   N = 7, K = 2, Coord = 8, C(7, 2) = 21, 21 > 8, N is a slice edge
  //   N = 6, K = 1, Coord = 8, C(6, 1) = 6
  //   N = 5, K = 1, Coord = 2, C(5, 1) = 6, 6 > 2, N is a slice edge
  //   N = 4, K = 0, Coord = 2, C(4, 0) = 1
  //   N = 3, K = 0, Coord = 1, C(3, 0) = 1
  //   N = 2, K = 0, Coord = 0, C(2, 0) = 1, 1 > 0, N is a slice edge
  //
  //   +---+---+---+---+---+---+---+---+---+---+----+----+
  //   | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
  //   +---+---+---+---+---+---+---+---+---+---+----+----+
  //   | - | - | X | - | - | X | - | X | - | X |  - |  - |
  //   +---+---+---+---+---+---+---+---+---+---+----+----+
  fn set_coord(cube: &mut PieceCube, coord: usize) {
    let mut coord = coord;
    let slice_edges = [EdgePos::FR, EdgePos::FL, EdgePos::BL, EdgePos::BR];
    let mut k = 3;

    cube.ep.copy_from_slice(&[EdgePos::UF; 12]);

    for i in (0..12).rev() {
      let binomial = choose(i, k);

      if binomial > coord {
        cube.ep[i] = slice_edges[k];
        if k == 0 {
          break;
        }
        k -= 1;
      } else {
        coord -= binomial;
      }
    }

    // Replace all `UR` edges with edges from the solved edge permutation.
    // note: This does not affect the coordinate, but creates a valid cube.
    let solved_ep = PieceCube::solved().ep;
    cube
      .ep
      .iter_mut()
      .filter(|&&mut e| e == EdgePos::UF)
      .zip(&solved_ep)
      .for_each(|(x, y)| *x = *y);

    if !cube.is_valid() {
      // Swap two corners to fix parity.
      cube.cp.swap(0, 1);
    }

    debug_assert!(StickerCube::from(cube.clone()).is_valid());
  }

  // The UD coordinate is calculated using binomial coefficients.
  //
  // Calculating the coordinate starts from position 11, and iterates
  // down to position 0. At every position (N) that is not a slice edge,
  // the binomial coefficient, C(N, K), is summed up to produce the final
  // coordinate. K is initially 3 and is reduced by 1 for each slide edge at
  // a position > N. When K becomes negative, the calculation is complete.
  // This means that edges at a lower position than the 4th slice edge are
  // ignored.
  //
  // Example:
  //
  //   +---+---+---+---+---+---+---+---+---+---+----+----+
  //   | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
  //   +---+---+---+---+---+---+---+---+---+---+----+----+
  //   | - | - | X | X | - | - | - | - | X | - | X  | -  |
  //   +---+---+---+---+---+---+---+---+---+---+----+----+
  //
  //   N = 11, K = 3, C(11, 3) = 165
  //   N = 10, K -= 1, Slice edge
  //   N = 9, K = 2, C(9, 2) = 36
  //   N = 8, K -= 1, Slice edge
  //   N = 7, K = 1, C(7, 1) = 7
  //   N = 6, K = 1, C(6, 1) = 6
  //   N = 5, K = 1, C(5, 1) = 5
  //   N = 4, K = 1, C(4, 1) = 4
  //   N = 3, K -= 1, Slice edge
  //   N = 2, K -= 1, Slice edge
  //
  //   Coordinate = 165 + 36 + 7 + 6 + 5 + 4 = 223
  fn get_coord(cube: &PieceCube) -> usize {
    let mut coord = 0;
    let mut k = 3;
    for i in (0..12).rev() {
      if cube.ep[i] < EdgePos::FR {
        coord += choose(i, k);
      } else {
        if k == 0 {
          break;
        }
        k -= 1;
      }
    }

    coord
  }
}

// Get the G0 CO prune table.
fn get_co_prune_table(co_trans: &[[usize; 6]]) -> Box<[usize]> {
  init_prune_table(&co_trans[..], 7, co_trans.len())
}

// Get the G0 EO prune table.
fn get_eo_prune_table(eo_trans: &[[usize; 6]]) -> Box<[usize]> {
  init_prune_table(&eo_trans[..], 8, eo_trans.len())
}

// Get the G0 UD1 prune table.
fn get_ud1_prune_table(ud1_trans: &[[usize; 6]]) -> Box<[usize]> {
  init_prune_table(&ud1_trans[..], 6, ud1_trans.len())
}

pub struct G0;

impl GroupIDS for G0 {
  type Tables = G0Tables;

  fn solution_check(solution: &[Move]) -> bool {
    // Phase0 cannot end in U or D.
    if solution
      .last()
      .map(|m| m.face() == Face::U || m.face() == Face::D)
      .unwrap_or(false)
    {
      return false;
    }

    // Phase0 cannot end a half turn.
    if solution.last().map(|m| m.is_half_turn()).unwrap_or(false) {
      return false;
    }

    let len = solution.len();
    if len > 1 {
      let m1 = &solution[len - 2];
      let m2 = &solution[len - 1];

      // Phase 0 cannot end in A2 B, where A and B are opposite faces.
      if m1.face().is_opposite(m2.face()) && m1.is_half_turn() {
        return false;
      }
    }

    true
  }

  fn turn_counts(_f: Face) -> core::ops::Range<usize> {
    0..3
  }
}

#[derive(Clone, Copy)]
pub struct G0Coord {
  eo: usize,
  co: usize,
  ud1: usize,
}

impl GroupCoord for G0Coord {
  fn is_solved(&self) -> bool {
    self.eo == 0 && self.co == 0 && self.ud1 == 0
  }
}

impl From<PieceCube> for G0Coord {
  fn from(val: PieceCube) -> G0Coord {
    G0Coord {
      eo: EOCoord::get_coord(&val),
      co: COCoord::get_coord(&val),
      ud1: UD1Coord::get_coord(&val),
    }
  }
}

pub struct G0Tables {
  pub eo_t: Vec<[usize; 6]>,
  pub co_t: Vec<[usize; 6]>,
  pub ud1_t: Vec<[usize; 6]>,
  pub eo_p: Box<[usize]>,
  pub co_p: Box<[usize]>,
  pub ud1_p: Box<[usize]>,
}

impl GroupTables for G0Tables {
  type Coord = G0Coord;

  // The new `G0Coord` after doing the `face` move.
  // note: This only does quarter turns.
  fn transition(&self, coord: G0Coord, face: Face) -> G0Coord {
    let eo = self.eo_t[coord.eo][face as usize];
    let co = self.co_t[coord.co][face as usize];
    let ud1 = self.ud1_t[coord.ud1][face as usize];
    G0Coord { eo, co, ud1 }
  }

  fn prune_depth(&self, coord: G0Coord) -> usize {
    std::cmp::max(
      self.eo_p[coord.eo],
      std::cmp::max(self.co_p[coord.co], self.ud1_p[coord.ud1]),
    )
  }
}
