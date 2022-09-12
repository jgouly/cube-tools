use crate::ids::*;
use crate::{
  factorial, pruning_table::init_prune_table,
  transition_table::init_transition_table, Coord, PieceCube,
};
use cube::{CornerPos, EdgePos, Face, Move, StickerCube};

pub fn get_nth_zero(val: u8, n: u8) -> u8 {
  let mut val = val;
  for _ in 0..n {
    // makes the rightmost 0 bit a 1
    val |= val + 1;
  }

  (!val).trailing_zeros() as u8
}

struct FactorialDigits<I: Iterator<Item = usize>> {
  val: usize,
  len: usize,
  base_iter: I,
}

fn factorial_digits(
  val: usize,
  len: usize,
) -> FactorialDigits<impl Iterator<Item = usize>> {
  FactorialDigits {
    val,
    len,
    base_iter: (0..len).map(factorial).rev(),
  }
}

impl<I: Iterator<Item = usize>> Iterator for FactorialDigits<I> {
  type Item = usize;
  fn next(&mut self) -> Option<Self::Item> {
    if self.val == 0 && self.len == 0 {
      None
    } else {
      let base = self.base_iter.next().unwrap();
      let next = self.val / base;
      self.val %= base;

      if self.len > 0 {
        self.len -= 1;
      }

      Some(next)
    }
  }
}

fn set_perm_coord<P: Copy>(perm: &mut [P], coord: usize, a: Vec<P>) {
  let mut used_bits = 0u8;

  let digits = factorial_digits(coord, perm.len());
  for (i, n) in (0..perm.len()).rev().zip(digits) {
    let bit_n = get_nth_zero(used_bits, n as u8) as usize;

    used_bits |= 1 << bit_n;

    perm[i] = a[perm.len() - 1 - bit_n];
  }
}

// The number of inversions with regards to the element `i`.
fn num_inversions_of<P: PartialOrd>(perm: &[P], i: usize) -> usize {
  if perm.len() <= i {
    return 0;
  }

  let p = &perm[i];
  perm[..i].iter().filter(|&j| j > p).count()
}

// A `Iterator` over the number of inversions of each element
// of the permutation `perm`.
fn get_perm_inversions<'a, P: PartialOrd + 'a>(
  perm: &'a [P],
) -> impl Iterator<Item = usize> + 'a {
  (0..perm.len()).map(move |i| num_inversions_of(&perm, i))
}

fn get_perm_coord<P: PartialOrd>(perm: &[P]) -> usize {
  get_perm_inversions(perm)
    .zip((0..).map(factorial))
    .fold(0, |acc, (f, p)| acc + f * p)
}

// The G1 EP coordinate encodes the positions of the U and D edges.
pub(crate) struct EPCoord;

impl Coord for EPCoord {
  const NUM_ELEMS: usize = 40320; // 8!

  fn set_coord(cube: &mut PieceCube, ep: usize) {
    set_perm_coord(&mut cube.ep[0..8], ep, EdgePos::oriented_iter().collect());

    if !cube.is_valid() {
      // Swap two corners to fix parity.
      cube.cp.swap(0, 1);
    }

    debug_assert!(StickerCube::from(cube.clone()).is_valid());
  }

  fn get_coord(cube: &PieceCube) -> usize {
    get_perm_coord(&cube.ep[0..8])
  }
}

// The G1 CP coordinate encodes the positions of the corners.
pub(crate) struct CPCoord;

impl Coord for CPCoord {
  const NUM_ELEMS: usize = 40320; // 8!

  fn set_coord(cube: &mut PieceCube, cp: usize) {
    set_perm_coord(&mut cube.cp, cp, CornerPos::oriented_iter().collect());

    if !cube.is_valid() {
      // Swap two edges to fix parity.
      cube.ep.swap(0, 1);
    }

    debug_assert!(StickerCube::from(cube.clone()).is_valid());
  }

  fn get_coord(cube: &PieceCube) -> usize {
    get_perm_coord(&cube.cp)
  }
}

// The G1 UD2 coordinate encodes the positions of the E-slice edges.
pub(crate) struct UD2Coord;

impl Coord for UD2Coord {
  const NUM_ELEMS: usize = 24; // 4!

  fn set_coord(cube: &mut PieceCube, ud2: usize) {
    let mut edge_offsets = [EdgePos::FR, EdgePos::FL, EdgePos::BL, EdgePos::BR];
    set_perm_coord(
      &mut edge_offsets,
      ud2,
      vec![EdgePos::FR, EdgePos::FL, EdgePos::BL, EdgePos::BR],
    );

    cube.ep[8..12]
      .iter_mut()
      .zip(&edge_offsets)
      .for_each(|(e, &o)| *e = o);

    if !cube.is_valid() {
      // Swap two corners to fix parity.
      cube.cp.swap(0, 1);
    }

    debug_assert!(StickerCube::from(cube.clone()).is_valid());
  }

  fn get_coord(cube: &PieceCube) -> usize {
    get_perm_coord(&cube.ep[8..12])
  }
}

pub struct G1;

impl GroupIDS for G1 {
  type Tables = G1Tables;

  fn solution_check(_solution: &[Move]) -> bool {
    // All G1 solutions are valid.
    true
  }

  fn turn_counts(f: Face) -> core::ops::Range<usize> {
    if f != Face::U && f != Face::D {
      1..2
    } else {
      0..3
    }
  }
}

#[derive(Clone, Copy)]
pub struct G1Coord {
  ep: usize,
  cp: usize,
  ud2: usize,
}

impl GroupCoord for G1Coord {
  fn is_solved(&self) -> bool {
    self.ep == 0 && self.cp == 0 && self.ud2 == 0
  }
}

impl From<PieceCube> for G1Coord {
  fn from(val: PieceCube) -> G1Coord {
    G1Coord {
      ep: EPCoord::get_coord(&val),
      cp: CPCoord::get_coord(&val),
      ud2: UD2Coord::get_coord(&val),
    }
  }
}

pub struct G1Tables {
  ep_t: Vec<[usize; 6]>,
  cp_t: Vec<[usize; 6]>,
  ud2_t: Vec<[usize; 6]>,
  ep_p: Box<[usize]>,
  cp_p: Box<[usize]>,
  ud2_p: Box<[usize]>,
}

impl G1Tables {
  pub fn new() -> Self {
    let ep_t = init_transition_table::<EPCoord>(1);
    let cp_t = init_transition_table::<CPCoord>(1);
    let ud2_t = init_transition_table::<UD2Coord>(1);
    let ep_p = get_ep_prune_table(&ep_t);
    let cp_p = get_cp_prune_table(&cp_t);
    let ud2_p = get_ud2_prune_table(&ud2_t);

    G1Tables {
      ep_t,
      cp_t,
      ud2_t,
      ep_p,
      cp_p,
      ud2_p,
    }
  }
}

impl GroupTables for G1Tables {
  type Coord = G1Coord;

  // The new `G1Coord` after doing the `face` move.
  // note: This is a quarter turn for U/D and half turn for FBRL.
  fn transition(&self, coord: G1Coord, face: Face) -> G1Coord {
    let ep = self.ep_t[coord.ep][face as usize];
    let cp = self.cp_t[coord.cp][face as usize];
    let ud2 = self.ud2_t[coord.ud2][face as usize];
    G1Coord { ep, cp, ud2 }
  }

  fn prune_depth(&self, coord: G1Coord) -> usize {
    std::cmp::max(
      self.ep_p[coord.ep],
      std::cmp::max(self.cp_p[coord.cp], self.ud2_p[coord.ud2]),
    )
  }
}

// Get the G1 CP prune table.
fn get_cp_prune_table(cp_trans: &[[usize; 6]]) -> Box<[usize]> {
  init_prune_table(&cp_trans[..], 14, cp_trans.len())
}

// Get the G1 EP prune table.
fn get_ep_prune_table(ep_trans: &[[usize; 6]]) -> Box<[usize]> {
  init_prune_table(&ep_trans[..], 9, ep_trans.len())
}

// Get the G1 UD2 prune table.
fn get_ud2_prune_table(ud2_trans: &[[usize; 6]]) -> Box<[usize]> {
  init_prune_table(&ud2_trans[..], 5, ud2_trans.len())
}
