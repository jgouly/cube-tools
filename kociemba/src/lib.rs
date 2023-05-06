mod group0;
mod group1;
mod ids;
mod piece_cube;
mod pruning_table;
mod transition_table;

use piece_cube::PieceCube;

pub(crate) trait Coord {
  // Number of elements in `Coord`'s transition table.
  const NUM_ELEMS: usize;

  // Modify `Cube` to have the given coordinate.
  fn set_coord(cube: &mut PieceCube, coord: usize);

  // Get the coordinate for a given `Cube`.
  fn get_coord(cube: &PieceCube) -> usize;
}

pub(crate) fn factorial(n: usize) -> usize {
  (1..n + 1).product()
}

pub struct Kociemba {
  g0: group0::G0Tables,
  g1: group1::G1Tables,
}

impl Kociemba {
  pub fn new() -> Self {
    Kociemba {
      g0: group0::G0Tables::new(),
      g1: group1::G1Tables::new(),
    }
  }

  pub fn solve(&self, c: cube::StickerCube) -> cube::Alg {
    let mut c: PieceCube = c.into();

    let mut g0 = vec![];
    for i in 0.. {
      g0.clear();
      if !ids::ids::<group0::G0>(c.into(), i, &self.g0, &mut g0) {
        continue;
      }
      break;
    }

    for m in g0.clone().into_iter() {
      c = c.do_move(m);
    }

    let mut solution = g0;

    let mut g1 = vec![];
    for i in 0.. {
      g1.clear();
      if !ids::ids::<group1::G1>(c.into(), i, &self.g1, &mut g1) {
        continue;
      }
      break;
    }

    solution.extend(g1);
    cube::Alg::from(solution).cancel()
  }
}
