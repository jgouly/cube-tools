mod group0;
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
