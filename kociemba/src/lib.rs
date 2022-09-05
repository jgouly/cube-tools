mod piece_cube;

use piece_cube::PieceCube;

pub(crate) trait Coord {
  // Number of elements in `Coord`'s transition table.
  const NUM_ELEMS: usize;

  // Modify `Cube` to have the given coordinate.
  fn set_coord(cube: &mut PieceCube, coord: usize);

  // Get the coordinate for a given `Cube`.
  fn get_coord(cube: &PieceCube) -> usize;
}
