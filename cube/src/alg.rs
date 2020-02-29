use crate::Face;

mod parser;
pub use parser::parse_alg;

/// The amount of a move.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Amount {
  Single,
  Double,
}

/// The direction of a move.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Direction {
  Clockwise,
  AntiClockwise,
}

/// Represents a move of the cube.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum Move {
  Face(Face, Amount, Direction),
}
