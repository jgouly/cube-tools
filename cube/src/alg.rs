use crate::Face;

/// The amount of a move.
#[derive(Clone, Debug)]
pub enum Amount {
  Single,
  Double,
}

/// The direction of a move.
#[derive(Clone, Debug)]
pub enum Direction {
  Clockwise,
  AntiClockwise,
}

/// Represents a move of the cube.
#[derive(Clone, Debug)]
pub enum Move {
  Face(Face, Amount, Direction),
}
