mod alg;
mod corner_pos;
mod edge_pos;
mod sticker_cube;

pub use corner_pos::CornerPos;
pub use edge_pos::EdgePos;
pub use sticker_cube::StickerCube;

/// Represents a face of a cube.
#[derive(Clone, Copy, Debug)]
pub enum Face {
  U,
  R,
  F,
  D,
  B,
  L,
}

/// Represents a particular centre position on a cube.
#[derive(Clone, Copy, Debug)]
enum CentrePos {
  U,
  R,
  F,
  D,
  B,
  L,
}
