#![allow(dead_code)]

use cube::StickerCube;

mod subsets;

#[derive(Debug, PartialEq)]
struct State {
  cube: StickerCube,
}
