use cube::{CornerPos, Piece, StickerCube};
use rand::{
  seq::{IteratorRandom, SliceRandom},
  Rng,
};

fn filter<'a, P: Piece + PartialEq>(
  p: impl Iterator<Item = P> + 'a,
  f: &'a [P],
) -> impl Iterator<Item = P> + 'a {
  p.filter(|&p| !f.iter().any(|p1| p.orient() == p1.orient()))
}

fn pieces_from<const N: usize, P: Piece + PartialEq>(
  rng: &mut (impl Rng + ?Sized),
  pieces: impl Iterator<Item = P>,
) -> [P; N] {
  let mut pieces = pieces.collect::<Vec<_>>();

  pieces.shuffle(rng);

  (&pieces[0..N]).try_into().unwrap()
}

fn pieces<const N: usize, P: Piece + PartialEq + std::fmt::Debug>(
  rng: &mut (impl Rng + ?Sized),
  buf: P,
) -> [P; N] {
  pieces_from(rng, filter(P::oriented_iter(), &[buf]))
}

pub fn random_3twist(
  rng: &mut (impl Rng + ?Sized),
  buffer: CornerPos,
) -> StickerCube {
  let [c0, c1] = pieces(rng, buffer);

  let rotate = if rng.gen() {
    CornerPos::clockwise_pos
  } else {
    CornerPos::anti_clockwise_pos
  };

  let mut c = StickerCube::solved();
  c.set_corner(buffer, rotate(buffer));
  c.set_corner(c0, rotate(c0));
  c.set_corner(c1, rotate(c1));

  assert!(c.is_valid());

  c
}

pub fn random_floating_3twist(rng: &mut (impl Rng + ?Sized)) -> StickerCube {
  let buffer = CornerPos::oriented_iter().choose(rng).unwrap();
  random_3twist(rng, buffer)
}
