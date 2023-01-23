use cube::{CornerPos, EdgePos, Piece, StickerCube};
use rand::{
  seq::{IteratorRandom, SliceRandom},
  Rng,
};

fn rotate(r: u8, c: CornerPos) -> CornerPos {
  match r % 3 {
    0 => c,
    1 => c.clockwise_pos(),
    2 => c.anti_clockwise_pos(),
    _ => unreachable!(),
  }
}

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

pub fn random_2c2c(
  rng: &mut (impl Rng + ?Sized),
  buffer: CornerPos,
) -> StickerCube {
  let [c0, c1, c2] =
    pieces_from(rng, filter(CornerPos::oriented_iter(), &[buffer]));
  let corners = [buffer, c0, c1, c2];

  let twists: [u8; 3] = [
    rng.gen_range(0..3),
    rng.gen_range(0..3),
    rng.gen_range(0..3),
  ];

  let last_twist = 3 - (twists.iter().sum::<u8>() % 3);

  let mut c = StickerCube::solved();
  c.set_corner(corners[0], rotate(twists[0], corners[1]));
  c.set_corner(corners[1], rotate(twists[1], corners[0]));
  c.set_corner(corners[2], rotate(twists[2], corners[3]));
  c.set_corner(corners[3], rotate(last_twist, corners[2]));

  assert!(c.is_valid());

  c
}

pub fn random_floating_2c2c(rng: &mut (impl Rng + ?Sized)) -> StickerCube {
  let buffer = CornerPos::oriented_iter().choose(rng).unwrap();
  random_2c2c(rng, buffer)
}

pub fn random_2e2e(
  rng: &mut (impl Rng + ?Sized),
  buffer: EdgePos,
) -> StickerCube {
  let [e0, e1, e2] = pieces(rng, buffer);
  let edges = [buffer, e0, e1, e2];

  let flips: [bool; 3] = [rng.gen(), rng.gen(), rng.gen()];
  let last_flip = flips.iter().fold(false, |f, r| f ^ r);

  let flip = |f, e: EdgePos| if f { e.flip() } else { e };

  let mut c = StickerCube::solved();
  c.set_edge(edges[0], flip(flips[0], edges[1]));
  c.set_edge(edges[1], flip(flips[1], edges[0]));
  c.set_edge(edges[2], flip(flips[2], edges[3]));
  c.set_edge(edges[3], flip(last_flip, edges[2]));

  assert!(c.is_valid());

  c
}

pub fn random_ltct_with_target(
  rng: &mut (impl Rng + ?Sized),
  target: &[CornerPos],
) -> StickerCube {
  let buffer = CornerPos::URF;

  let [c0, c1] = if let Some(&c0) = target.choose(rng) {
    let [c1] =
      pieces_from(rng, filter(CornerPos::oriented_iter(), &[buffer, c0]));
    [c0, c1]
  } else {
    let [c0, c1] = pieces(rng, buffer);
    let c0 = rotate(rng.gen_range(0..3), c0);
    [c0, c1]
  };

  let c1 = rotate(rng.gen_range(0..3), c1);

  let (r1, r2): (fn(CornerPos) -> CornerPos, fn(CornerPos) -> CornerPos) =
    if rng.gen() {
      (CornerPos::clockwise_pos, CornerPos::anti_clockwise_pos)
    } else {
      (CornerPos::anti_clockwise_pos, CornerPos::clockwise_pos)
    };

  let mut c = StickerCube::solved();
  c.set_edge(EdgePos::UR, EdgePos::UF);
  c.set_edge(EdgePos::UF, EdgePos::UR);

  c.set_corner(buffer, c0);
  c.set_corner(c1, r1(c1));
  c.set_corner(c0, r2(buffer));

  assert!(c.is_valid());

  c
}

pub fn random_ltct(rng: &mut (impl Rng + ?Sized)) -> StickerCube {
  random_ltct_with_target(rng, &[])
}
