use crate::{num_inversions, CornerPos, EdgePos, Piece, StickerCube};
use rand::seq::SliceRandom;
use rand::Rng;

fn random_state_pieces<P: Piece>(rng: &mut (impl Rng + ?Sized)) -> Vec<P> {
  let mut pieces = P::oriented_iter().collect::<Vec<_>>();
  pieces.shuffle(rng);

  let orientation =
    std::iter::repeat_with(|| rng.gen_range(0..P::NUM_ORIENTATIONS));
  let mut total_orientation = 0;

  pieces.iter_mut().zip(orientation).for_each(|(c, i)| {
    total_orientation += i;
    for _ in 0..i {
      *c = c.rotate();
    }
  });

  pieces.last_mut().map(|c| {
    for _ in
      0..(P::NUM_ORIENTATIONS - (total_orientation % P::NUM_ORIENTATIONS))
    {
      *c = c.rotate();
    }
  });

  pieces
}

fn fix_parity<P: PartialOrd>(pieces: &mut [P], rng: &mut (impl Rng + ?Sized)) {
  let c0 = rng.gen_range(0..pieces.len());
  let mut c1 = rng.gen_range(0..pieces.len() - 1);
  if c1 >= c0 {
    c1 += 1;
  }

  assert_ne!(c0, c1);
  pieces.swap(c0, c1);
}

fn random_state_subset<P: Piece + PartialOrd + std::fmt::Debug>(
  rng: &mut (impl Rng + ?Sized),
) -> StickerCube {
  let mut pieces = random_state_pieces(rng);

  let parity = num_inversions(&pieces) % 2 != 0;
  if parity {
    fix_parity(&mut pieces, rng);
  }

  let mut c = StickerCube::solved();
  for (p0, &p1) in P::oriented_iter().zip(&pieces) {
    P::set(&mut c, p0, p1);
  }

  assert!(c.is_valid(), "{:?} {:?}", c, pieces);

  c
}

pub fn random_state_edges(rng: &mut (impl Rng + ?Sized)) -> StickerCube {
  random_state_subset::<EdgePos>(rng)
}

pub fn random_state_corners(rng: &mut (impl Rng + ?Sized)) -> StickerCube {
  random_state_subset::<CornerPos>(rng)
}

pub fn random_state(rng: &mut (impl Rng + ?Sized)) -> StickerCube {
  let mut corners = random_state_pieces(rng);
  let mut edges = random_state_pieces(rng);

  let c_parity = num_inversions(&corners) % 2 != 0;
  let e_parity = num_inversions(&edges) % 2 != 0;
  if c_parity != e_parity {
    if rng.gen() {
      fix_parity(&mut corners, rng);
    } else {
      fix_parity(&mut edges, rng);
    }

    let c_parity = num_inversions(&corners) % 2 != 0;
    let e_parity = num_inversions(&edges) % 2 != 0;
    assert_eq!(c_parity, e_parity);
  }

  let mut c = StickerCube::solved();
  for (c0, &c1) in CornerPos::oriented_iter().zip(&corners) {
    c.set_corner(c0, c1);
  }

  for (e0, &e1) in EdgePos::oriented_iter().zip(&edges) {
    c.set_edge(e0, e1);
  }

  assert!(c.is_valid(), "{:?} {:?}", c, corners);

  c
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::thread_rng;

  #[test]
  fn test_random_states_are_valid() {
    for _ in 0..100 {
      let c = random_state_corners(&mut thread_rng());
      assert!(c.is_valid());
    }

    for _ in 0..100 {
      let c = random_state_edges(&mut thread_rng());
      assert!(c.is_valid());
    }

    for _ in 0..100 {
      let c = random_state(&mut thread_rng());
      assert!(c.is_valid());
    }
  }
}
