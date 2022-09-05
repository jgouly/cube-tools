use crate::{Coord, PieceCube};
use cube::{Face, Move};

pub(crate) fn init_transition_table<T: Coord>(group: usize) -> Vec<[usize; 6]> {
  let mut v = vec![[0; 6]; T::NUM_ELEMS];
  let amounts = match group {
    0 => [1; 6],
    1 => [1, 1, 2, 2, 2, 2],
    _ => unreachable!(),
  };
  let turns = [Face::U, Face::D, Face::F, Face::B, Face::R, Face::L];

  for i in 0..T::NUM_ELEMS {
    let mut c = PieceCube::solved();
    T::set_coord(&mut c, i);

    for (&f, &amt) in turns.iter().zip(&amounts) {
      let nc = c.do_move(Move::from_face_and_num_90degrees(f, amt));
      let coord = T::get_coord(&nc);
      assert!(coord < T::NUM_ELEMS);
      v[i][f as usize] = coord;
    }
  }
  v
}
