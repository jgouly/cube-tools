use crate::State;
use cube::StickerCube;
use cycles::Piece;

pub(crate) fn exec_3cycle<P: Piece>(c: &mut StickerCube, cycle: [P; 3]) {
  let p0 = P::lookup(c, cycle[0]);
  let p1 = P::lookup(c, cycle[1]);
  let p2 = P::lookup(c, cycle[2]);
  P::set(c, cycle[2], p1);
  P::set(c, cycle[1], p0);
  P::set(c, cycle[0], p2);
}

pub(crate) fn try_3cycle<P: Piece + std::fmt::Debug>(
  state: &State,
) -> Option<(Vec<P>, State)> {
  let c = &state.cube;
  let buffer = P::oriented_iter().next().unwrap();

  let p0 = P::lookup(c, buffer);
  let p1 = P::lookup(c, p0);

  if buffer.orient() == p0.orient() || buffer.orient() == p1.orient() {
    return None;
  }

  let cycle = [buffer, p0, p1];
  let mut next_cube = c.clone();
  exec_3cycle(&mut next_cube, cycle);
  Some((cycle.to_vec(), State { cube: next_cube }))
}

#[cfg(test)]
mod tests {
  use super::*;
  use cube::CornerPos::*;
  use cube::EdgePos::*;

  #[test]
  fn basic_3cycle() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, RDF, LDB]);
    let result = try_3cycle(&State { cube: c });
    assert_eq!(
      Some((
        vec![URF, LDB, RDF],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );

    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UF, UB, DF]);
    let result = try_3cycle(&State { cube: c });
    assert_eq!(
      Some((
        vec![UF, DF, UB],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );
  }
}
