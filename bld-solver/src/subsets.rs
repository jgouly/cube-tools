use crate::State;
use cube::{CornerPos, EdgePos, StickerCube};
use cycles::{cycle_len, get_piece_cycles, Piece};

pub(crate) fn exec_3cycle<P: Piece + std::fmt::Debug>(
  c: &mut StickerCube,
  cycle: [P; 3],
) {
  assert_ne!(cycle[0].orient(), cycle[1].orient());
  assert_ne!(cycle[0].orient(), cycle[2].orient());
  assert_ne!(cycle[1].orient(), cycle[2].orient());
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

fn exec_2twist<P: Piece + std::fmt::Debug>(c: &mut StickerCube, cycle: [P; 2]) {
  assert_ne!(cycle[0].orient(), cycle[1].orient());
  P::set(c, cycle[0].orient(), cycle[0].orient());
  P::set(c, cycle[1].orient(), cycle[1].orient());
}

pub(crate) fn try_2twist<P: Piece + std::fmt::Debug>(
  state: &State,
) -> Option<(Vec<P>, State)> {
  let pieces = get_piece_cycles::<P>(&state.cube);
  if !pieces.iter().all(|c| cycle_len(&c) == 1)
    || pieces.iter().filter(|c| cycle_len(&c) == 1).count() % 2 != 0
  {
    return None;
  }

  let cycle = [pieces[0][1], pieces[1][1]];
  let mut next_cube = state.cube.clone();
  exec_2twist(&mut next_cube, cycle);
  Some((cycle.to_vec(), State { cube: next_cube }))
}

fn exec_corner_3twist(c: &mut StickerCube, cycle: [CornerPos; 3]) {
  c.set_corner(cycle[0].orient(), cycle[0].orient());
  c.set_corner(cycle[1].orient(), cycle[1].orient());
  c.set_corner(cycle[2].orient(), cycle[2].orient());
}

pub(crate) fn try_corner_3twist(
  state: &State,
) -> Option<(Vec<CornerPos>, State)> {
  let c = &state.cube;
  let corners = get_piece_cycles::<CornerPos>(&c);
  if corners.len() < 3
    || !corners.iter().all(|c| cycle_len(&c) == 1)
    || corners.iter().filter(|c| cycle_len(&c) == 1).count() % 2 != 1
  {
    return None;
  }

  let cycle = [corners[0][1], corners[1][1], corners[2][1]];
  let mut next_cube = c.clone();
  exec_corner_3twist(&mut next_cube, cycle);
  Some((cycle.to_vec(), State { cube: next_cube }))
}

fn break_into_non_twist<P: Piece>(
  cycles: &[Vec<P>],
  buffer_idx: Option<usize>,
) -> Option<usize> {
  for (i, c) in cycles.iter().enumerate() {
    if Some(i) == buffer_idx {
      continue;
    }

    if cycle_len(c) != 1 {
      return Some(i);
    }
  }

  None
}

pub(crate) fn try_buffer_in_place_cycle_break<P: Piece + std::fmt::Debug>(
  state: &State,
) -> Option<(Vec<P>, State)> {
  let c = &state.cube;

  let buffer = P::oriented_iter().next().unwrap();
  if P::lookup(c, buffer).orient() != buffer.orient() {
    return None;
  }

  let pieces = get_piece_cycles(c);

  let break_idx = break_into_non_twist(&pieces, None);
  let cycle_break = pieces[break_idx?][0];

  let p0 = P::lookup(c, cycle_break);

  let cycle = [buffer, cycle_break, p0];
  let mut next_cube = c.clone();
  exec_3cycle(&mut next_cube, cycle);
  Some((cycle.to_vec(), State { cube: next_cube }))
}

pub(crate) fn try_cycle_break<P: Piece + std::fmt::Debug>(
  state: &State,
) -> Option<(Vec<P>, State)> {
  let c = &state.cube;

  let pieces = get_piece_cycles::<P>(&c);
  let buffer = P::oriented_iter().next().unwrap();
  let buffer_idx = pieces.iter().position(|p| p[0] == buffer)?;

  if cycle_len(&pieces[buffer_idx]) != 2 || pieces.len() < 2 {
    return None;
  }

  let p0 = P::lookup(c, buffer);

  let break_idx = break_into_non_twist(&pieces, Some(buffer_idx));
  let cycle_break = pieces[break_idx?][0];

  let cycle = [buffer, p0, cycle_break];
  let mut next_cube = c.clone();
  exec_3cycle(&mut next_cube, cycle);
  Some((cycle.to_vec(), State { cube: next_cube }))
}

fn exec_parity(
  c: &mut StickerCube,
  corners: [CornerPos; 2],
  edges: [EdgePos; 2],
) {
  let c0 = c.corner(corners[0]);
  let c1 = c.corner(corners[1]);
  c.set_corner(corners[0], c1);
  c.set_corner(corners[1], c0);

  let e0 = c.edge(edges[0]);
  let e1 = c.edge(edges[1]);
  c.set_edge(edges[0], e1);
  c.set_edge(edges[1], e0);
}

pub(crate) fn try_parity(state: &State) -> Option<(Vec<CornerPos>, State)> {
  let c = &state.cube;

  let corners = get_piece_cycles::<CornerPos>(&c);
  if corners.iter().any(|c| cycle_len(c) > 2)
    || corners.iter().filter(|c| cycle_len(c) == 2).count() != 1
  {
    return None;
  }

  let buffer = CornerPos::URF;
  let p0 = c.corner(buffer);
  if buffer.orient() == p0.orient() {
    return None;
  }

  let cycle = [buffer, p0];
  let mut next_cube = c.clone();
  exec_parity(&mut next_cube, cycle, [EdgePos::UF, EdgePos::UR]);
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

  #[test]
  fn basic_2twist() {
    let mut c = StickerCube::solved();
    c.set_corner(URF, FUR);
    c.set_corner(UFL, FLU);
    let result = try_2twist(&State { cube: c });
    assert_eq!(
      Some((
        vec![FUR, FLU],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );

    let mut c = StickerCube::solved();
    c.set_edge(UF, FU);
    c.set_edge(UR, RU);
    let result = try_2twist(&State { cube: c });
    assert_eq!(
      Some((
        vec![FU, RU],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );
  }

  #[test]
  fn basic_3twist() {
    let mut c = StickerCube::solved();
    c.set_corner(URF, FUR);
    c.set_corner(UFL, FLU);
    c.set_corner(ULB, LBU);
    let result = try_corner_3twist(&State { cube: c });
    assert_eq!(
      Some((
        vec![FUR, FLU, LBU],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );
  }

  #[test]
  fn test_cycle_break_index() {
    let corners = vec![vec![URF, FUR], vec![UFL, ULB, UBR]];
    assert_eq!(Some(1), break_into_non_twist(&corners, None));

    let corners = vec![vec![URF, UBR], vec![UFL, ULB, DRB]];
    assert_eq!(Some(1), break_into_non_twist(&corners, Some(0)));

    let corners = vec![vec![URF, UBR], vec![UFL, FLU], vec![ULB, DBL, DRB]];
    assert_eq!(Some(2), break_into_non_twist(&corners, Some(0)));
  }

  #[test]
  fn test_buffer_in_place_cycle_break() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UFL, RDF, LDB]);

    let mut expected = StickerCube::solved();
    exec_3cycle(&mut expected, [URF, UFL, RDF]);

    let result = try_buffer_in_place_cycle_break(&State { cube: c });
    assert_eq!(
      Some((vec![URF, UFL, LDB], State { cube: expected })),
      result
    );

    let mut c = StickerCube::solved();
    c.set_edge(UF, FU);
    c.set_edge(UR, RU);
    exec_3cycle(&mut c, [UL, UB, DR]);

    let mut expected = StickerCube::solved();
    expected.set_edge(UF, FU);
    expected.set_edge(UR, RU);
    exec_3cycle(&mut expected, [UF, UL, UB]);

    let result = try_buffer_in_place_cycle_break(&State { cube: c });
    assert_eq!(Some((vec![UF, UL, DR], State { cube: expected })), result);
  }

  #[test]
  fn test_cycle_break() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, UBR, ULB]);
    exec_3cycle(&mut c, [URF, UFL, ULB]);

    let mut expected = StickerCube::solved();
    exec_3cycle(&mut expected, [URF, UFL, ULB]);

    let result = try_cycle_break(&State { cube: c });
    assert_eq!(
      Some((vec![URF, UBR, UFL], State { cube: expected })),
      result
    );
  }

  #[test]
  fn test_parity() {
    let mut c = StickerCube::solved();
    c.set_corner(URF, UBR);
    c.set_corner(UBR, URF);
    c.set_edge(UF, UR);
    c.set_edge(UR, UF);

    let result = try_parity(&State { cube: c });
    assert_eq!(
      Some((
        vec![URF, UBR],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );

    let mut c = StickerCube::solved();
    c.set_corner(URF, FLU);
    c.set_corner(FLU, URF);
    c.set_edge(UF, UR);
    c.set_edge(UR, UF);

    let result = try_parity(&State { cube: c });
    assert_eq!(
      Some((
        vec![URF, FLU],
        State {
          cube: StickerCube::solved()
        }
      )),
      result
    );
  }
}
