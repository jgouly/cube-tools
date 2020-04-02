use cube::{CornerPos, EdgePos, StickerCube};
use cycles::{get_piece_cycles, Piece};

mod subsets;
use subsets::*;

#[derive(Clone, Debug, PartialEq)]
struct State {
  cube: StickerCube,
}

fn solve_pieces<P: Piece + std::fmt::Debug>(
  state: &State,
  funcs: &[fn(&State) -> Option<(Vec<P>, State)>],
) -> Vec<Vec<P>> {
  let orig_cube = state.cube.clone();

  (0..)
    .try_fold((vec![], state.clone()), |(mut cycles, state), _| {
      if P::solved(&state.cube) {
        Err(cycles)
      } else {
        let (cycle, next_state) =
          funcs.iter().find_map(|f| f(&state)).unwrap_or_else(|| {
            let orig_cycles = get_piece_cycles::<P>(&orig_cube);
            unreachable!(
              "{:?} {:?} {:?} {:?}",
              cycles,
              get_piece_cycles::<P>(&state.cube),
              orig_cycles,
              orig_cube
            )
          });

        cycles.push(cycle);
        Ok((cycles, next_state))
      }
    })
    .unwrap_err()
}

fn solve_corners(state: &State) -> Vec<Vec<CornerPos>> {
  solve_pieces(
    state,
    &[
      try_3cycle,
      try_parity,
      try_buffer_in_place_cycle_break,
      try_cycle_break,
      try_corner_3twist,
      try_corner_2twist,
    ],
  )
}

fn solve_edges(state: &State) -> Vec<Vec<EdgePos>> {
  solve_pieces(
    state,
    &[
      try_3cycle,
      try_buffer_in_place_cycle_break,
      try_cycle_break,
      try_edge_2flip,
    ],
  )
}

// This checks if a cube is valid, taking into account the fact that parity
// swap may have happened.
fn is_valid(c: &StickerCube) -> bool {
  if !c.is_valid() {
    // If parity swap happened, the cube will have corner parity, but not
    // edge parity.
    c.corner_parity() && !c.edge_parity()
  } else {
    true
  }
}

pub fn solve(cube: &StickerCube) -> (Vec<Vec<EdgePos>>, Vec<Vec<CornerPos>>) {
  let mut cube = cube.clone();

  let edge_memo_swap = (EdgePos::UF, EdgePos::UR);
  if cube.corner_parity() {
    let a = cube.position_of(edge_memo_swap.0);
    let b = cube.position_of(edge_memo_swap.1);
    cube.set_edge(a, edge_memo_swap.1);
    cube.set_edge(b, edge_memo_swap.0);
  }

  (
    solve_edges(&State { cube: cube.clone() }),
    solve_corners(&State { cube: cube.clone() }),
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use cube::CornerPos::*;
  use cube::EdgePos::*;

  #[test]
  fn basic_corner_3cycles() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, RDF, LDB]);
    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![URF, LDB, RDF]], result);

    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, RDF, LDB]);
    exec_3cycle(&mut c, [URF, ULB, UBR]);
    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![URF, UBR, ULB], vec![URF, LDB, RDF]], result);
  }

  #[test]
  fn basic_edge_3cycles() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UF, RF, LB]);
    let result = solve_edges(&State { cube: c });
    assert_eq!(vec![vec![UF, LB, RF]], result);

    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UF, DF, LD]);
    exec_3cycle(&mut c, [UF, DB, UR]);
    let result = solve_edges(&State { cube: c });
    assert_eq!(vec![vec![UF, UR, DB], vec![UF, LD, DF]], result);
  }

  #[test]
  fn basic_corner_2twist() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, ULB, UFL]);
    exec_3cycle(&mut c, [URF, UFL, LBU]);
    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![RFU, BUL]], result);

    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, ULB, UFL]);
    exec_3cycle(&mut c, [URF, UFL, LBU]);
    exec_3cycle(&mut c, [URF, UFL, UBR]);
    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![URF, UBR, UFL], vec![RFU, BUL]], result);
  }

  #[test]
  fn basic_edge_2twist() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UF, UL, UR]);
    exec_3cycle(&mut c, [UF, RU, LU]);
    let result = solve_edges(&State { cube: c });
    assert_eq!(vec![vec![FU, RU]], result);

    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UF, UL, UR]);
    exec_3cycle(&mut c, [UF, RU, LU]);
    exec_3cycle(&mut c, [UF, UB, UL]);
    let result = solve_edges(&State { cube: c });
    assert_eq!(vec![vec![UF, UL, UB], vec![FU, RU]], result);
  }

  #[test]
  fn basic_corner_3twist() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, UBR, ULB]);
    exec_3cycle(&mut c, [URF, LBU, RUB]);
    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![FUR, BUL, RUB]], result);

    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, UBR, ULB]);
    exec_3cycle(&mut c, [URF, LBU, RUB]);
    exec_3cycle(&mut c, [URF, DLF, DRB]);
    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![URF, DRB, DLF], vec![FUR, BUL, RUB]], result);
  }

  #[test]
  fn test_2c2c() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [URF, UBR, ULB]);
    exec_3cycle(&mut c, [URF, UFL, ULB]);

    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![URF, UBR, UFL], vec![URF, ULB, UFL]], result);
  }

  #[test]
  fn test_2e2e() {
    let mut c = StickerCube::solved();
    exec_3cycle(&mut c, [UF, UR, UB]);
    exec_3cycle(&mut c, [UF, UL, UB]);

    let result = solve_edges(&State { cube: c });
    assert_eq!(vec![vec![UF, UR, UL], vec![UF, UB, UL]], result);
  }

  #[test]
  fn test_parity() {
    let mut c = StickerCube::solved();
    c.set_corner(URF, LDB);
    c.set_corner(LDB, URF);

    let result = solve_corners(&State { cube: c });
    assert_eq!(vec![vec![URF, LDB]], result);

    let mut c = StickerCube::solved();
    c.set_corner(URF, LDB);
    c.set_corner(LDB, URF);
    c.set_edge(UF, UR);
    c.set_edge(UR, UF);

    let (e, c) = solve(&c);
    assert_eq!(vec![vec![URF, LDB]], c);
    assert_eq!(0, e.len());
  }
}
