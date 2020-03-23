#![allow(dead_code)]

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
  solve_pieces(state, &[try_3cycle])
}

fn solve_edges(state: &State) -> Vec<Vec<EdgePos>> {
  solve_pieces(state, &[try_3cycle])
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
}
