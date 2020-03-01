use cube::EdgePos;
use cube::StickerCube;

pub fn get_edge_cycles(c: &StickerCube) -> Vec<Vec<EdgePos>> {
  let mut unsolved = Vec::with_capacity(12);
  let mut cycles = vec![];

  let order = EdgePos::iter().collect::<Vec<_>>();
  for e in order.chunks(2) {
    if c.edge(e[0]) != e[0] {
      unsolved.push(e[0]);
    }
  }

  while unsolved.len() > 0 {
    let mut cur_cycle = vec![];
    let buffer = unsolved[0];
    cur_cycle.push(buffer);

    let mut current_piece = buffer;

    loop {
      current_piece = c.edge(current_piece);

      unsolved.remove(
        unsolved
          .iter()
          .position(|&p| p == current_piece || p == current_piece.flip())
          .unwrap(),
      );

      // The buffer is solved, end of the current cycle.
      if current_piece == buffer {
        break;
      }

      cur_cycle.push(current_piece);

      // The buffer is in place but flipped, end of the current cycle.
      if current_piece.flip() == buffer {
        break;
      }
    }

    cycles.push(cur_cycle);
  }

  cycles
}

#[cfg(test)]
mod tests {
  use super::*;
  use cube::parse_alg;
  use cube::EdgePos::*;

  #[test]
  fn edge_cycles() {
    let c = StickerCube::solved();
    let cycles = get_edge_cycles(&c);
    assert_eq!(Vec::<Vec<EdgePos>>::new(), cycles);

    macro_rules! test_alg_cycles {
      ($alg: expr, $cycles: expr) => {
        let alg = parse_alg($alg).unwrap();

        let mut c = StickerCube::solved();
        for m in alg.iter() {
          c.do_move_mut(m);
        }

        let cycles = get_edge_cycles(&c);
        assert_eq!($cycles, cycles);
      };
    }

    test_alg_cycles!("R2 U R U R' U' R' U' R' U R'", vec![vec![UF, UR, UL]]);
    test_alg_cycles!("R2", vec![vec![UR, DR], vec![FR, BR]]);
    test_alg_cycles!(
      "R' U2 R2 U R' U' R' U2 L F R F' L'",
      vec![vec![UF, FU], vec![UR, RU]]
    );
    test_alg_cycles!(
      "R U R' U' R' F R2 U' R' U' R U R' F'",
      vec![vec![UL, UR]]
    );
  }
}
