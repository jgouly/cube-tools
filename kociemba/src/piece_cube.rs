use cube::{CornerPos, EdgePos, Piece, StickerCube};

const NUM_CORNERS: usize = 8;
const NUM_EDGES: usize = 12;

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct PieceCube {
  pub cp: [CornerPos; NUM_CORNERS],
  pub co: [u8; NUM_CORNERS],
  pub ep: [EdgePos; NUM_EDGES],
  pub eo: [u8; NUM_EDGES],
}

impl PieceCube {
  pub fn solved() -> Self {
    let cp = [
      CornerPos::URF,
      CornerPos::UFL,
      CornerPos::ULB,
      CornerPos::UBR,
      CornerPos::DFR,
      CornerPos::DLF,
      CornerPos::DBL,
      CornerPos::DRB,
    ];
    let co = [0; NUM_CORNERS];
    let ep = [
      EdgePos::UF,
      EdgePos::UL,
      EdgePos::UB,
      EdgePos::UR,
      EdgePos::DF,
      EdgePos::DL,
      EdgePos::DB,
      EdgePos::DR,
      EdgePos::FR,
      EdgePos::FL,
      EdgePos::BL,
      EdgePos::BR,
    ];
    let eo = [0; NUM_EDGES];
    PieceCube { cp, co, ep, eo }
  }
}

impl From<PieceCube> for StickerCube {
  fn from(cube: PieceCube) -> Self {
    let mut sticker_cube = StickerCube::solved();

    for (&cp, (&co, sticker)) in cube
      .cp
      .iter()
      .zip(cube.co.iter().zip(CornerPos::oriented_iter()))
    {
      sticker_cube.set_corner(
        sticker,
        match co {
          0 => cp,
          1 => cp.clockwise_pos(),
          2 => cp.anti_clockwise_pos(),
          _ => unreachable!(),
        },
      );
    }

    for (&ep, (&eo, sticker)) in cube
      .ep
      .iter()
      .zip(cube.eo.iter().zip(EdgePos::oriented_iter()))
    {
      sticker_cube.set_edge(
        sticker,
        match eo {
          0 => ep,
          1 => ep.flip(),
          _ => unreachable!(),
        },
      );
    }

    sticker_cube
  }
}

impl From<StickerCube> for PieceCube {
  fn from(sticker_cube: StickerCube) -> Self {
    let mut cp = [CornerPos::URF; NUM_CORNERS];
    for (cp, sticker) in cp.iter_mut().zip(CornerPos::oriented_iter()) {
      *cp = sticker_cube.corner(sticker).orient();
    }

    let mut co = [0; NUM_CORNERS];
    for (co, sticker) in co.iter_mut().zip(CornerPos::oriented_iter()) {
      *co = sticker_cube
        .corner(sticker)
        .num_rotations()
        .try_into()
        .unwrap();
    }

    let mut ep = [EdgePos::UR; NUM_EDGES];
    for (ep, sticker) in ep.iter_mut().zip(EdgePos::oriented_iter()) {
      *ep = sticker_cube.edge(sticker).orient();
    }

    let mut eo = [0; NUM_EDGES];
    for (eo, sticker) in eo.iter_mut().zip(EdgePos::oriented_iter()) {
      *eo = sticker_cube
        .edge(sticker)
        .num_rotations()
        .try_into()
        .unwrap();
    }

    PieceCube { cp, co, ep, eo }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use cube::parse_alg;

  #[test]
  fn sticker_cube_conversion() {
    let sc1 = StickerCube::solved();
    let c = PieceCube::solved();
    let sc2 = c.into();
    assert_eq!(sc1, sc2);

    let c1 = PieceCube::solved();
    let sc = StickerCube::solved();
    let c2 = sc.into();
    assert_eq!(c1, c2);

    let mut sc1 = StickerCube::solved();
    let u = parse_alg("U").unwrap();

    sc1.do_move_mut(u.iter().next().unwrap());
    let c: PieceCube = sc1.clone().into();
    let sc2: StickerCube = c.into();
    assert_eq!(sc1, sc2);

    let mut sc1 = StickerCube::solved();
    let r = parse_alg("R").unwrap();

    sc1.do_move_mut(r.iter().next().unwrap());
    let c: PieceCube = sc1.clone().into();
    let sc2: StickerCube = c.into();
    assert_eq!(sc1, sc2);
  }

  #[test]
  fn random_sticker_cube_conversion() {
    for _ in 0..100 {
      let sc1 = cube::random_state();
      let c: PieceCube = sc1.clone().into();
      let sc2: StickerCube = c.into();
      assert_eq!(sc1, sc2);
    }
  }
}
