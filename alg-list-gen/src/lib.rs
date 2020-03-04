use cube::{Alg, CornerPos, EdgePos, StickerCube};
use cycles::get_piece_cycles;

#[derive(Debug, PartialEq)]
pub enum Category {
  CornerCycle3,
  EdgeCycle3,
}

pub fn get_alg_category(alg: &Alg) -> Option<Category> {
  let c = alg.invert().iter().fold(StickerCube::solved(), |mut c, m| {
    c.do_move_mut(m);
    c
  });

  let corners = get_piece_cycles::<CornerPos>(&c);
  let edges = get_piece_cycles::<EdgePos>(&c);

  if edges.len() == 0 {
    corners_only(&corners)
  } else if corners.len() == 0 {
    edges_only(&edges)
  } else {
    None
  }
}

fn corners_only(cycles: &[Vec<CornerPos>]) -> Option<Category> {
  if cycles.len() == 1 {
    match cycles.get(0).map(|c| c.len()) {
      Some(3) => Some(Category::CornerCycle3),
      _ => None,
    }
  } else {
    None
  }
}

fn edges_only(cycles: &[Vec<EdgePos>]) -> Option<Category> {
  if cycles.len() == 1 {
    match cycles.get(0).map(|c| c.len()) {
      Some(3) => Some(Category::EdgeCycle3),
      _ => None,
    }
  } else {
    None
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use cube::parse_alg;

  #[test]
  fn corner_cycle() {
    assert_eq!(
      Some(Category::CornerCycle3),
      corners_only(&[vec![CornerPos::URF, CornerPos::RDF, CornerPos::LDB]])
    );

    assert_eq!(None, corners_only(&[vec![CornerPos::URF, CornerPos::RDF]]));

    assert_eq!(
      Some(Category::CornerCycle3),
      get_alg_category(&parse_alg("[R U R', D2]").unwrap())
    );

    assert_eq!(None, get_alg_category(&parse_alg("U").unwrap()));
  }

  #[test]
  fn edge_cycle() {
    assert_eq!(
      Some(Category::EdgeCycle3),
      edges_only(&[vec![EdgePos::UF, EdgePos::DB, EdgePos::LB]])
    );

    assert_eq!(None, edges_only(&[vec![EdgePos::UF, EdgePos::UR]]));

    assert_eq!(
      Some(Category::EdgeCycle3),
      get_alg_category(&parse_alg("R' L F2 R L' U2").unwrap())
    );

    assert_eq!(None, get_alg_category(&parse_alg("U").unwrap()));
  }
}
