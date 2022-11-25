use cube::{Alg, CornerPos, EdgePos, StickerCube};
use cycles::{cycle_len, get_piece_cycles};
use miniserde::Deserialize;

#[derive(Debug, PartialEq)]
pub enum Category {
  CornerCycle3,
  EdgeCycle3,
  EdgeFlip,
  Parity,
  Ltct,
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
  } else if edges.len() == 1 && corners.len() == 1 {
    if edges[0].len() == 2 && corners[0].len() == 2 {
      return Some(Category::Parity);
    }

    None
  } else if edges.len() == 1 && corners.len() == 2 {
    if edges[0].len() == 2 && corners[0].len() == 3 && corners[1].len() == 2 {
      return Some(Category::Ltct);
    }

    None
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
    if cycles.iter().all(|c| cycle_len(c) == 1) {
      Some(Category::EdgeFlip)
    } else {
      None
    }
  }
}

#[derive(Deserialize)]
pub struct LetterScheme {
  pub corners: Vec<String>,
  pub edges: Vec<String>,
}

impl LetterScheme {
  fn corner(&self, c: CornerPos) -> char {
    self.corners[c as usize].chars().next().unwrap()
  }

  pub fn corner_pair(&self, c0: CornerPos, c1: CornerPos) -> String {
    format!("{}{}", self.corner(c0), self.corner(c1))
  }

  fn edge(&self, c: EdgePos) -> char {
    self.edges[c as usize].chars().next().unwrap()
  }

  pub fn edge_pair(&self, e0: EdgePos, e1: EdgePos) -> String {
    format!("{}{}", self.edge(e0), self.edge(e1))
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

  #[test]
  fn parity() {
    assert_eq!(
      Some(Category::Parity),
      get_alg_category(
        &parse_alg("R U R' F' R U R' U' R' F R2 U' R' U'").unwrap()
      )
    );
  }

  #[test]
  fn ltct() {
    assert_eq!(
      Some(Category::Ltct),
      get_alg_category(&parse_alg("R B2 R' D Rw B2 Rw D Rw2 D'").unwrap())
    );
  }

  #[test]
  fn letter_scheme() {
    let ls = LetterScheme {
      corners: vec![
        "a".to_string(),
        "b".to_string(),
        "c".to_string(),
        "d".to_string(),
      ],
      edges: vec![
        "e".to_string(),
        "f".to_string(),
        "g".to_string(),
        "h".to_string(),
      ],
    };

    assert_eq!('a', ls.corner(CornerPos::URF));
    assert_eq!(
      "ad".to_string(),
      ls.corner_pair(CornerPos::URF, CornerPos::UFL)
    );
    assert_eq!(
      "dc".to_string(),
      ls.corner_pair(CornerPos::UFL, CornerPos::FUR)
    );

    assert_eq!('e', ls.edge(EdgePos::UF));
    assert_eq!("eg".to_string(), ls.edge_pair(EdgePos::UF, EdgePos::UL));
    assert_eq!("hf".to_string(), ls.edge_pair(EdgePos::LU, EdgePos::FU));
  }
}
