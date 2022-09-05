use cube::{Face, Move};

pub(crate) trait GroupCoord: Copy {
  fn is_solved(&self) -> bool;
}

pub(crate) trait GroupTables {
  type Coord: GroupCoord;

  fn transition(&self, coord: Self::Coord, face: Face) -> Self::Coord;
  fn prune_depth(&self, coord: Self::Coord) -> usize;
}

pub(crate) trait GroupIDS {
  type Tables: GroupTables;

  fn solution_check(solution: &[Move]) -> bool;
  fn turn_counts(f: Face) -> core::ops::Range<usize>;
}

pub(crate) fn ids<G: GroupIDS>(
  coord: <G::Tables as GroupTables>::Coord,
  depth_remaining: usize,
  tables: &G::Tables,
  solution: &mut Vec<Move>,
) -> bool {
  if depth_remaining == 0 {
    if !G::solution_check(solution) {
      return false;
    }

    return coord.is_solved();
  }

  if depth_remaining < tables.prune_depth(coord) {
    return false;
  }

  for &f in &[Face::U, Face::D, Face::F, Face::B, Face::R, Face::L] {
    if skip_face(solution, f) {
      continue;
    }

    let mut next = coord;

    for i in G::turn_counts(f) {
      next = tables.transition(next, f);
      let m = Move::from_face_and_num_90degrees(f, i + 1);
      solution.push(m);

      if ids::<G>(next, depth_remaining - 1, tables, solution) {
        return true;
      }

      solution.pop();
    }
  }
  false
}

// Check if a face should be skipped.
fn skip_face(solution: &[Move], face: Face) -> bool {
  let len = solution.len();
  if len > 0 {
    // Check for A A.
    if solution.last().map(|m| m.face() == face).unwrap_or(false) {
      return true;
    }

    if len > 1 {
      // Check for A B A where A and B are opposite faces.
      let m1 = &solution[len - 2];
      let m2 = &solution[len - 1];

      if m1.face() == face && m2.face().is_opposite(face) {
        return true;
      }
    }
  }

  false
}
