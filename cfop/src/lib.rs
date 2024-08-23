use cube::{parse_alg, CornerPos, EdgePos, Face, Move, StickerCube};

pub fn cross_edge_position(c: &StickerCube) -> [EdgePos; 4] {
  [
    c.position_of(EdgePos::DF),
    c.position_of(EdgePos::DL),
    c.position_of(EdgePos::DB),
    c.position_of(EdgePos::DR),
  ]
}

/*
  // Modify the edge values such that:
 //   0 < edge[n] < (24 - 2n)
 //
 // e.g.
 //   0 < edge[0] < 24
 //   0 < edge[1] < 22
 for i in 0..edges.len() {
   for j in 0..i {
     if edges[i] > edges[j] {
       edges[i] -= 2;
     }
   }
   debug_assert!(edges[i] < ((edge_pos.len() as u32) - (2 * i as u32)));
 }

 // Combine the values into the index.
 let mut edge_mult = edge_pos.len() as u32;
 let mut index = 0;
 for &e in &edges {
   debug_assert!(e < edge_mult);
   edge_mult -= 2;
   index += e;
   index *= edge_mult;
 }
 // Undo the last multiplication.
 index /= edge_mult;
*/

pub fn cross_edge_index(c: &StickerCube) -> u64 {
  let [e0, e1, e2, e3] = cross_edge_position(c);
  // dbg!((e0,e1,e2,e3));
  let [mut e0, mut e1, mut e2, mut e3] =
    [e0 as u64, e1 as u64, e2 as u64, e3 as u64];
  // dbg!((e0,e1,e2,e3));
  if e0 > e1 {
    e0 -= 2;
  }

  if e0 > e2 {
    e0 -= 2;
  }

  if e0 > e3 {
    e0 -= 2;
  }

  if e1 > e2 {
    e1 -= 2;
  }

  if e1 > e3 {
    e1 -= 2;
  }

  if e2 > e3 {
    e2 -= 2;
  }
  // dbg!((e0,e1,e2,e3));
  (((((e0 * 22) + e1) * 20) + e2) * 18) + e3
}

const CROSS_EDGE_SOLVED: u64 = 2272;
const CROSS_INDEX_SIZE: usize = 24 * 22 * 20 * 18;

fn f2l_pair_position(cube: &StickerCube, e: EdgePos) -> (EdgePos, CornerPos) {
  let c = match e {
    EdgePos::FR => CornerPos::DFR,
    EdgePos::FL => CornerPos::DLF,
    EdgePos::BL => CornerPos::DBL,
    EdgePos::BR => CornerPos::DRB,
    _ => unreachable!(),
  };

  (cube.position_of(e), cube.position_of_corner(c))
}

fn gen_pruning_table_inner(
  c: &StickerCube,
  table: &mut Vec<usize>,
  depth: usize,
) {
  if depth > 9 {
    return;
  }
  let turns = [Face::U, Face::D, Face::F, Face::B, Face::R, Face::L];
  let n = [1, 2, 3];
  // for m in turns
  //   .into_iter()
  //   .zip(n.into_iter())
  //   .map(|(f, i)| Move::from_face_and_num_90degrees(f, i))
  for f in turns {
    for m in n
      .into_iter()
      .map(|i| Move::from_face_and_num_90degrees(f, i))
    {
      let mut c = c.clone();
      c.do_move_mut(m);
      if table[cross_edge_index(&c) as usize] <= depth {
        continue;
      }
      table[cross_edge_index(&c) as usize] = depth;
      gen_pruning_table_inner(&c, table, depth + 1);
    }
  }
}

pub fn gen_pruning_table() -> Vec<usize> {
  let c = StickerCube::solved();
  let mut table = vec![usize::MAX; CROSS_INDEX_SIZE];
  table[cross_edge_index(&c) as usize] = 0;
  gen_pruning_table_inner(&c, &mut table, 1);
  table
}

fn solve(
  c: &StickerCube,
  depth_remaining: usize,
  solution: &mut Vec<Move>,
) -> bool {
  if depth_remaining == 0 {
    return cross_edge_index(c) == CROSS_EDGE_SOLVED;
  }

  return false;
}

#[test]
fn index_test() {
  let c = StickerCube::solved();
  assert_eq!(cross_edge_index(&c), CROSS_EDGE_SOLVED);
  assert_eq!(
    f2l_pair_position(&c, EdgePos::FR),
    (EdgePos::FR, CornerPos::DFR)
  );
  assert!(solve(&c, 0, &mut vec![]));

  let scramble = parse_alg("R2").unwrap();
  let mut c = StickerCube::solved();
  for m in scramble.iter() {
    c.do_move_mut(m);
  }
  assert_eq!(cross_edge_index(&c), 528);
  assert_eq!(
    f2l_pair_position(&c, EdgePos::FR),
    (EdgePos::BR, CornerPos::UBR)
  );
  assert!(!solve(&c, 0, &mut vec![]));
}
