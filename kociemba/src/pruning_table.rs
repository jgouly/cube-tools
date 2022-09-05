const NUM_FACES: usize = 6;
const NUM_90D_ROT: usize = 3;

fn init_prune_table_inner(
  coord: usize,
  prune_table: &mut [usize],
  trans_table: &[[usize; 6]],
  max_depth: usize,
  depth: usize,
) {
  // End the current search branch if max_depth is reached or the current
  // coordinate was already reached at a lower depth.
  if depth == max_depth || prune_table[coord] <= depth {
    return;
  }
  // Save the current depth for this coordinate.
  prune_table[coord] = depth;

  for f in 0..NUM_FACES {
    let mut new_coord = coord;

    for _ in 0..NUM_90D_ROT {
      new_coord = trans_table[new_coord][f];
      init_prune_table_inner(
        new_coord,
        prune_table,
        trans_table,
        max_depth,
        depth + 1,
      );
    }
  }
}

// Initialise a pruning table from a transition table. The pruning table
// stores the depth of each coordinate.
pub(crate) fn init_prune_table(
  trans_table: &[[usize; 6]],
  max_depth: usize,
  table_size: usize,
) -> Box<[usize]> {
  let mut table = vec![table_size; table_size];
  init_prune_table_inner(0, &mut table, trans_table, max_depth, 0);
  table.into_boxed_slice()
}
