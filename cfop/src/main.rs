use std::{
  fs::File,
  io::{Read as _, Write as _},
};

use cube::{parse_alg, StickerCube};

fn serialise(table: &[usize]) {
  let mut file = File::create("cross.prune").unwrap();
  for v in table {
    file.write_all(&v.to_le_bytes()).unwrap();
  }
}

fn deserialise() -> Vec<usize> {
  match File::open("cross.prune") {
    Ok(mut f) => {
      let mut data = vec![];
      f.read_to_end(&mut data).unwrap();
      let mut table = vec![];
      for chunk in data.chunks(8) {
        table.push(usize::from_le_bytes(chunk.try_into().unwrap()));
      }
      table
    }
    Err(_) => {
      let table = cfop::gen_pruning_table();
      serialise(&table);
      table
    }
  }
}

fn main() {
  let table = deserialise();//cfop::gen_pruning_table();
  dbg!(table
    .iter()
    .enumerate()
    .filter(|&(i, f)| *f != usize::MAX)
    .collect::<Vec<_>>());

  dbg!(table
    .iter()
    .enumerate()
    .filter(|&(i, f)| *f != usize::MAX)
    .count());
  let mut scramble = String::new();
  std::io::stdin().read_line(&mut scramble).unwrap();
  let scramble = parse_alg(&scramble).unwrap();
  let mut c = StickerCube::solved();
  for m in scramble.iter() {
    c.do_move_mut(dbg!(m));
  }
  dbg!(cfop::cross_edge_position(&c));
  dbg!(table[dbg!(cfop::cross_edge_index(&c) as usize)]);
  return;
  let mut scramble = String::new();
  std::io::stdin().read_line(&mut scramble).unwrap();
  let scramble = parse_alg(&scramble).unwrap();
  let mut c = StickerCube::solved();
  for m in scramble.iter() {
    c.do_move_mut(m);
  }

  dbg!(cfop::cross_edge_position(&c));
  dbg!(cfop::cross_edge_index(&c));

  let scramble = parse_alg("R' L' B' R  D'").unwrap();
  for m in scramble.iter() {
    c.do_move_mut(m);
  }

  dbg!(cfop::cross_edge_position(&c));
  dbg!(cfop::cross_edge_index(&c));
}
