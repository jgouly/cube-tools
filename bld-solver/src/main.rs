use bld_solver::solve;
use cube::{parse_alg, StickerCube};

fn main() {
  let mut scramble = String::new();
  std::io::stdin().read_line(&mut scramble).unwrap();
  let scramble = parse_alg(&scramble).unwrap();

  let mut c = StickerCube::solved();
  for m in scramble.iter() {
    c.do_move_mut(m);
  }

  let (e, c) = solve(&c);
  println!("edges: {:?}", e);
  println!("corners: {:?}", c);
}
