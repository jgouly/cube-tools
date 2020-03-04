use alg_list_gen::{get_alg_category, Category};
use cube::{parse_alg, Alg, CornerPos, StickerCube};
use cycles::get_piece_cycles;

fn div(text: impl AsRef<str>) -> String {
  format!("<div>{}</div>", text.as_ref())
}

fn a(link: impl AsRef<str>, text: impl AsRef<str>) -> String {
  format!(
    "<a href=\"{}\" target=\"_blank\">{}</a>",
    link.as_ref(),
    text.as_ref()
  )
}

fn alg_cubing_move_fmt(m: cube::Move) -> String {
  format!("{}_", m).replace("'", "-")
}

fn alg_cubing_url(alg: &Alg) -> String {
  let mut url = String::from("https://alg.cubing.net/?&type=alg&alg=");
  for m in alg.iter() {
    url.push_str(&alg_cubing_move_fmt(m));
  }
  url
}

fn format_alg(alg: &Alg) -> String {
  match get_alg_category(alg) {
    Some(Category::CornerCycle3) => div(a(
      alg_cubing_url(alg),
      format!("{:?} {}", get_corner_cycle(alg), alg),
    )),
    _ => unimplemented!(),
  }
}

const TEMPLATE: &str =
  include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/templates/main.html"));

fn gen_alg_list(algs: Vec<Alg>) -> String {
  let algs_html = algs.iter().map(format_alg).collect::<String>();
  String::from(TEMPLATE).replace("BODY", &algs_html)
}

fn get_corner_cycle(alg: &Alg) -> Vec<Vec<CornerPos>> {
  let mut c = StickerCube::solved();
  for m in alg.invert().iter() {
    c.do_move_mut(m);
  }

  get_piece_cycles::<CornerPos>(&c)
}

fn read_algs() -> Vec<Alg> {
  let mut algs = vec![];

  loop {
    let mut alg = String::new();
    let res = std::io::stdin().read_line(&mut alg).unwrap();
    if res == 0 {
      break;
    }
    let alg = parse_alg(&alg).unwrap();
    algs.push(alg);
  }
  algs
}

fn main() {
  let algs = read_algs();
  println!("{}", gen_alg_list(algs));
}
