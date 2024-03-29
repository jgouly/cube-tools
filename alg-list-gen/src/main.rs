use alg_list_gen::{get_alg_category, Category, LetterScheme};
use cube::{parse_alg, Alg, CornerPos, EdgePos, Piece, StickerCube};
use cycles::get_piece_cycles;
use miniserde::json;

fn div(text: impl AsRef<str>) -> String {
  format!("<div>{}</div>", text.as_ref())
}

fn div_with_attr(text: impl AsRef<str>, attr: impl AsRef<str>) -> String {
  format!("<div{}>{}</div>", attr.as_ref(), text.as_ref())
}

fn a(link: impl AsRef<str>, text: impl AsRef<str>) -> String {
  format!(
    "<a href=\"{}\" target=\"_blank\">{}</a>",
    link.as_ref(),
    text.as_ref()
  )
}

fn div_flip_or_twist<P: Piece + std::fmt::Debug>(
  v: String,
  cycle: &[Vec<P>],
) -> String {
  cycle.iter().rev().fold(v, |acc, c| {
    div_with_attr(acc, format!(" class='{:?}'", c[0]))
  })
}

fn div_cycle<P: Piece + std::fmt::Debug, S: AsRef<str>>(
  v: S,
  cycle: &[Vec<P>],
) -> String {
  div_with_attr(
    div_with_attr(
      div_with_attr(v, format!(" class='{:?}'", cycle[0][2])),
      format!(" class='{:?}'", cycle[0][1]),
    ),
    format!(" class='{:?}'", cycle[0][0]),
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

fn format_alg(alg: &Alg, letter_scheme: &Option<LetterScheme>) -> String {
  (match get_alg_category(alg) {
    Some(Category::CornerCycle3) => {
      let cycle = get_corner_cycle(alg);
      div_cycle(
        div(a(
          alg_cubing_url(alg),
          format!(
            "{:?} {} {}",
            cycle[0],
            letter_scheme.as_ref().map_or_else(String::new, |s| s
              .corner_pair(cycle[0][1], cycle[0][2])),
            alg
          ),
        )),
        &cycle,
      )
    }
    Some(Category::EdgeCycle3) => {
      let cycle = get_edge_cycle(alg);
      div_cycle(
        div(a(
          alg_cubing_url(alg),
          format!(
            "{:?} {} {}",
            cycle[0],
            letter_scheme.as_ref().map_or_else(String::new, |s| s
              .edge_pair(cycle[0][1], cycle[0][2])),
            alg
          ),
        )),
        &cycle,
      )
    }
    Some(Category::EdgeFlip) => {
      let cycle = get_edge_cycle(alg);
      let cycle_str = match cycle.len() {
        2 => format!("[{:?}, {:?}]", cycle[0][0], cycle[1][0]),
        4 => format!(
          "[{:?}, {:?}, {:?}, {:?}]",
          cycle[0][0], cycle[1][0], cycle[2][0], cycle[3][0]
        ),
        _ => unimplemented!(),
      };
      div_flip_or_twist(
        a(alg_cubing_url(alg), format!("{} {}", cycle_str, alg)),
        &cycle,
      )
    }
    Some(Category::Twist2) => {
      let corner_cycle = get_corner_cycle(alg);
      let corner1 = match corner_cycle[0][1].num_rotations() {
        1 => corner_cycle[0][1].rotate().rotate(),
        2 => corner_cycle[0][1].rotate(),
        _ => unreachable!(),
      };

      let corner2 = match corner_cycle[1][1].num_rotations() {
        1 => corner_cycle[1][1].rotate().rotate(),
        2 => corner_cycle[1][1].rotate(),
        _ => unreachable!(),
      };
      div_with_attr(
        div_with_attr(
          div(a(
            alg_cubing_url(alg),
            format!("[{:?}] [{:?}] {}", corner1, corner2, alg),
          )),
          format!(" class='{:?}'", corner_cycle[1][1]),
        ),
        format!(" class='{:?}'", corner_cycle[0][1]),
      )
    }
    Some(Category::Parity) => {
      let corner_cycle = get_corner_cycle(alg);
      let edge_cycle = get_edge_cycle(alg);
      div_with_attr(
        div_with_attr(
          div(a(
            alg_cubing_url(alg),
            format!("{:?} {:?} {}", corner_cycle[0], edge_cycle[0], alg),
          )),
          format!(" class='{:?}'", corner_cycle[0][1]),
        ),
        format!(" class='{:?}'", corner_cycle[0][0]),
      )
    }
    Some(Category::Ltct) => {
      let corner_cycle = get_corner_cycle(alg);
      let misoriented_corner = match corner_cycle[1][1].num_rotations() {
        1 => corner_cycle[1][1].rotate().rotate(),
        2 => corner_cycle[1][1].rotate(),
        _ => unreachable!(),
      };
      div_with_attr(
        div_with_attr(
          div(a(
            alg_cubing_url(alg),
            format!(
              "{:?} [{:?}] {}",
              &corner_cycle[0][1..2],
              misoriented_corner,
              alg
            ),
          )),
          format!(" class='{:?}'", corner_cycle[1][1]),
        ),
        format!(" class='{:?}'", corner_cycle[0][1]),
      )
    }
    _ => unimplemented!(),
  }) + "\n"
}

const TEMPLATE: &str =
  include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/templates/main.html"));

fn filter_html(algs: &[Alg]) -> &'static str {
  match get_alg_category(&algs[0]) {
    Some(Category::CornerCycle3) => {
      r#"<input type="text" id="p0" size="3"></input>
         <input type="text" id="p1" size="3"></input>
         <input type="text" id="p2" size="3"></input>"#
    }
    Some(Category::EdgeCycle3) => {
      r#"<input type="text" id="p0" size="2"></input>
         <input type="text" id="p1" size="2"></input>
         <input type="text" id="p2" size="2"></input>"#
    }
    Some(Category::EdgeFlip) => "",
    Some(Category::Twist2) => "",
    Some(Category::Parity) => "",
    Some(Category::Ltct) => "",
    _ => unimplemented!(),
  }
}

fn gen_alg_list(
  algs: Vec<Alg>,
  letter_scheme: &Option<LetterScheme>,
) -> String {
  let algs_html = algs
    .iter()
    .map(|a| format_alg(a, letter_scheme))
    .collect::<String>();
  let filter_html = filter_html(&algs);
  let body = String::from(filter_html) + &algs_html;
  String::from(TEMPLATE).replace("BODY", &body)
}

fn get_corner_cycle(alg: &Alg) -> Vec<Vec<CornerPos>> {
  let mut c = StickerCube::solved();
  for m in alg.invert().iter() {
    c.do_move_mut(m);
  }

  get_piece_cycles::<CornerPos>(&c)
}

fn get_edge_cycle(alg: &Alg) -> Vec<Vec<EdgePos>> {
  let mut c = StickerCube::solved();
  for m in alg.invert().iter() {
    c.do_move_mut(m);
  }

  get_piece_cycles::<EdgePos>(&c)
}

fn read_algs() -> Result<Vec<Alg>, String> {
  let mut algs = vec![];

  loop {
    let mut alg = String::new();
    let res = std::io::stdin().read_line(&mut alg).unwrap();
    if res == 0 {
      break;
    }

    if alg.trim() == "" {
      continue;
    }

    let alg = parse_alg(&alg).map_err(|_e| format!("Bad alg: {}", alg))?;
    algs.push(alg);
  }

  Ok(algs)
}

fn all_equal<I: Iterator<Item = T>, T: PartialEq>(mut iter: I) -> bool {
  match iter.next() {
    None => true,
    Some(a) => iter.all(|x| a == x),
  }
}

fn all_same_category(algs: &[Alg]) -> bool {
  all_equal(algs.iter().map(|a| {
    std::mem::discriminant(
      &get_alg_category(a).expect("Should have a category!"),
    )
  }))
}

fn create_options() -> getopts::Options {
  let mut opts = getopts::Options::new();
  opts.optflag("h", "help", "print this help message");
  opts.optopt("", "scheme", "Load letter scheme from <file>", "FILE");
  opts
}

fn main() -> Result<(), String> {
  let opts = create_options();
  let args: Vec<String> = std::env::args().collect();
  let matches = match opts.parse(&args[1..]) {
    Ok(m) => m,
    Err(f) => return Err(f.to_string()),
  };

  if matches.opt_present("h") {
    let brief = format!("Usage: {} [options]", args[0]);
    println!("{}", opts.usage(&brief));
    return Ok(());
  }

  let algs = read_algs()?;
  assert!(all_same_category(&algs));

  let letter_scheme = matches.opt_str("scheme").map(|s| {
    let data = std::fs::read_to_string(s).expect("Unable to read file");
    json::from_str(&data).unwrap()
  });

  println!("{}", gen_alg_list(algs, &letter_scheme));

  Ok(())
}
