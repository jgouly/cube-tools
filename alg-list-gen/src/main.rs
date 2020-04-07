use alg_list_gen::{get_alg_category, Category};
use cube::{parse_alg, Alg, CornerPos, EdgePos, StickerCube};
use cycles::get_piece_cycles;

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
  (match get_alg_category(alg) {
    Some(Category::CornerCycle3) => {
      let cycle = get_corner_cycle(alg);
      div_with_attr(
        div_with_attr(
          div_with_attr(
            div(a(alg_cubing_url(alg), format!("{:?} {}", cycle, alg))),
            format!(" class='{:?}'", cycle[0][2]),
          ),
          format!(" class='{:?}'", cycle[0][1]),
        ),
        format!(" class='{:?}'", cycle[0][0]),
      )
    }
    Some(Category::EdgeCycle3) => {
      let cycle = get_edge_cycle(alg);
      div_with_attr(
        div_with_attr(
          div_with_attr(
            div(a(alg_cubing_url(alg), format!("{:?} {}", cycle, alg))),
            format!(" class='{:?}'", cycle[0][2]),
          ),
          format!(" class='{:?}'", cycle[0][1]),
        ),
        format!(" class='{:?}'", cycle[0][0]),
      )
    },
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
    _ => unimplemented!(),
  }
}

fn gen_alg_list(algs: Vec<Alg>) -> String {
  let algs_html = algs.iter().map(format_alg).collect::<String>();
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
  all_equal(
    algs
      .iter()
      .map(|a| std::mem::discriminant(&get_alg_category(a))),
  )
}

fn main() -> Result<(), String> {
  let algs = read_algs()?;
  assert!(all_same_category(&algs));
  println!("{}", gen_alg_list(algs));

  Ok(())
}
