use alg_list_gen::{get_alg_category, Category, LetterScheme};
use cube::{parse_alg, Alg, CornerPos, EdgePos, StickerCube};
use kociemba::Kociemba;
use miniserde::{json, Deserialize};
use rand::prelude::SliceRandom;
use std::collections::HashMap;
use std::io::BufRead;

fn read_alg_list(file: &str) -> Result<Vec<Alg>, String> {
  let file = std::fs::File::open(file)
    .map_err(|_e| format!("Could not open file: {}", file))?;
  let lines = std::io::BufReader::new(file).lines();

  lines
    .filter_map(|l| {
      let Ok(l) = l else {
        return Some(Err(String::from("IO error")));
      };

      if l.trim() == "" {
        return None;
      }

      Some(parse_alg(&l).map_err(|_e| format!("Bad alg: {}", l)))
    })
    .collect()
}

struct TrainerAlg {
  alg: Alg,
  corner_cycles: Vec<Vec<CornerPos>>,
  edge_cycles: Vec<Vec<EdgePos>>,
}

impl TrainerAlg {
  fn to_memo(
    &self,
    letter_scheme: &LetterScheme,
    words: &HashMap<String, String>,
  ) -> String {
    match get_alg_category(&self.alg) {
      Some(Category::CornerCycle3) => {
        let p = letter_scheme
          .corner_pair(self.corner_cycles[0][1], self.corner_cycles[0][2]);
        words.get(&p).map(|s| s.as_str()).unwrap_or(&p).to_string()
      }
      Some(Category::EdgeCycle3) => {
        letter_scheme.edge_pair(self.edge_cycles[0][1], self.edge_cycles[0][2])
      }
      unhandled => {
        panic!("Unhandled category: {:?} for {}", unhandled, self.alg)
      }
    }
  }
}

fn into_trainer_algs(algs: Vec<Alg>) -> Vec<TrainerAlg> {
  algs
    .into_iter()
    .map(|alg| {
      let mut c = StickerCube::solved();
      for m in alg.invert().iter() {
        c.do_move_mut(m);
      }

      TrainerAlg {
        alg,
        corner_cycles: cycles::get_piece_cycles::<CornerPos>(&c),
        edge_cycles: cycles::get_piece_cycles::<EdgePos>(&c),
      }
    })
    .collect()
}

fn create_options() -> getopts::Options {
  let mut opts = getopts::Options::new();
  opts.optflag("h", "help", "print this help message");
  opts.optopt("", "scheme", "Load letter scheme from <file>", "FILE");
  opts.optopt("", "words", "Load words from <file>", "FILE");
  opts.optopt("", "algs", "Load algs to train from <file>", "FILE");
  opts.optopt("N", "", "N algs to train at a time ", "N");
  opts
}

fn load_json_opt<T: Deserialize>(
  matches: &getopts::Matches,
  opt: &str,
  default_filename: &str,
) -> Result<T, String> {
  let file = matches
    .opt_str(opt)
    .unwrap_or_else(|| String::from(default_filename));
  let data = std::fs::read_to_string(&file)
    .map_err(|_| format!("Could not read {}", file))?;
  json::from_str(&data).map_err(|_| String::from("Could not parse json"))
}

fn wait_for_enter() {
  let mut buf = String::new();
  std::io::stdin().read_line(&mut buf).unwrap();
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

  let n = matches
    .opt_get_default("N", 3)
    .map_err(|_| String::from("invalid integer for N"))?;

  let words: HashMap<String, String> =
    load_json_opt(&matches, "words", "words.json").unwrap_or_default();

  let letter_scheme: LetterScheme =
    load_json_opt(&matches, "scheme", "scheme.json")?;

  let alg_file = matches
    .opt_str("algs")
    .ok_or_else(|| String::from("No algs file provided"))?;
  let algs = read_alg_list(&alg_file)?;
  let mut algs = into_trainer_algs(algs);
  algs.shuffle(&mut rand::thread_rng());

  let k = Kociemba::new();

  while !algs.is_empty() {
    let mut c = StickerCube::solved();

    let split = if algs.len() >= n { algs.len() - n } else { 0 };
    let train = algs.split_off(split);

    for alg in train.iter().rev() {
      for m in alg.alg.invert().iter() {
        c.do_move_mut(m.clone());
      }
    }

    let memo: Vec<_> = train
      .iter()
      .map(|alg| alg.to_memo(&letter_scheme, &words))
      .collect();

    println!("{}", k.solve(c).invert().normalise_half_turns());

    println!("{}", memo.join("\n"));

    wait_for_enter();
  }

  Ok(())
}
