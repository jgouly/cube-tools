use alg_list_gen::LetterScheme;
use cube::{parse_alg, Alg, CornerPos, StickerCube};
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
      let Ok(l) = l else { return Some(Err(String::from("IO error"))); };

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
        corner_cycles: cycles::get_piece_cycles::<cube::CornerPos>(&c),
      }
    })
    .collect()
}

fn create_options() -> getopts::Options {
  let mut opts = getopts::Options::new();
  opts.optflag("h", "help", "print this help message");
  opts.optopt("", "scheme", "Load letter scheme from <file>", "FILE");
  opts.optopt("", "words", "Load words from <file>", "FILE");
  opts.optflag("", "corners", "Train corner algs");
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

  if !matches.opt_present("corners") {
    return Err(String::from("alg-trainer only supports corner algs"));
  }

  let n = matches
    .opt_get_default("N", 3)
    .map_err(|_| String::from("invalid integer for N"))?;

  let words: HashMap<String, String> =
    load_json_opt(&matches, "words", "words.json")?;

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

    let letters: Vec<_> = train
      .iter()
      .map(|alg| {
        letter_scheme
          .corner_pair(alg.corner_cycles[0][1], alg.corner_cycles[0][2])
      })
      .collect();

    println!("{}", k.solve(c).invert());

    let words: Vec<&str> = letters
      .iter()
      .map(|p| words.get(p).map(|s| s.as_str()).unwrap_or(&p))
      .collect();
    println!("{}", words.join("\n"));

    wait_for_enter();
  }

  Ok(())
}
