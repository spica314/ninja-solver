use std::{io::stdin, str::FromStr};
use std::io::Read;

use formats::dimacs::DIMACS;
use ninja_solver::*;
use sat::SatProblem;

fn main() {
    let mut stdin = stdin();
    let mut s = String::new();
    stdin.read_to_string(&mut s).unwrap();
    let dimacs = DIMACS::from_str(&s).unwrap();
    let mut problem = SatProblem::new();
    for clause in dimacs.clauses() {
        let mut xs  = vec![];
        for &lit in clause {
            if lit > 0 {
                xs.push((lit as usize, true));
            } else {
                xs.push(((-lit) as usize, false));
            }
        }
        problem.add_clause(&xs);
    }
    let res = problem.solve();
    eprintln!("res = {:?}", res);
}
