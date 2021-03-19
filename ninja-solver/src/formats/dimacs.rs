//! struct for DIMACS format
//!
//! reference: <http://www.satcompetition.org/2009/format-benchmarks2009.html>

use std::str::FromStr;
use std::convert::TryFrom;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct DIMACS {
    comments: Vec<String>,
    n_var: usize,
    clauses: Vec<Vec<i64>>,
}

impl DIMACS {
    pub fn new() -> DIMACS {
        DIMACS {
            comments: vec![],
            n_var: 0,
            clauses: vec![],
        }
    }
    pub fn n_var(&self) -> usize {
        self.n_var
    }
    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }
    pub fn clauses(&self) -> &Vec<Vec<i64>> {
        &self.clauses
    }
    pub fn push_clause(&mut self, clause: Vec<i64>) {
        for lit in &clause {
            self.n_var = std::cmp::max(self.n_var, usize::try_from(lit.abs()).unwrap());
        }
        self.clauses.push(clause);
    }
}

impl FromStr for DIMACS {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut comments = vec![];
        let mut n_var = None;
        let mut n_clauses = None;
        let mut clauses = vec![];
        for line in s.lines() {
            // skip blank line
            if line.chars().all(|c| c.is_whitespace()) {
                continue;
            }
            // comment
            if line.starts_with('c') {
                comments.push(line[2..].to_string());
                continue;
            }
            // n_var and n_clauses
            if line.starts_with("p cnf") {
                let ts: Vec<_> = line.split(' ').collect();
                if ts.len() != 4 {
                    return Err(());
                }
                if let Ok(m) = ts[2].parse::<usize>() {
                    n_var = Some(m);
                } else {
                    return Err(());
                }
                if let Ok(m) = ts[3].parse::<usize>() {
                    n_clauses = Some(m);
                }
                continue;
            }
            // clause
            let mut ts = vec![];
            for t in line.split(' ') {
                if let Ok(x) = t.parse::<i64>() {
                    if x != 0 {
                        ts.push(x);
                    }
                } else {
                    return Err(());
                }
            }
            clauses.push(ts);
        }
        if n_var.is_none() {
            return Err(());
        }
        let n_var = n_var.unwrap();
        if n_clauses.is_none() {
            return Err(());
        }
        let n_clauses = n_clauses.unwrap();
        if n_clauses != clauses.len() {
            return Err(());
        }
        Ok(DIMACS {
            comments,
            n_var,
            clauses,
        })
    }
}

impl ToString for DIMACS {
    fn to_string(&self) -> String {
        let mut res = String::new();
        for comment in &self.comments {
            res.push_str("c ");
            res.push_str(comment);
            res.push('\n');
        }
        res.push_str(&format!("p cnf {} {}\n", self.n_var, self.clauses.len()));
        for clause in &self.clauses {
            res.push_str(&format!("{}", clause[0]));
            for &lit in &clause[1..] {
                res.push_str(&format!(" {}", lit));
            }
            res.push_str(" 0\n");
        }
        res
    }
}

#[test]
fn dimacs_test_1() {
    let s = r#"c test comment
c test comment2
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0
"#;
    let right = DIMACS {
        comments: vec![
            "test comment".to_string(),
            "test comment2".to_string(),
        ],
        n_var: 5,
        clauses: vec![
            vec![1, -5, 4],
            vec![-1, 5, 3, 4],
            vec![-3, -4],
        ],
    };
    assert_eq!(DIMACS::from_str(&s).unwrap(), right);
    assert_eq!(right.to_string(), s);
}
