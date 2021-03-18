use std::{collections::HashMap, fmt::{self, Debug}, unimplemented};

use crate::rand::xorshift::XorShift128;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct Lit(usize);

impl Lit {
    pub fn new(id: usize, sign: bool) -> Lit {
        if sign {
            Lit((id << 1) | 1)
        } else {
            Lit(id << 1)
        }
    }
    pub fn id(self) -> usize {
        self.0 >> 1
    }
    pub fn sign(self) -> bool {
        self.0 & 1 != 0
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lit")
            .field("id", &self.id())
            .field("sign", &self.sign())
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct Clause {
    xs: Vec<Lit>,
}

impl Clause {
    pub fn new() -> Clause {
        Clause {
            xs: vec![],
        }
    }
    pub fn push(&mut self, lit: Lit) {
        self.xs.push(lit);
    }
    pub fn iter(&self) -> impl Iterator<Item=&Lit> {
        self.xs.iter()
    }
}


#[derive(Debug, Clone)]
pub enum SatSolverResult {
    Unknown,
    Sat(HashMap<usize, bool>),
    Unsat,
}

impl SatSolverResult {
    pub fn is_unknown(&self) -> bool {
        match self {
            SatSolverResult::Unknown => true,
            _ => false,
        }
    }
    pub fn is_sat(&self) -> bool {
        match self {
            SatSolverResult::Sat(_) => true,
            _ => false,
        }
    }
    pub fn is_unsat(&self) -> bool {
        match self {
            SatSolverResult::Unsat => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum SatSolverResultInner {
    Unknown,
    Sat(Vec<bool>),
    Unsat,
}

#[derive(Debug, Clone)]
pub struct SatProblem {
    clauses: Vec<Clause>,
    outer_id_to_inner_id_map: HashMap<usize, usize>,
    inner_id_to_outer_id_map: HashMap<usize, usize>,
}

impl SatProblem {
    pub fn new() -> SatProblem {
        SatProblem {
            clauses: vec![],
            outer_id_to_inner_id_map: HashMap::new(),
            inner_id_to_outer_id_map: HashMap::new(),
        }
    }
    pub fn add_clause(&mut self, clause: &[(usize, bool)]) {
        let mut c = Clause::new();
        for &(id, sign) in clause {
            let next_id = self.outer_id_to_inner_id_map.len();
            let id2 = *self.outer_id_to_inner_id_map.entry(id).or_insert(next_id);
            self.inner_id_to_outer_id_map.insert(id2, id);
            c.push(Lit::new(id2, sign));
        }
        self.clauses.push(c);
    }
    pub fn solve(&self) -> SatSolverResult {
        let mut solver = SatSolver::new(self.outer_id_to_inner_id_map.len(), self.clauses.clone());
        match solver.solve() {
            SatSolverResultInner::Unknown => SatSolverResult::Unknown,
            SatSolverResultInner::Sat(xs) => {
                //eprintln!("xs = {:?}", xs);
                let mut res = HashMap::new();
                for (&key, &value) in &self.outer_id_to_inner_id_map {
                    res.insert(key, xs[value]);
                }
                SatSolverResult::Sat(res)
            }
            SatSolverResultInner::Unsat => SatSolverResult::Unsat,
        }
    }
    pub fn check_result(&self, res: &SatSolverResult) -> bool {
        let n_var = self.outer_id_to_inner_id_map.len();
        match res {
            SatSolverResult::Unknown => true,
            SatSolverResult::Sat(xs) => {
                let mut ok_cnf = true;
                for clause in &self.clauses {
                    let mut ok_clause = false;
                    for lit in clause.iter() {
                        if xs[&self.inner_id_to_outer_id_map[&lit.id()]] == lit.sign() {
                            ok_clause = true;
                        }
                    }
                    if !ok_clause {
                        eprintln!("error clause = {:?}", clause);
                        ok_cnf = false;
                    }
                }
                ok_cnf
            }
            SatSolverResult::Unsat => {
                for bits in 0..1<<n_var {
                    let mut ok_cnf = true;
                    for clause in &self.clauses {
                        let mut ok_clause = false;
                        for lit in clause.iter() {
                            if (bits >> self.inner_id_to_outer_id_map[&lit.id()]) & 1 == lit.sign() as usize{
                                ok_clause = true;
                            }
                        }
                        if !ok_clause {
                            ok_cnf = false;
                        }
                    }
                    if ok_cnf {
                        return false;
                    }
                }
                true
            }
        }
    }
}

#[derive(Debug, Clone)]
struct SatSolver {
    n_var: usize,
    clauses: Vec<Clause>,
    assigns: Vec<(Lit, Vec<Lit>)>,
    assigned: Vec<Option<bool>>,
}

impl SatSolver {
    fn new(n_var: usize, clauses: Vec<Clause>) -> SatSolver {
        SatSolver {
            n_var,
            clauses,
            assigns: vec![],
            assigned: vec![None; n_var],
        }
    }
    fn unit_prop(&mut self, i: usize, sign: bool) -> Option<(Lit, Vec<Lit>)> {
        //eprintln!("unit_prop: assigns = {:?}, i = {}, sign = {}", self.assigns, i, sign);
        self.assigned[i] = Some(sign);
        let mut unit_prop = vec![];
        let mut fail_satisfy = false;
        loop {
            let mut updated = false;
            for clause in &self.clauses {
                let mut not_assigned_count = 0;
                let mut not_assigned_lit = None;
                let mut satisfy_clause = false;
                for lit in clause.iter() {
                    if let Some(x) = self.assigned[lit.id()] {
                        if lit.sign() == x {
                            satisfy_clause = true;
                            break;
                        }
                    } else {
                        not_assigned_count += 1;
                        not_assigned_lit = Some(lit);
                    }
                }
                //eprintln!("clause = {:?}, satisfy_clause = {}, not_assigned_lit = {:?}", clause, satisfy_clause, not_assigned_count);
                if satisfy_clause {
                    continue;
                }
                assert!(!satisfy_clause);
                if not_assigned_count >= 2 {
                    continue;
                }
                if not_assigned_count == 1 {
                    // unit prop
                    updated = true;
                    let lit = *not_assigned_lit.unwrap();
                    self.assigned[lit.id()] = Some(lit.sign());
                    unit_prop.push(lit);
                    continue;
                }
                assert!(not_assigned_count == 0);
                //eprintln!("-> fail");
                self.assigned[i] = None;
                for lit in unit_prop {
                    self.assigned[lit.id()] = None;
                }
                return None;
            }
            if !updated {
                break;
            }
        }
        //eprintln!("-> ok");
        Some((Lit::new(i, sign), unit_prop))
    }
    fn solve(&mut self) -> SatSolverResultInner {
        'lo: loop {
            //eprintln!("assigns = {:?}", self.assigns);
            let mut i = 0;
            while i < self.assigned.len() && self.assigned[i].is_some() {
                i += 1;
            }
            if i == self.assigned.len() {
                break;
            }
            if let Some((lit, unit_prop)) = self.unit_prop(i, false) {
                self.assigns.push((lit, unit_prop));
            } else if let Some((lit, unit_prop)) = self.unit_prop(i, true) {
                self.assigns.push((lit, unit_prop));
            } else {
                // backtrack
                while let Some((lit, unit_prop)) = self.assigns.pop() {
                    self.assigned[lit.id()] = None;
                    for lit in unit_prop {
                        self.assigned[lit.id()] = None;
                    }
                    if lit.sign() {
                        continue;
                    } else {
                        if let Some((lit, unit_prop)) = self.unit_prop(lit.id(), true) {
                            self.assigns.push((lit, unit_prop));
                            continue 'lo;
                        } else {
                            continue;
                        }
                    }
                }
                return SatSolverResultInner::Unsat;
            }
        }
        let xs: Vec<_> = self.assigned.iter().map(|&x| x.unwrap()).collect();
        SatSolverResultInner::Sat(xs)
    }
}

#[test]
fn test_sat_solver_1() {
    let mut problem = SatProblem::new();
    problem.add_clause(&[(0, false), (1, false)]);
    problem.add_clause(&[(0, true)]);
    let res = problem.solve();
    problem.check_result(&res);
    match res {
        SatSolverResult::Sat(xs) => {
            // eprintln!("xs = {:?}", xs);
            assert!(xs[&0] && !xs[&1])
        }
        _ => panic!(),
    }
}

#[test]
fn test_sat_solver_2() {
    let mut problem = SatProblem::new();
    problem.add_clause(&[(1, false), (1, true)]);
    problem.add_clause(&[(0, true)]);
    let res = problem.solve();
    problem.check_result(&res);
}

#[test]
fn test_sat_solver_3() {
    let mut problem = SatProblem::new();
    problem.add_clause(&[(0, true),  (1, false), (1, false)]);
    problem.add_clause(&[(1, true),  (2, false), (2, true)]);
    problem.add_clause(&[(0, true),  (0, true),  (2, true)]);
    problem.add_clause(&[(1, false), (2, false), (1, true)]);
    problem.add_clause(&[(0, true),  (2, false), (1, true)]);
    let res = problem.solve();
    assert!(problem.check_result(&res));
    //eprintln!("res = {:?}", res);
}

fn test_sat_solver_rand(n_var: usize, n_clause: usize, n_test: usize) {
    let mut rand = XorShift128::new();
    let gen_random_lit = |rand: &mut XorShift128| {
        (rand.gen_mod(n_var), rand.gen_mod(2) != 0)
    };
    let mut count_unknown = 0;
    let mut count_sat = 0;
    let mut count_unsat = 0;
    for test_id in 0..n_test {
        let mut problem = SatProblem::new();
        for _ in 0..n_clause {
            let a = gen_random_lit(&mut rand);
            let b = gen_random_lit(&mut rand);
            let c = gen_random_lit(&mut rand);
            problem.add_clause(&[a, b, c]);
        }
        let res = problem.solve();
        if res.is_unknown() {
            count_unknown += 1;
        }
        if res.is_sat() {
            count_sat += 1;
        }
        if res.is_unsat() {
            count_unsat += 1;
        }
        assert!(problem.check_result(&res), "test_id = {}, problem = {:?}, res = {:?}", test_id, problem, res);
    }
    eprintln!("n_var = {}, n_clause = {}, sat = {}, unsat = {}, unknown = {}", n_var, n_clause, count_sat, count_unsat, count_unknown);
}

#[test]
fn test_sat_solver_rand_1() {
    test_sat_solver_rand(3, 19, 1000);
}

#[test]
fn test_sat_solver_rand_2() {
    test_sat_solver_rand(10, 48, 1000);
}

#[test]
fn test_sat_solver_rand_3() {
    test_sat_solver_rand(15, 68, 200);
}
