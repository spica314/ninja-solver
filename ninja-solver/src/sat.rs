use std::{collections::HashMap, fmt::{self, Debug}};

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


pub enum SatSolverResult {
    Unknown,
    Sat(HashMap<usize, bool>),
    Unsat,
}

pub enum SatSolverResultInner {
    Unknown,
    Sat(Vec<bool>),
    Unsat,
}

pub struct SatProblem {
    clauses: Vec<Clause>,
    outer_id_to_inner_id_map: HashMap<usize, usize>,
}

impl SatProblem {
    pub fn new() -> SatProblem {
        SatProblem {
            clauses: vec![],
            outer_id_to_inner_id_map: HashMap::new(),
        }
    }
    pub fn add_clause(&mut self, clause: &[(usize, bool)]) {
        let mut c = Clause::new();
        for &(id, sign) in clause {
            let next_id = self.outer_id_to_inner_id_map.len();
            let id2 = *self.outer_id_to_inner_id_map.entry(id).or_insert(next_id);
            c.push(Lit::new(id2, sign));
        }
        self.clauses.push(c);
    }
    pub fn solve(&self) -> SatSolverResult {
        let mut solver = SatSolver::new(self.outer_id_to_inner_id_map.len(), self.clauses.clone());
        match solver.solve() {
            SatSolverResultInner::Unknown => SatSolverResult::Unknown,
            SatSolverResultInner::Sat(xs) => {
                eprintln!("xs = {:?}", xs);
                let mut res = HashMap::new();
                for (&key, &value) in &self.outer_id_to_inner_id_map {
                    res.insert(key, xs[value]);
                }
                SatSolverResult::Sat(res)
            }
            SatSolverResultInner::Unsat => SatSolverResult::Unsat,
        }
    }
}

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
        eprintln!("unit_prop: assigns = {:?}, i = {}, sign = {}", self.assigns, i, sign);
        self.assigned[i] = Some(sign);
        let mut unit_prop = vec![];
        let mut fail_satisfy = false;
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
            eprintln!("clause = {:?}, satisfy_clause = {}, not_assigned_lit = {:?}", clause, satisfy_clause, not_assigned_count);
            if satisfy_clause {
                continue;
            }
            assert!(!satisfy_clause);
            if not_assigned_count >= 2 {
                continue;
            }
            if not_assigned_count == 1 {
                // unit prop
                let lit = *not_assigned_lit.unwrap();
                self.assigned[lit.id()] = Some(lit.sign());
                unit_prop.push(lit);
                continue;
            }
            assert!(not_assigned_count == 0);
            fail_satisfy = true;
            break;
        }
        if fail_satisfy {
            eprintln!("-> fail");
            self.assigned[i] = None;
            for lit in unit_prop {
                self.assigned[lit.id()] = None;
            }
            return None;
        }
        eprintln!("-> ok");
        Some((Lit::new(i, sign), unit_prop))
    }
    fn solve(&mut self) -> SatSolverResultInner {
        'lo: loop {
            eprintln!("assigns = {:?}", self.assigns);
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
    match res {
        SatSolverResult::Sat(xs) => {
            eprintln!("xs = {:?}", xs);
            assert!(xs[&0] && !xs[&1])
        }
        _ => panic!(),
    }
}
