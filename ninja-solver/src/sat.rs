use std::{collections::{BTreeSet, HashMap}, fmt::{self, Debug}};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct Lit(usize);

const LIT_ROOT: Lit = Lit(0);

impl Lit {
    pub fn new(id: usize, sign: bool) -> Lit {
        assert!(id >= 1);
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
    pub fn normalize(&mut self) {
        self.xs.sort();
        self.xs.dedup();
        if self.xs.len() == 0 {
            return;
        }
        for i in 1..self.xs.len() {
            if self.xs[i-1].id() == self.xs[i].id() && self.xs[i-1].sign() != self.xs[i].sign() {
                self.xs.clear();
                return;
            }
        }
    }
    pub fn merge_if_cross(&mut self, r: &Clause) {
        {
            let mut merge_flag = false;
            let mut i = 0;
            let mut k = 0;
            while i < self.xs.len() && k < r.xs.len() {
                if self.xs[i].id() < r.xs[k].id() {
                    i += 1;
                } else if self.xs[i].id() == r.xs[k].id() {
                    if self.xs[i].sign() != r.xs[k].sign() {
                        merge_flag = true;
                        break;
                    }
                    i += 1;
                    k += 1;
                } else {
                    k += 1;
                }
            }
            if !merge_flag {
                return;
            }
        }
        let mut res = vec![];
        let mut i = 0;
        let mut k = 0;
        while i < self.xs.len() && k < r.xs.len() {
            if self.xs[i].id() < r.xs[k].id() {
                res.push(self.xs[i]);
                i += 1;
            } else if self.xs[i].id() == r.xs[k].id() {
                if self.xs[i].sign() != r.xs[k].sign() {
                } else {
                    res.push(self.xs[i]);
                }
                i += 1;
                k += 1;
            } else {
                res.push(r.xs[k]);
                k += 1;
            }
        }
        while i < self.xs.len() {
            res.push(self.xs[i]);
            i += 1;
        }
        while k < r.xs.len() {
            res.push(r.xs[k]);
            k += 1;
        }
        self.xs = res;
        self.normalize();
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
        matches!(self, SatSolverResult::Unknown)
    }
    pub fn is_sat(&self) -> bool {
        matches!(self, SatSolverResult::Sat(_))
    }
    pub fn is_unsat(&self) -> bool {
        matches!(self, SatSolverResult::Unsat)
    }
}

#[derive(Debug, Clone)]
enum SatSolverResultInner {
    Unknown,
    Sat(Vec<bool>),
    Unsat,
}

#[derive(Debug, Clone, Default)]
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
            let next_id = self.outer_id_to_inner_id_map.len() + 1;
            let id2 = *self.outer_id_to_inner_id_map.entry(id).or_insert(next_id);
            self.inner_id_to_outer_id_map.insert(id2, id);
            c.push(Lit::new(id2, sign));
        }
        //c.normalize();
        //if !c.xs.is_empty() {
        //}
        self.clauses.push(c);
    }
    pub fn solve(&self) -> SatSolverResult {
        /*
        eprintln!("clauses: ");
        for clause in &self.clauses {
            eprintln!("    {:?}", clause);
        }
        */
        //eprintln!("clauses = {:?}", self.clauses);
        let mut solver = SatSolver::new(self.outer_id_to_inner_id_map.len(), self.clauses.clone());
        //eprintln!("solver = {:?}", solver);
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
            SatSolverResult::Unknown => false,
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
                            assert!(lit.id()-1 < n_var);
                            if (bits >> (lit.id()-1)) & 1 == lit.sign() as usize {
                                ok_clause = true;
                            }
                        }
                        if !ok_clause {
                            ok_cnf = false;
                        }
                    }
                    if ok_cnf {
                        eprintln!("bits = {:b}", bits);
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
    dicisions: Vec<(Lit, Vec<(Lit, usize)>)>,
    // sign, level
    assigned: Vec<Option<(bool, usize)>>,
    reason: Vec<Option<usize>>,
}

impl SatSolver {
    fn new(n_var: usize, clauses: Vec<Clause>) -> SatSolver {
        let mut clauses2 = vec![];
        for mut clause in clauses {
            clause.normalize();
            if !clause.xs.is_empty() {
                clauses2.push(clause);
            }
        }
        SatSolver {
            n_var: n_var + 1,
            clauses: clauses2,
            dicisions: vec![],
            assigned: vec![None; n_var + 1],
            reason: vec![None; n_var + 1],
        }
    }
    fn solve(&mut self) -> SatSolverResultInner {
        //eprintln!("------------------------------------------");
        self.clauses.sort();
        self.clauses.dedup();
        self.clauses.sort_by(|x,y| x.xs.len().cmp(&y.xs.len()));
        self.clauses.reverse();
        /*
        for clause in &self.clauses {
            eprintln!("    {:?}", clause);
        }
        */
        'lo: for _ in 0.. {
            //eprintln!();
            //eprintln!("dicisions = {:?}", self.dicisions);
            let level = self.dicisions.len();
            let i = {
                let mut i = 0;
                while i < self.assigned.len() && self.assigned[i].is_some() {
                    i += 1;
                }
                if i == self.assigned.len() {
                    break;
                }
                i
            };
            let lit = if i == 0 { LIT_ROOT } else { Lit::new(i, false) };
            //eprintln!("next_decision: lit = {:?}", lit);
            self.assigned[i] = Some((false, level));
            // unit_prop
            let mut unit_prop = vec![];
            loop {
                let mut updated = false;
                for (k, clause) in self.clauses.iter().enumerate().rev() {
                    let mut not_assigned_count = 0;
                    let mut not_assigned_lit = None;
                    let mut satisfy_clause = false;
                    for lit in clause.iter() {
                        if let Some((x, _)) = self.assigned[lit.id()] {
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
                        self.assigned[lit.id()] = Some((lit.sign(), level));
                        self.reason[lit.id()] = Some(k);
                        unit_prop.push((lit, k));
                        continue;
                    }
                    assert!(not_assigned_count == 0);
                    // conflict
                    //eprintln!("unit_prop conflict: lit = {:?}, unit_prop = {:?}, level = {}", lit, unit_prop, level);
                    if level == 0 {
                        return SatSolverResultInner::Unsat;
                    }
                    let mut clause = clause.clone();
                    for &(_, k) in unit_prop.iter().rev() {
                        //eprint!("{:?} & {:?} -> ", clause, &self.clauses[k]);
                        clause.merge_if_cross(&self.clauses[k]);
                        //eprintln!("{:?}", clause);
                    }
                    //eprintln!("new_clause = {:?}", clause);
                    //eprintln!("assignd = {:?}", self.assigned);
                    let mut max_level = 0;
                    for &lit2 in clause.iter() {
                        if let Some(t) = self.assigned[lit2.id()] {
                            if t.1 != level {
                                max_level = std::cmp::max(max_level, t.1);
                            }
                        } else {
                            panic!();
                        }
                    }
                    self.assigned[lit.id()] = None;
                    for &(lit2, _) in unit_prop.iter().rev() {
                        self.assigned[lit2.id()] = None;
                        self.reason[lit2.id()] = None;
                    }
                    let old = clause.clone();
                    clause.normalize();
                    if !clause.xs.is_empty() {
                        if !self.clauses.iter().any(|x| x == &clause) {
                            self.clauses.push(clause);
                        }
                    } else {
                        panic!("old = {:?}", old);
                    }
                    /*
                    eprintln!("clauses:");
                    for clause in &self.clauses {
                        eprintln!("    {:?}", clause);
                    }
                    */
                    while self.dicisions.len() > max_level {
                        if let Some((lit, unit_prop)) = self.dicisions.pop() {
                            self.assigned[lit.id()] = None;
                            for (lit, _) in unit_prop {
                                self.assigned[lit.id()] = None;
                            }
                        }
                    }
                    continue 'lo;
                }
                if !updated {
                    break;
                }
            }
            /* success */
            self.dicisions.push((lit, unit_prop));
            continue 'lo;
        }
        if !self.assigned.iter().all(|x| x.is_some()) {
            return SatSolverResultInner::Unknown;
        }
        let xs: Vec<_> = self.assigned.iter().map(|&x| x.unwrap().0).collect();
        SatSolverResultInner::Sat(xs)
    }
}

#[cfg(test)]
mod tests {
    use crate::rand::xorshift::XorShift128;
    use super::*;

    #[test]
    fn test_sat_solver_1() {
        let mut problem = SatProblem::new();
        problem.add_clause(&[(0, false), (1, false)]);
        problem.add_clause(&[(0, true)]);
        let res = problem.solve();
        problem.check_result(&res);
        match res {
            SatSolverResult::Sat(xs) => {
                eprintln!("xs = {:?}", xs);
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
        eprintln!("res = {:?}", res);
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
        eprintln!("res = {:?}", res);
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
        test_sat_solver_rand(3, 19, 300000);
    }

    #[test]
    fn test_sat_solver_rand_2() {
        test_sat_solver_rand(10, 48, 30000);
    }

    #[test]
    fn test_sat_solver_rand_3() {
        test_sat_solver_rand(15, 68, 1000);
    }

    #[test]
    fn test_sat_solver_rand_4() {
        test_sat_solver_rand(18, 80, 100);
    }
}
