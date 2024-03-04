use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::Rc;

// spell-checker:ignore fnode,gnode

#[derive(Clone, Debug)]
pub enum Edge {
    Terminal(bool),
    Inner(Rc<Node>),
}

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        use Edge::*;
        match (self, other) {
            (Terminal(l), Terminal(r)) => l == r,
            (Inner(l), Inner(r)) => Rc::ptr_eq(l, r),
            _ => false,
        }
    }
}
impl Eq for Edge {}

impl PartialOrd for Edge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Edge {
    fn cmp(&self, other: &Self) -> Ordering {
        use Edge::*;
        match (self, other) {
            (Terminal(l), Terminal(r)) => l.cmp(r),
            (Terminal(_), Inner(_)) => Ordering::Less,
            (Inner(_), Terminal(_)) => Ordering::Greater,
            (Inner(l), Inner(r)) => Rc::as_ptr(l).cmp(&Rc::as_ptr(r)),
        }
    }
}

impl Hash for Edge {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Edge::Terminal(v) => v.hash(state),
            Edge::Inner(v) => Rc::as_ptr(v).hash(state),
        }
    }
}

impl Edge {
    pub fn eval(&self, env: &[bool]) -> bool {
        match self {
            Edge::Terminal(b) => *b,
            Edge::Inner(node) => if env[node.level as usize] {
                &node.t
            } else {
                &node.e
            }
            .eval(env),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Node {
    /// Level number, must be less than `t.level` and `e.level` (given that
    /// these point to inner nodes)
    level: u32,
    /// Then edge
    t: Edge,
    /// Else edge
    e: Edge,
}

#[derive(Default, Debug)]
pub struct Manager {
    unique_table: HashMap<Node, Rc<Node>>,
    apply_not_cache: HashMap<Edge, Edge>,
    apply_and_cache: HashMap<(Edge, Edge), Edge>,
}

impl Manager {
    pub fn new() -> Self {
        Self::default()
    }

    fn unique_table_get_or_insert(&mut self, node: Node) -> Edge {
        Edge::Inner(match self.unique_table.entry(node.clone()) {
            Entry::Occupied(entry) => entry.get().clone(),
            Entry::Vacant(entry) => entry.insert(Rc::new(node)).clone(),
        })
    }

    pub fn get_var(&mut self, level: u32) -> Edge {
        self.unique_table_get_or_insert(Node {
            t: Edge::Terminal(true),
            e: Edge::Terminal(false),
            level,
        })
    }

    pub fn apply_and(&mut self, f: &Edge, g: &Edge) -> Edge {
        if f == g {
            return f.clone();
        }

        let fnode = match f {
            Edge::Terminal(false) => return Edge::Terminal(false),
            Edge::Terminal(true) => return g.clone(),
            Edge::Inner(node) => node,
        };
        let gnode = match g {
            Edge::Terminal(false) => return Edge::Terminal(false),
            Edge::Terminal(true) => return f.clone(),
            Edge::Inner(node) => node,
        };

        // ∧ is commutative, so we use a canonical form of the key to increase
        // cache efficiency
        let key = if f < g {
            (f.clone(), g.clone())
        } else {
            (g.clone(), f.clone())
        };
        if let Some(res) = self.apply_and_cache.get(&key) {
            return res.clone();
        }

        // cofactors with respect to the top variable
        let (ft, fe) = if fnode.level <= gnode.level {
            (&fnode.t, &fnode.e)
        } else {
            (f, f)
        };
        let (gt, ge) = if gnode.level <= fnode.level {
            (&gnode.t, &gnode.e)
        } else {
            (g, g)
        };

        let node = Node {
            t: self.apply_and(ft, gt),
            e: self.apply_and(fe, ge),
            level: std::cmp::min(fnode.level, gnode.level),
        };
        let res = self.unique_table_get_or_insert(node);

        self.apply_and_cache.insert(key, res.clone());

        res
    }

    pub fn apply_not(&mut self, f: &Edge) -> Edge {
        let fnode = match f {
            Edge::Terminal(t) => return Edge::Terminal(!t),
            Edge::Inner(n) => n,
        };

        if let Some(res) = self.apply_not_cache.get(f) {
            return res.clone();
        }

        let node = Node {
            t: self.apply_not(&fnode.t),
            e: self.apply_not(&fnode.e),
            level: fnode.level,
        };
        let res = self.unique_table_get_or_insert(node);

        self.apply_not_cache.insert(f.clone(), res.clone());

        res
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, PartialEq, Eq, Debug)]
    enum Formula {
        False,
        True,
        Var(u32),
        Not(Box<Formula>),
        And(Box<Formula>, Box<Formula>),
    }

    impl Formula {
        fn next(&mut self, num_vars: u32, depth: u32) -> bool {
            use Formula::*;
            match self {
                False => *self = True,
                True => {
                    *self = if num_vars > 0 {
                        Var(0)
                    } else if depth != 0 {
                        Not(Box::new(False))
                    } else {
                        return false;
                    }
                }
                Var(i) => {
                    *self = if *i + 1 < num_vars {
                        Var(*i + 1)
                    } else if depth != 0 {
                        Not(Box::new(False))
                    } else {
                        return false;
                    }
                }
                Not(f) => {
                    if !f.next(num_vars, depth - 1) {
                        *self = And(Box::new(False), Box::new(False))
                    }
                }
                And(f, g) => {
                    if !g.next(num_vars, depth - 1) {
                        **g = False;
                        if !f.next(num_vars, depth - 1) {
                            return false;
                        }
                    }
                }
            }
            true
        }

        fn build(&self, manager: &mut Manager) -> Edge {
            match self {
                Formula::False => Edge::Terminal(false),
                Formula::True => Edge::Terminal(true),
                Formula::Var(i) => manager.get_var(*i),
                Formula::Not(f) => {
                    let f = f.build(manager);
                    manager.apply_not(&f)
                }
                Formula::And(f, g) => {
                    let f = f.build(manager);
                    let g = g.build(manager);
                    manager.apply_and(&f, &g)
                }
            }
        }

        fn eval(&self, env: &[bool]) -> bool {
            match self {
                Formula::False => false,
                Formula::True => true,
                Formula::Var(i) => env[*i as usize],
                Formula::Not(f) => !f.eval(env),
                Formula::And(f, g) => f.eval(env) && g.eval(env),
            }
        }
    }

    #[test]
    fn test_3_vars_depth_3() {
        let mut manager = Manager::new();

        let mut formula = Formula::False;
        loop {
            let f = formula.build(&mut manager);
            for x1 in [false, true] {
                for x2 in [false, true] {
                    for x3 in [false, true] {
                        let env = [x1, x2, x3];
                        let expected = formula.eval(&env);
                        let actual = f.eval(&env);
                        if actual != expected {
                            panic!(
                                "Error for {formula:?} in {env:?}: expected {expected}, got {actual}\nDD: {f:?}"
                            );
                        }
                    }
                }
            }
            if !formula.next(3, 3) {
                break;
            }
        }
    }
}
