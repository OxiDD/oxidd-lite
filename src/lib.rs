use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;

// spell-checker:ignore fnode,gnode

// Note: We only need some arbitrary total ordering on `Edge`s. This avoids
// having both f ∧ g and g ∧ f separately in the apply cache.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Edge(u32);

impl Edge {
    const NUM_TERMINALS: u32 = 2;

    pub fn to_terminal(value: bool) -> Self {
        Self(value as u32)
    }

    fn to_inner_node(index: u32) -> Self {
        Self(index + Self::NUM_TERMINALS)
    }

    pub fn terminal_value(self) -> Option<bool> {
        if self.0 == 0 {
            Some(false)
        } else if self.0 == 1 {
            Some(true)
        } else {
            None
        }
    }

    fn inner_node_index(self) -> Option<u32> {
        if self.0 >= 2 {
            Some(self.0 - Self::NUM_TERMINALS)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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
    node_store: Vec<Node>,
    unique_table: HashMap<Node, Edge>,
    apply_not_cache: HashMap<Edge, Edge>,
    apply_and_cache: HashMap<(Edge, Edge), Edge>,
}

impl Manager {
    pub fn new() -> Self {
        Self::default()
    }

    /// Panics if self points to
    pub fn get_node(&self, f: Edge) -> Node {
        self.node_store[f.inner_node_index().unwrap() as usize]
    }

    pub fn eval(&self, f: Edge, env: &[bool]) -> bool {
        if let Some(v) = f.terminal_value() {
            v
        } else {
            let node = self.get_node(f);
            self.eval(
                if env[node.level as usize] {
                    node.t
                } else {
                    node.e
                },
                env,
            )
        }
    }

    fn unique_table_get_or_insert(&mut self, node: Node) -> Edge {
        match self.unique_table.entry(node) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let idx = self.node_store.len() as u32;
                let edge = Edge::to_inner_node(idx);
                self.node_store.push(node);
                *entry.insert(edge)
            }
        }
    }

    pub fn get_var(&mut self, level: u32) -> Edge {
        self.unique_table_get_or_insert(Node {
            t: Edge::to_terminal(true),
            e: Edge::to_terminal(false),
            level,
        })
    }

    pub fn apply_and(&mut self, f: Edge, g: Edge) -> Edge {
        if f == g {
            return f;
        }

        match (f.terminal_value(), g.terminal_value()) {
            (Some(false), _) | (_, Some(false)) => return Edge::to_terminal(false),
            (Some(true), _) => return g,
            (_, Some(true)) => return f,
            (None, None) => {}
        }
        let fnode = self.get_node(f);
        let gnode = self.get_node(g);

        // ∧ is commutative, so we use a canonical form of the key to increase
        // cache efficiency
        let key = if f < g { (f, g) } else { (g, f) };
        if let Some(res) = self.apply_and_cache.get(&key) {
            return *res;
        }

        // cofactors with respect to the top variable
        let (ft, fe) = if fnode.level <= gnode.level {
            (fnode.t, fnode.e)
        } else {
            (f, f)
        };
        let (gt, ge) = if gnode.level <= fnode.level {
            (gnode.t, gnode.e)
        } else {
            (g, g)
        };

        let node = Node {
            t: self.apply_and(ft, gt),
            e: self.apply_and(fe, ge),
            level: std::cmp::min(fnode.level, gnode.level),
        };
        let res = self.unique_table_get_or_insert(node);

        self.apply_and_cache.insert(key, res);

        res
    }

    pub fn apply_not(&mut self, f: Edge) -> Edge {
        let fnode = match f.terminal_value() {
            Some(t) => return Edge::to_terminal(!t),
            None => self.get_node(f),
        };

        if let Some(res) = self.apply_not_cache.get(&f) {
            return *res;
        }

        let node = Node {
            t: self.apply_not(fnode.t),
            e: self.apply_not(fnode.e),
            level: fnode.level,
        };
        let res = self.unique_table_get_or_insert(node);

        self.apply_not_cache.insert(f, res);

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
                Formula::False => Edge::to_terminal(false),
                Formula::True => Edge::to_terminal(true),
                Formula::Var(i) => manager.get_var(*i),
                Formula::Not(f) => {
                    let f = f.build(manager);
                    manager.apply_not(f)
                }
                Formula::And(f, g) => {
                    let f = f.build(manager);
                    let g = g.build(manager);
                    manager.apply_and(f, g)
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
                        let actual = manager.eval(f, &env);
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
