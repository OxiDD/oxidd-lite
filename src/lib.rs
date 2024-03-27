//! Simple implementation of binary decision diagrams (BDDs) using an
//! index-based edge representation

#![warn(missing_docs)]

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;

// spell-checker:ignore fnode,gnode

/// Edge pointing to an inner or terminal node
//
// Note: We only need some arbitrary total ordering on `Edge`s. This avoids
// having both f ∧ g and g ∧ f separately in the apply cache.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Edge(u32);

impl Edge {
    const NUM_TERMINALS: u32 = 2;

    /// Get an edge pointing to the given terminal node (`value`)
    pub fn to_terminal(value: bool) -> Self {
        Self(value as u32)
    }

    /// Get an edge pointing to the inner node at `index`
    fn to_inner_node(index: u32) -> Self {
        Self(index + Self::NUM_TERMINALS)
    }

    /// Get the terminal node value of this edge or [`None`] if this edge points
    /// to an inner node
    pub fn terminal_value(self) -> Option<bool> {
        if self.0 == 0 {
            Some(false)
        } else if self.0 == 1 {
            Some(true)
        } else {
            None
        }
    }

    /// Get the inner node index of this edge
    fn inner_node_index(self) -> Option<u32> {
        if self.0 >= 2 {
            Some(self.0 - Self::NUM_TERMINALS)
        } else {
            None
        }
    }
}

/// Inner node of the decision diagram
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

/// Manager responsible for storing nodes and ensuring their uniqueness
#[derive(Default, Debug)]
pub struct Manager {
    node_store: Vec<Node>,
    unique_table: HashMap<Node, Edge>,
    apply_not_cache: HashMap<Edge, Edge>,
    apply_and_cache: HashMap<(Edge, Edge), Edge>,
}

impl Manager {
    /// Create a new `Manager`
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the inner node for edge `f`
    ///
    /// `f` must belong to this manager, otherwise the `get_node()` might panic.
    /// Also, `get_node` will panic if `f` points to a terminal node.
    pub fn get_node(&self, f: Edge) -> Node {
        self.node_store[f.inner_node_index().unwrap() as usize]
    }

    /// Evaluate the Boolean function represented by `f` with the given
    /// `valuation`. If `valuation[i]` is true, then the variable at level `i`
    /// is set to `true`, otherwise it is `false`.
    pub fn eval(&self, f: Edge, valuation: &[bool]) -> bool {
        if let Some(v) = f.terminal_value() {
            v
        } else {
            let node = self.get_node(f);
            self.eval(
                if valuation[node.level as usize] {
                    node.t
                } else {
                    node.e
                },
                valuation,
            )
        }
    }

    /// Apply the BDD reduction rules to `node` and return an `Edge` pointing to
    /// the resulting node or [`None`] in case of an out-of-memory situation
    ///
    /// The outgoing edges of `node` must belong to this manager.
    fn reduce(&mut self, level: u32, then_edge: Edge, else_edge: Edge) -> Option<Edge> {
        if then_edge == else_edge {
            return Some(then_edge);
        }
        let node = Node {
            level,
            t: then_edge,
            e: else_edge,
        };
        Some(match self.unique_table.entry(node) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let idx = self.node_store.len();
                if idx >= (1usize << u32::BITS) {
                    return None; // out of memory
                }
                let idx = idx as u32;
                let edge = Edge::to_inner_node(idx);
                self.node_store.push(node);
                *entry.insert(edge)
            }
        })
    }

    /// Get the Boolean function for the variable at level `level`
    ///
    /// Returns [`None`] in an out-of-memory situation
    pub fn get_var(&mut self, level: u32) -> Option<Edge> {
        self.reduce(level, Edge::to_terminal(true), Edge::to_terminal(false))
    }

    /// Compute the conjunction of the Boolean functions represented by `f` and
    /// `g`
    ///
    /// Returns [`None`] in an out-of-memory situation.
    ///
    /// `f` and `g` must belong to this manager.
    pub fn apply_and(&mut self, f: Edge, g: Edge) -> Option<Edge> {
        if f == g {
            return Some(f);
        }

        match (f.terminal_value(), g.terminal_value()) {
            (Some(false), _) | (_, Some(false)) => return Some(Edge::to_terminal(false)),
            (Some(true), _) => return Some(g),
            (_, Some(true)) => return Some(f),
            (None, None) => {}
        }

        // ∧ is commutative, so we use a canonical form of the key to increase
        // cache efficiency
        let key = if f < g { (f, g) } else { (g, f) };
        if let Some(res) = self.apply_and_cache.get(&key) {
            return Some(*res);
        }

        let fnode = self.get_node(f);
        let gnode = self.get_node(g);
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

        let level = std::cmp::min(fnode.level, gnode.level);
        let then_edge = self.apply_and(ft, gt)?;
        let else_edge = self.apply_and(fe, ge)?;
        let res = self.reduce(level, then_edge, else_edge)?;

        self.apply_and_cache.insert(key, res);

        Some(res)
    }

    /// Compute the negation of the Boolean functions represented by `f`
    ///
    /// Returns [`None`] in an out-of-memory situation.
    ///
    /// `f` must belong to this manager.
    pub fn apply_not(&mut self, f: Edge) -> Option<Edge> {
        if let Some(t) = f.terminal_value() {
            return Some(Edge::to_terminal(!t));
        }

        if let Some(res) = self.apply_not_cache.get(&f) {
            return Some(*res);
        }

        let fnode = self.get_node(f);
        let then_edge = self.apply_not(fnode.t)?;
        let else_edge = self.apply_not(fnode.e)?;
        let res = self.reduce(fnode.level, then_edge, else_edge)?;

        self.apply_not_cache.insert(f, res);

        Some(res)
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

        fn build(&self, manager: &mut Manager) -> Option<Edge> {
            match self {
                Formula::False => Some(Edge::to_terminal(false)),
                Formula::True => Some(Edge::to_terminal(true)),
                Formula::Var(i) => manager.get_var(*i),
                Formula::Not(f) => {
                    let f = f.build(manager)?;
                    manager.apply_not(f)
                }
                Formula::And(f, g) => {
                    let f = f.build(manager)?;
                    let g = g.build(manager)?;
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
            let f = formula.build(&mut manager).unwrap();
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
