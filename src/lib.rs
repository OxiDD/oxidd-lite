extern crate creusot_contracts;
// TODO: when importing everything from creusot_contracts
// there seems to be name clash with respect to things imported
// from other creates
use creusot_contracts::{std, Clone, PartialEq, logic, *};

use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;

// spell-checker:ignore fnode,gnode

// Note: We only need some arbitrary total ordering on `Edge`s. This avoids
// having both f ∧ g and g ∧ f separately in the apply cache.
// Note 2: Since we are forced to implement trait OrdLogic, that speaks
// about this total order, we would need to define ourselves this relation
// to guarantee that both orders coincide
// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Edge(u32);

impl ShallowModel for Edge {
    type ShallowModelTy = Int;
    
    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0.shallow_model()
    }
}

impl PartialOrd for Edge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Edge {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0, other.0) {
            (a, b) if a < b => Ordering::Less,
            (a, b) if a > b => Ordering::Greater,
            _               => Ordering::Equal,
        }
    }
}


impl Edge {
    const NUM_TERMINALS: u32 = 2;

    pub fn to_terminal(value: bool) -> Self {
        Self(value as u32)
    }

    // To avoid overflow
    #[requires(index <= u32::MAX - Self::NUM_TERMINALS)]
    fn to_inner_node(index: u32) -> Self {
        Self(index + Self::NUM_TERMINALS)
    }

    #[ensures(self.0@ >= 2 ==> result == None)]
    #[ensures(result == None ==> self.0@ >= 2)]
    pub fn terminal_value(self) -> Option<bool> {
        if self.0 == 0 {
            Some(false)
        } else if self.0 == 1 {
            Some(true)
        } else {
            None
        }
    }

    
    #[ensures(self.0@ >= 2 ==> result != None)]
    // TODO: forced to do this; otherwise: ShallowModel for Option(u32)
    #[ensures(self.0@ >= 2 ==> 
              match result {
                  Some(x) => x@ == self.0@ - Self::NUM_TERMINALS@,
                  None    => false
              })]
    fn inner_node_index(self) -> Option<u32> {
        if self.0 >= 2 { // TODO: NUM_TERMINALS?
            Some(self.0 - Self::NUM_TERMINALS)
        } else {
            None
        }
    }
}

// Creusot requirements:
// DeepModel for Edge
// From creusot's source:
// "The deep model corresponds to the model used for specifying
// operations such as equality, hash function or ordering, which are
// computed deeply in a data structure."
impl DeepModel for Edge {
    type DeepModelTy = Edge;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

// Creusot requirement: OrdLogic trait for Edge
// defined in https://github.com/creusot-rs/creusot/blob/master/creusot-contracts/src/logic/ord.rs
impl OrdLogic for Edge {

    #[logic]
    #[open]
    fn cmp_log(self, other : Self) -> Ordering {
        // TODO: use a match?
        if self.0 < other.0 {
            Ordering::Less
        } else if self.0 > other.0 {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    #[logic]
    #[open]
    fn le_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Greater }
    }

    #[law]
    #[open]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self) {
        ()
    }

    #[logic]
    #[open]
    fn lt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Less }
    }

    #[law]
    #[open]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    fn cmp_lt_log(x: Self, y: Self) {
        ()
    }

    #[logic]
    #[open]
    fn ge_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Less }
    }

    #[law]
    #[open]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    fn cmp_ge_log(x: Self, y: Self) {
        ()
    }

    #[logic]
    #[open]
    fn gt_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) == Ordering::Greater }
    }

    #[law]
    #[open]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    fn cmp_gt_log(x: Self, y: Self) {
        ()
    }

    #[law]
    #[open]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    fn refl(x: Self) {
        ()
    }

    #[law]
    #[open]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {
        ()
    }

    #[law]
    #[open]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    fn antisym1(x: Self, y: Self) {
        ()
    }

    #[law]
    #[open]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    fn antisym2(x: Self, y: Self) {
        ()
    }

    #[law]
    #[open]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    fn eq_cmp(x: Self, y: Self) {
        ()
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

// Creusot requirement: DeepModel for NodeWrapper
// From creusot's source:
// "The deep model corresponds to the model used for specifying
// operations such as equality, hash function or ordering, which are
// computed deeply in a data structure."
// TODO: check this! type DeepModelTy = Node?
impl DeepModel for Node {
    type DeepModelTy = Node;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl ShallowModel for Node {
    type ShallowModelTy = Node;
    
    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self
    }
}

// Creusot forces me to implement traits for these types. 
// To avoid problems with the orphan rule, we use the newtype pattern
#[derive(Debug)]
struct UniqueTableWrapper (HashMap<Node, Edge>);
#[derive(Debug)]
struct ApplyNotCacheWrapper (HashMap<Edge, Edge>);
#[derive(Debug)]
struct ApplyAndCacheWrapper (HashMap<(Edge, Edge), Edge>);

// TODO: to avoid Creusot asking me to implement a Default trait over
// type HashMap<_, _>
//#[derive(Default, Debug)]
#[derive(Debug)]
pub struct Manager {
    node_store: Vec<Node>,
    unique_table: UniqueTableWrapper,
    apply_not_cache: ApplyNotCacheWrapper,
    apply_and_cache: ApplyAndCacheWrapper,
}

// TODO: put models into another crate?
// impl ShallowModel for UniqueTableWrapper {
//     // We will look at HashMap<Node, Edge> as a simple mapping Node -> Edge
//     type ShallowModelTy = logic::Mapping<Node, Edge>;

//     #[logic]
//     fn shallow_model(self) -> Self::ShallowModelTy {
//      logic::Mapping(std::marker::PhantomData)
//     }
// }

impl Manager {
    //#[ensures(result.node_store@ == logic::Seq::EMPTY)]
    pub fn new() -> Self {
        // TODO: to avoid Creusot asking me to implement a Default trait
        // Self::default()
        Manager {
            // TODO: warning: calling an external function with no contract will yield an impossible precondition
            node_store: Vec::new(),
            unique_table: UniqueTableWrapper(HashMap::new()),
            apply_not_cache: ApplyNotCacheWrapper(HashMap::new()),
            apply_and_cache: ApplyAndCacheWrapper(HashMap::new()),
        }
    }

    // Invariant about node_store
    #[predicate]
    fn invariant_sound_node_store(self) -> bool {
        pearlite! {
            // Seq::len(self.node_store@) is used as parameter to to_inner_node, 
            // in unique_table_get_or_insert;
            Seq::len(self.node_store@) <= u32::MAX@ - Edge::NUM_TERMINALS@
            &&
            forall<i : Int> 0 <= i && i < Seq::len(self.node_store@) ==> 
                // Every node level corresponds to its index in node_store
                self.node_store[i].level@ == i
                &&
                // Every edge that does not point to a terminal, points to an 
                // existing node
                (self.node_store[i]).t.0@ - Edge::NUM_TERMINALS@ < Seq::len(self.node_store@)
                &&
                (self.node_store[i]).e.0@ - Edge::NUM_TERMINALS@ < Seq::len(self.node_store@)
                
        }
    }

    /// Panics if self points to
    // To avoid inner_node_index() == None
    // TODO: ugly, I am exposing implementation details
    #[requires(f.0@ >= 2)]
    // To guarantee index within bounds
    // TODO: ugly, here I am speaking about implementation details
    #[requires(f.0@ - Edge::NUM_TERMINALS@ < Seq::len(self.node_store@))]
    #[ensures(result == self.node_store[f.0@ - Edge::NUM_TERMINALS@])]
    pub fn get_node(&self, f: Edge) -> Node {
        self.node_store[f.inner_node_index().unwrap() as usize]
    }
      
    // Cannot guarantee panics absence if we eval over an arbitrary Manager
    #[requires(self.invariant_sound_node_store())]
    // To satisfy get_node's precondition
    // TODO: ugly, I am exposing implementation details
    #[requires(f.0@ >= 2 ==> f.0@ - Edge::NUM_TERMINALS@ < Seq::len(self.node_store@))]
    // To guarantee index within bounds of env
    #[requires(f.0@ >= 2 ==> self.node_store@[f.0@ - Edge::NUM_TERMINALS@].level@ < Seq::len(env@))]
    #[requires(Seq::len(env@) == Seq::len(self.node_store@))]
    pub fn eval(&self, f: Edge, env: &[bool]) -> bool {
        if let Some(v) = f.terminal_value() {
            v
        } else {
            proof_assert!(f.0@ >= 2);
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

    // Cannot guarantee panics absence if we eval over an arbitrary Manager
    #[requires(self.invariant_sound_node_store())]
    // To avoid integer overflow when pushing into self.node_store
    #[requires(Seq::len(self.node_store@) < u32::MAX@)]
    fn unique_table_get_or_insert(&mut self, node: Node) -> Edge {
        match self.unique_table.0.entry(node) {
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
        if let Some(res) = self.apply_and_cache.0.get(&key) {
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

        self.apply_and_cache.0.insert(key, res);

        res
    }

    pub fn apply_not(&mut self, f: Edge) -> Edge {
        let fnode = match f.terminal_value() {
            Some(t) => return Edge::to_terminal(!t),
            None => self.get_node(f),
        };

        if let Some(res) = self.apply_not_cache.0.get(&f) {
            return *res;
        }

        let node = Node {
            t: self.apply_not(fnode.t),
            e: self.apply_not(fnode.e),
            level: fnode.level,
        };
        let res = self.unique_table_get_or_insert(node);

        self.apply_not_cache.0.insert(f, res);

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

