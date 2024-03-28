extern crate creusot_contracts;
use creusot_contracts::{std, Clone, PartialEq, predicate, *};

// Axiomatization of HashMaps
//mod hashmap_spec;
use crate::hashmap_spec;
use hashmap_spec::hashmap_spec::HashMapWrapper;
use hashmap_spec::hashmap_spec::EntryWrapper;

use std::cmp::Ordering;
// NOTE: using our own hash-map wrapper
//use std::collections::HashMap;
use std::hash::Hash;

// spell-checker:ignore fnode,gnode

// Note: We only need some arbitrary total ordering on `Edge`s. This avoids
// having both f ∧ g and g ∧ f separately in the apply cache.
// Note 2: Since we are forced to implement trait OrdLogic, that speaks
// about this total order, we would need to define ourselves this relation
// to guarantee that both orders coincide
// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
// TODO: warning: calling an external function with no contract will yield an impossible precondition
//#[derive(Debug)]    
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
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
    #[ensures(result == Some(self.cmp_log(*other)))]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Edge {
    #[ensures(result == self.cmp_log(*other))]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0, other.0) {
            (a, b) if a < b => Ordering::Less,
            (a, b) if a > b => Ordering::Greater,
            _               => Ordering::Equal,
        }
    }
}

impl creusot_contracts::Default for Edge {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        // TODO: ?
        pearlite! { self.0@ == 0 }
    }
}

impl Edge {

    const NUM_TERMINALS: u32 = 2;

    #[ensures(!result.points_to_inner_node())]
    // To help in proving assertions that depend on the
    // injectivity of to_terminal (NOTE: weaker prop. than injectivity) 
    #[ensures(match result {
        Edge(e) => if e@ == 0 {value == false}
        else {value == true}
    })]
    // Expected correspondence with to_terminal_logic
    #[ensures(result@ == Edge::to_terminal_logic(value))]
    pub fn to_terminal(value: bool) -> Self {
        Self(value as u32)
    }

    #[logic]
    #[open]
    pub fn to_terminal_logic(value: bool) -> Int {
        pearlite! { 
            // TODO: ugly, by I cannot use casts here
            if value {
                1
            } else {
                // { !value }
                0
            }
        }
    }

    // To avoid overflow
    #[predicate]
    fn to_inner_node_precondition(index : Int) -> bool {
        pearlite! { index <= u32::MAX@ - Self::NUM_TERMINALS@ }
    }

    #[requires(Edge::to_inner_node_precondition(index@))]
    #[ensures(result.points_to_inner_node())]
    // TODO: ugly, but it solves problems later, when reasoning
    // about the value of to_inner_node(index)
    #[ensures(result.0@ == index@ + Self::NUM_TERMINALS@)]
    fn to_inner_node(index: u32) -> Self {
        Self(index + Self::NUM_TERMINALS)
    }

    #[ensures(self.0@ >= 2 ==> result == None)]
    #[ensures(result == None ==> self.0@ >= 2)]
    // Expected correspondence with terminal_value_logic
    #[ensures(self.is_terminal_value() ==>
              match result {
                  Some(b) => 
                      b == self.terminal_value_logic(),
                  None =>
                  // Impossible case
                      false
              })]
    pub fn terminal_value(self) -> Option<bool> {
        if self.0 == 0 {
            Some(false)
        } else if self.0 == 1 {
            Some(true)
        } else {
            None
        }
    }
    
    #[predicate]
    #[open]
    pub fn is_terminal_value(self) -> bool {
        pearlite! { self.0@ == 0 || self.0@ == 1 }
    }
    
    #[predicate]
    #[open]
    #[requires(self.is_terminal_value())]
    pub fn terminal_value_logic(self) -> bool {
        pearlite! {
            if self@ == 0 { 
                false 
            } else {
                true
            }
        }
    }
    
    #[ensures(self.0@ >= 2 ==> result != None)]
    // TODO: forced to do this; otherwise: ShallowModel for Option(u32)
    #[ensures(self.0@ >= 2 ==> 
              match result {
                  Some(x) => x@ == self.0@ - Self::NUM_TERMINALS@,
                  None    => false
              })]
    // Expected correspondence with inner_node_index_logic
    #[ensures(self.points_to_inner_node() ==>
              match result {
                  Some(index) => index@ == self.inner_node_index_logic(),
                  None => true
              })]
    fn inner_node_index(self) -> Option<u32> {
        if self.0 >= 2 { // TODO: NUM_TERMINALS?
            Some(self.0 - Self::NUM_TERMINALS)
        } else {
            None
        }
    }

    // Useful to abstract the mechanism implemented by inner_node_index,
    // for specification purposes
    #[predicate]
    #[open]
    pub fn points_to_inner_node(self) -> bool {
        // TODO: NUM_TERMINALS?
        pearlite! { self.0@ >= 2 }
    }

    #[logic]
    #[requires(self.points_to_inner_node())]
    #[open]
    pub fn inner_node_index_logic(self) -> Int {
        pearlite! { self.0@ - Self::NUM_TERMINALS@ }
    }

        // Edge points to an existing node
    #[predicate]
    #[open]
    pub fn edge_invariant (self, manager : &Manager) -> bool {
        pearlite! { 
            self.points_to_inner_node() ==>
                self.inner_node_index_logic() < Seq::len(manager.node_store@)
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

// TODO: warning: calling an external function with no contract will yield an impossible precondition
//#[derive(Debug)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Node {
    /// Level number, must be less than `t.level` and `e.level` (given that
    /// these point to inner nodes)
    level: u32,
    /// Then edge
    t: Edge,
    /// Else edge
    e: Edge,
}

impl Node {

    pub fn get_level (self) -> u32 {
        self.level
    }

    #[ensures(result == self.get_then_logic())]
    pub fn get_then (self) -> Edge {
        self.t
    }
    
    #[logic]
    #[open]
    pub fn get_then_logic (self) -> Edge {
        self.t
    }

    #[ensures(result == self.get_else_logic())]
    pub fn get_else (self) -> Edge {
        self.e
    }

    #[logic]
    #[open]
    pub fn get_else_logic (self) -> Edge {
        self.e
    }

    // For spec. purposes
    // Sound node, with respect to a given instance of Manager
    #[predicate]
    #[open]
    pub fn node_invariant (self, manager : &Manager) -> bool {
        pearlite! { self.t.edge_invariant(manager) 
                    && 
                    self.e.edge_invariant(manager)
                    &&
                    self.t != self.e
                    // TODO: something to say about the following property?
                    // &&
                    // every node at level i can only have successor nodes at levels greater than i
        }
    }

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

impl creusot_contracts::Default for Node {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        // TODO: stub!
        pearlite! { self.t@ == 0 && self.t@ == 1 && self.level@ == 0 }
    }
}

// TODO: warning: calling an external function with no contract will yield an impossible precondition
//#[derive(Debug)]
#[derive(Default)]
pub struct Manager {
    node_store: Vec<Node>,
    // From OxiDD's paper: Here, it is assumed that the get_or_make_node function 
    // at the bottom also maintains reducedness, typically implemented using a
    // hash table called unique table
    unique_table: HashMapWrapper<Node, Edge>,
    apply_not_cache: HashMapWrapper<Edge, Edge>,
    apply_and_cache: HashMapWrapper<(Edge, Edge), Edge>,
}

impl creusot_contracts::Default for Manager {
    #[predicate]
    #[open]
    //#[requires(self.manager_invariant())]
    fn is_default(self) -> bool {
        // NOTE: if self.manager_invariant(), we can reduce
        // the predicate to just this
        pearlite! { Seq::len(self.node_store@) == 0 }
    }
}

impl ShallowModel for Manager {
    type ShallowModelTy = Manager;
    
    #[open]
    #[logic]
    // TODO: ?
    fn shallow_model(self) -> Self::ShallowModelTy {
        self
    }
}

impl Manager {
    // TODO: check this
    // #[ensures(Manager::is_default(result))]
    // #[ensures(result.manager_invariant())]
    pub fn new() -> Self {
        Self::default()
    }

    ///////////////////////////////////
    // Predicates about Manager
    ///////////////////////////////////
    #[predicate]
    #[open]
    pub fn manager_invariant(self) -> bool {
        pearlite! {
            self.node_store_invariant()
            &&
            self.unique_table_invariant()
            &&
            self.apply_and_cache_invariant()
            &&
            self.apply_not_cache_invariant()
            // TODO: it would be useful, though Creusot requires for me to
            // implement trait std::iter::ExactSizeIterator
            // &&
            // Seq::len(self.node_store@) == Mapping::len(self.unique_table@)
        }
    }

    ///////////////////////////////////
    // Predicates about self.unique_table
    ///////////////////////////////////
    // Every edge satisfies edge_invariant
    // TODO: would it help quantify only over the keys of the hash?
    #[predicate]
    #[open]
    pub fn unique_table_invariant(self) -> bool {
        pearlite! {
            (forall<i : Int> 0 <= i && i < Seq::len(self.node_store@) ==> 
              exists<e : Edge> (self.unique_table)@.get(self.node_store@[i]) == Some(e))
             &&
             forall<node : Node>
              forall<e : Edge> 
                (self.unique_table)@.get(node) == Some(e) ==>
                e.edge_invariant(&self)
                &&
                e.points_to_inner_node() 
                && 
                self.node_store@[e.inner_node_index_logic()] == node
        }
    }
    
    /////////////////////////////////////////////////////
    // Predicates about self.node_store and related stuff
    /////////////////////////////////////////////////////
    // We can still store at least on element in self.node_store
    // TODO: see if we really need to separate it from the predicate 
    // Seq::len(self.node_store@) <= u32::MAX@ - Edge::NUM_TERMINALS@
    #[predicate]
    fn node_store_has_space_left(self) -> bool {
        pearlite! { Seq::len(self.node_store@) < u32::MAX@ }
    }

    // Invariant about node_store
    #[predicate]
    #[open]
    pub fn node_store_invariant(self) -> bool {
        pearlite! {
            forall<i : Int> 0 <= i && i < Seq::len(self.node_store@) ==>
                // Every edge that does not point to a terminal, points to an 
                // existing node
                self.node_store[i].node_invariant(&self)
        }
    }

    // Checks if self.node_store is a "prefix" of another_store
    #[predicate]
    fn node_store_is_prefix(store : Vec<Node>, prefix_store : Vec<Node> ) -> bool {
        pearlite! { Seq::len(prefix_store@) <= Seq::len(store@)
                    &&
                    forall<i : Int> 0 <= i && i < Seq::len(prefix_store@) ==>
                                    store@[i] == prefix_store@[i] }
    }

    /////////////////////////////////////////////////////
    // Predicates about self.apply_and_cache
    /////////////////////////////////////////////////////
    // Invariant about apply_and_cache
    #[predicate]
    #[open]
    pub fn apply_and_cache_invariant(self) -> bool {
        pearlite! {
            forall<pair : (Edge, Edge)> 
                match self.apply_and_cache@.get(pair) {
                    Some(edge) => edge.edge_invariant(&self),
                    None => true
                }
        }
    }
    
    /////////////////////////////////////////////////////
    // Predicates about self.apply_not_cache
    /////////////////////////////////////////////////////
    // Invariant about apply_not_cache
    #[predicate]
    #[open]
    pub fn apply_not_cache_invariant(self) -> bool {
        pearlite! {
            forall<key : Edge> 
                match self.apply_not_cache@.get(key) {
                    Some(edge) => edge.edge_invariant(&self),
                    None => true
                }
        }
    }


    /// Panics if self points to
    // TODO: check if this is needed
    #[requires(self.manager_invariant())]
    #[ensures(result.node_invariant(self))]
    // To avoid inner_node_index() == None
    #[requires(f.points_to_inner_node())]
    // To guarantee index within bounds
    #[requires(f.inner_node_index_logic() < Seq::len(self.node_store@))]
    #[ensures(result == self.node_store[f.inner_node_index_logic()])]
    #[ensures(result.node_invariant(self))]
    pub fn get_node(&self, f: Edge) -> Node {
        self.node_store[f.inner_node_index().unwrap() as usize]
    }
      
    // Cannot guarantee panics absence if we eval over an arbitrary Manager
    #[requires(self.manager_invariant())]
    // To satisfy get_node's precondition
    #[requires(f.edge_invariant(&self))]
    // To guarantee index of env, within bounds
    #[requires(f.points_to_inner_node() ==>
               self.node_store[f.inner_node_index_logic()].level@ < Seq::len(env@))]
    // To preserve the previous property on recursive calls
    #[requires(forall<i : Int> 0 <= i && i < Seq::len(self.node_store@) ==>
                self.node_store[i].t.points_to_inner_node() ==> 
                self.node_store[self.node_store[i].t.inner_node_index_logic()].level@ < Seq::len(env@))]
    #[requires(forall<i : Int> 0 <= i && i < Seq::len(self.node_store@) ==>
                self.node_store[i].e.points_to_inner_node() ==> 
                self.node_store[self.node_store[i].e.inner_node_index_logic()].level@ < Seq::len(env@))]
    // TODO: see if it is possible to define an empty function whose spec.
    // states this property
    // Function correctness: 
    // [| node_i |] = (x_i /\ [| node_i.t |]) \/ (not x_i /\ [| node_i.e |])
    // We will reuse Creusot propositional fragment
    // TODO: some way to define constants in pearlite?
    // TODO: variant?
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

    /// Apply the BDD reduction rules to `node` and return an `Edge` pointing to
    /// the resulting node or [`None`] in case of an out-of-memory situation
    ///
    /// The outgoing edges of `node` must belong to this manager.
    #[requires(self.manager_invariant())]
    #[requires(then_edge.edge_invariant(self) 
               && 
               else_edge.edge_invariant(self))]
    // If we modify self.node_store, it is just by adding new nodes
    #[ensures(Manager::node_store_is_prefix((^self).node_store, (*self).node_store))]
    #[ensures((^self).manager_invariant())]
    #[ensures(match result {
                    Some(e) => e.edge_invariant(&^self) 
                               &&
                               (exists<node : Node>
                                e.points_to_inner_node()
                                ==>
                                (^self).node_store@[e.inner_node_index_logic()] == node),
                    None => true
              })]
    fn reduce(&mut self, level: u32, then_edge: Edge, else_edge: Edge) -> Option<Edge> {
        if then_edge == else_edge {
            return Some(then_edge);
        }
        
        proof_assert!(then_edge != else_edge);

        let node = Node {
            level,
            t: then_edge,
            e: else_edge,
        };
        
        let e = match self.unique_table.entry(node) {
            EntryWrapper::OccupiedWrapper(entry) => *entry.get(),
            EntryWrapper::VacantWrapper(_) => { 
                // TODO: not using entry to insert the element
                let idx = self.node_store.len();
                // To comply with to_inner_node's pre
                if idx > (u32::MAX - Edge::NUM_TERMINALS) as usize {
                    return None; // out of memory
                }
                let idx = idx as u32;
                let edge = Edge::to_inner_node(idx);

                self.node_store.push(node);                
                self.unique_table.insert(node, edge);
                
                edge
            }
        };

        Some(e)
    }

    /// Returns [`None`] in an out-of-memory situation
    // To satisfy pre-condition of reduce
    #[requires(self.manager_invariant())]
    #[requires(Seq::len(self.node_store@) <= u32::MAX@ - Edge::NUM_TERMINALS@)]
    #[ensures((^self).manager_invariant())]
    pub fn get_var(&mut self, level: u32) -> Option<Edge> {
        self.reduce(level, Edge::to_terminal(true), Edge::to_terminal(false))
    }
    
    /// Returns [`None`] in an out-of-memory situation
    // We are working over a sound manager (sound node_store, etc)
    #[requires(self.manager_invariant())]
    // get_node's pre-condition
    #[requires(f.edge_invariant(self))]
    #[requires(g.edge_invariant(self))]
    // The obtained manager preserves the invariant
    #[ensures((^self).manager_invariant())]
    // If we modify self.node_store, it is just by adding new nodes
    #[ensures(Manager::node_store_is_prefix((^self).node_store, (*self).node_store))]
    // To guarantee properties required by reduce, about the
    // received node
    #[ensures(match result {
                 Some(e) => e.edge_invariant(&^self)
                            &&
                            (e.points_to_inner_node()
                             ==>
                             exists<node : Node> 
                             (^self).node_store@[e.inner_node_index_logic()] == node),
                 None => true
              })]
    // Part of functional correctness
    #[ensures(f == g ==> result == Some(f))]
    #[ensures(match result { 
                  Some(e) =>
                   match f.is_terminal_value() {
                      true =>
                           match f.terminal_value_logic() {
                               false => e@ == Edge::to_terminal_logic(false),
                               true  => e == g,
                           }
                       false =>
                           // { !f.is_terminal_value() }
                           match g.is_terminal_value() {
                               true =>
                                   match g.terminal_value_logic() {
                                       false => e@ == Edge::to_terminal_logic(false),
                                       true  => e == f
                                   },
                               false =>
                                   // { !f.is_terminal_value() 
                                   //   && 
                                   //   !g.is_terminal_value() }
                                   true
                           }
                      },
                  None => true
              })]
    pub fn apply_and(&mut self, f: Edge, g: Edge) -> Option<Edge> {
        if f == g {
            return Some(f);
        }

        proof_assert!(f != g);
        
        match (f.terminal_value(), g.terminal_value()) {
            (Some(false), _) | (_, Some(false)) => return Some(Edge::to_terminal(false)),
            (Some(true), _) => return Some(g),
            (_, Some(true)) => return Some(f),
            (None, None) => {}
        }

        proof_assert!(!f.is_terminal_value() && !g.is_terminal_value());

        let fnode = self.get_node(f);

        proof_assert!(fnode.e != fnode.t);

        let gnode = self.get_node(g);

        proof_assert!(gnode.e != gnode.t);

        // ∧ is commutative, so we use a canonical form of the key to increase
        // cache efficiency
        let key = if f < g { (f, g) } else { (g, f) };
        if let Some(res) = self.apply_and_cache.get(&key) {
            return Some(*res);
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

        let level = std::cmp::min(fnode.level, gnode.level);
        let ft_and_gt = self.apply_and(ft, gt);
        let fe_and_ge = self.apply_and(fe, ge);
        let res;

        match (ft_and_gt, fe_and_ge) {
            (Some(then_edge), Some(else_edge)) => {
                match self.reduce(level, then_edge, else_edge) {
                    Some(edge) => {
                        self.apply_and_cache.insert(key, edge);
                        // TODO: check if, by adding these kind of asserts, we improve
                        // performance
                        // proof_assert!(edge.edge_invariant(&^self));
                        // proof_assert!((^self).apply_and_cache_invariant());
                        res = Some(edge)
                    }
                    None => res = None
                }
            },

            (_, _) => res = None
        }
        
        res
    }

    /// Returns [`None`] in an out-of-memory situation
    // We are working over a sound Manager
    #[requires(self.manager_invariant())]
    // get_node's pre-condition
    #[requires(f.edge_invariant(&self))]
    #[ensures((^self).manager_invariant())]
    // If we modify self.node_store, it is just by adding new nodes
    #[ensures(Manager :: node_store_is_prefix((^self).node_store, (*self).node_store))]
    // To guarantee properties required by reduce, about the
    // received node
    #[ensures(match result {
                 Some(e) => e.edge_invariant(&^self),
                 None => true
              })]
    pub fn apply_not(&mut self, f: Edge) -> Option<Edge> {
        let fnode = match f.terminal_value() {
            Some(t) => return Some(Edge::to_terminal(!t)),
            None => self.get_node(f),
        };

        if let Some(res) = self.apply_not_cache.get(&f) {
            return Some(*res);
        }

        let res;
        
        match (self.apply_not(fnode.t), self.apply_not(fnode.e)) {
            (Some(then_edge), Some(else_edge)) => {
                
                match self.reduce(fnode.level, then_edge, else_edge) {
                    Some(edge) => {
                        self.apply_not_cache.insert(f, edge);
                        res = Some(edge)
                    },
                    
                    None => res = None
                }
            },

            _ => res = None
        }

        res
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // TODO: warning: calling an external function with no contract will yield an impossible precondition
    //#[derive(Debug)]
    #[derive(Clone, PartialEq, Eq)]
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
                                "Error some formula in env: expected something, got other thing...\n"
                                // TODO: for the moment, no Debug trait
                                //"Error for {formula:?} in {env:?}: expected {expected}, got {actual}\nDD: {f:?}"
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
