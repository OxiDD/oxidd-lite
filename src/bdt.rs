extern crate creusot_contracts;
use creusot_contracts::{std, Clone, PartialEq, *};
use crate::index_based::*;

use std::cmp::max;

// Binary decision tree: IR between BDD and boolean functions
enum BDT {
    // TODO: do I actually need to compute the highest level?
    // node level, then node, else node, highest level among nodes
    Inner(u32, Box<BDT>, Box<BDT>, u32),
    Terminal(bool),
}

// TODO: no known useful documentation or example about this!
// #[trusted]
// impl WellFounded for BDT {}

impl BDT {

    #[predicate]
    fn bdt_invariant(self) -> bool {
        use BDT::*;

        pearlite! {
            match self {
                Terminal(_) => 
                    true,
                Inner(level, t, e, max_level) => 
                    level <= max_level && t.bdt_invariant() && e.bdt_invariant()
                    &&
                    t.get_max_level_logic() <= max_level@
                    &&
                    e.get_max_level_logic() <= max_level@
            }
        }
    }

    // To maintain the expected correspondence with get_max_level_logic
    #[ensures(result@ == self.get_max_level_logic())]
    fn get_max_level(&self) -> u32 {
        use BDT::*;

        match self {
            Terminal(_) => // TODO: Need to return some "neutral" of max
                           u32::MIN,
            Inner(_, _, _, max_level) => *max_level
        }
    }

    #[logic]
    fn get_max_level_logic(&self) -> Int {
        use BDT::*;

        pearlite! {
            match self {
                Terminal(_) => // TODO: Need to return some "neutral" of max
                               u32::MIN@,
                Inner(_, _, _, max_level) => (*max_level)@
            }
        }
    }

    // We are working with a sound Manager and Edge
    #[requires(manager.manager_invariant())]
    #[requires(edge.edge_invariant(manager))]
    fn to_bdt(edge : &Edge, manager: &Manager) -> Self {
        use BDT::*;
        let ret : BDT;

        match edge.terminal_value() {
            Some(false) => ret = Terminal(false),
            Some(true) => ret = Terminal(true),
            None => {
                let node = manager.get_node(*edge);

                let node_level = node.get_level();
                
                let t = BDT::to_bdt(&node.get_then(), manager);
                let e = BDT::to_bdt(&node.get_else(), manager);
                let max_level = max (node_level, max (t.get_max_level(), e.get_max_level()));
                
                ret = Inner(node_level,
                            Box::new(t), 
                            Box::new(e),
                            max_level)
            }
        }

        ret
    }
    
    #[requires(bdt.bdt_invariant())]
    #[requires(bdt.get_max_level_logic() < Seq::len(env@))]
    fn eval(bdt : &BDT, env: &[bool]) -> bool {
        use BDT::*;
        
        match bdt {
            Terminal(b) => *b,
            Inner(level, t, e, _) => {
                BDT::eval(
                    if env[*level as usize] {
                        &*t
                    } else {
                        &*e
                    },
                    env
                )
            }
        }
    }

    #[requires(bdt.bdt_invariant())]
    fn apply_not(bdt : &BDT) -> Self {
        use BDT::*;

        let ret : BDT;

        ret = match bdt {
            Terminal(b) => Terminal(!b),

            Inner(level, t, e, max_level) => 
                // TODO: implement reduction rules!
                Inner(*level, 
                      Box::new(BDT::apply_not(t)), 
                      Box::new(BDT::apply_not(e)), 
                      *max_level)
        };
        
        ret
    }
}
