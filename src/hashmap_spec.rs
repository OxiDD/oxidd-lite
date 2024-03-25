extern crate creusot_contracts;

// Axiomatization of the required behavior from HashMap, following
// the proposal done in bdd.rs from Creusot's test suite
// TODO: does HashMap's implementation use unsafe code?
pub mod hashmap_spec {
    // TODO: why do I need to declare this import in this level, instead of 
    // being able to declare them once and for all, outside of this module?
    use creusot_contracts::{logic::Mapping, predicate, logic, trusted, ensures, open, pearlite, ShallowModel};

    use ::std::collections::HashMap;
    use ::std::hash::Hash;
    use ::std::collections::hash_map::Entry;
    use ::std::collections::hash_map::OccupiedEntry;
    use ::std::collections::hash_map::VacantEntry;

    // TODO: warning: calling an external function with no contract will yield an impossible precondition
    //#[derive(Debug)]
    pub struct OccupiedEntryWrapper<'a, K, V> (OccupiedEntry<'a, K, V>);

    impl<'a, K : Default, V : Default> OccupiedEntryWrapper<'a, K, V> {
        // NOTE: if we do not implement a wrapper around OccupiedEntry,
        // self.get() would make Creusot to produce an impossible goal (false)
        #[trusted]
        #[ensures(*result == self@.1)]
        pub fn get(&self) -> &V {
            self.0.get()
        }

        #[trusted]
        pub fn key(&self) -> &K {
            self.0.key()
        }
    }

    impl<'a, K : Default, V : Default> ShallowModel for OccupiedEntryWrapper<'a, K, V>{
        type ShallowModelTy = (K, V);

        // We just assume the existence of a mapping between HashMap<K, V>
        // and logical type Mapping<K::DeepModelTy, Option<V>>
        #[logic]
        #[open(self)]
        #[trusted]
        fn shallow_model(self) -> Self::ShallowModelTy {
            absurd
        }
    }

    // TODO: warning: calling an external function with no contract will yield an impossible precondition
    //#[derive(Debug)]
    pub struct VacantEntryWrapper<'a, K, V> (VacantEntry<'a, K, V>);

    impl<'a, K : Default, V : Default> VacantEntryWrapper<'a, K, V> {
        #[trusted]
        pub fn insert(self, value: V) -> &'a mut V {
            self.0.insert(value)
        }
    }

    // TODO: warning: calling an external function with no contract will yield an impossible precondition
    //#[derive(Debug)]
    pub enum EntryWrapper<'a, K, V> {
        OccupiedWrapper(OccupiedEntryWrapper<'a, K, V>),
        VacantWrapper(VacantEntryWrapper<'a, K, V>),
    }

    // TODO: warning: calling an external function with no contract will yield an impossible precondition
    //#[derive(Debug)]
    pub struct HashMapWrapper<K, V> (HashMap<K, V>);

    impl<K, V> ShallowModel for HashMapWrapper<K, V> {
        type ShallowModelTy = Mapping<K, Option<V>>;

        // We just assume the existence of a mapping between HashMap<K, V>
        // and logical type Mapping<K::DeepModelTy, Option<V>>
        #[logic]
        #[open(self)]
        #[trusted]
        fn shallow_model(self) -> Self::ShallowModelTy {
            absurd
        }
    }
    
    // TODO: should I repeat the same traits on every type parameter?
    impl<K : Default, V : Default> creusot_contracts::std::default::Default for HashMapWrapper<K, V> {
        #[predicate]
        #[open]
        fn is_default(self) -> bool {
            pearlite! { self.shallow_model() == self.shallow_model() }
        }

    }

    impl<K : Default, V : Default> Default for HashMapWrapper<K, V> {

        #[trusted]
        // TODO: can't avoid the error: the trait `creusot_contracts::Default` 
        // is not implemented for `std::collections::HashMap<K, V>` maybe 
        // implement an empty trusted function, where we specify the desired 
        // properties of the return default
        fn default() -> Self { 
            HashMapWrapper(HashMap::default())
        }
    }

    // Re-implementation of HashMap API
    impl<K : Eq + PartialEq + Hash + Default, V : Default> HashMapWrapper<K, V> {

        
        // TODO: I need to add some property here that guarantees 
        // arbitrary desired conditions, when using entry
        #[trusted]
        #[ensures(match result {
                    EntryWrapper::OccupiedWrapper(entry)  => 
                          Some(entry@.1) == self@.get(key)
                          && 
                          entry@.0 == key
                          &&
                          *self == ^self, 
                    EntryWrapper::VacantWrapper(entry) => 
                          self@.get(key) == None
                          &&
                          *self == ^self
                  })]
        pub fn entry(&mut self, key: K) -> EntryWrapper<K, V> {
            match self.0.entry(key) {
                Entry::Occupied(entry) => {
                    EntryWrapper::OccupiedWrapper(OccupiedEntryWrapper(entry))
                }

                Entry::Vacant(entry) => {
                    EntryWrapper::VacantWrapper(VacantEntryWrapper(entry))
                }
            }
        }

        #[trusted]
        // TODO: check if this is needed
        #[ensures(match result {
                        Some(v) => self@.get(*key) == Some(*v),
                        None => self@.get(*key) == None,
          })]
        pub fn get(&self, key: &K) -> Option<&V> {
            self.0.get(key)
        }

        #[trusted]
        // insert only inserts (k, v)
        #[ensures((^self)@.get(k) == Some(v))]
        // Keys of (*self) are included in keys of (^self),
        // and the corresponding values are preserved, except for k
        #[ensures(forall<k2 : K> k2 != k ==> 
                  forall<v2 : V>
                  (*self)@.get(k2) == Some(v2) ==>
                  (^self)@.get(k2) == Some(v2))]
        // Keys of (^self) include keys of (^self) plus, perhaps, k
        #[ensures(forall<k2 : K> k2 != k ==>
                  forall<v2 : V>
                  (^self)@.get(k2) == Some(v2) ==> 
                  (*self)@.get(k2) == Some(v2))]
        pub fn insert(&mut self, k: K, v: V) -> Option<V> {
            self.0.insert(k, v)
        }
    }
}
