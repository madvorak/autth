import autth.PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

-- add new inital and final states
inductive add_init_final ( π : Type ) where
  | newinit
  | newfinal
  | oldstate: π -> (add_init_final π )

open add_init_final

instance : Fintype (add_init_final Q) where
  elems := ∅ -- Stefan: I want something like: {newinit, newfinal} ∪ { (oldstate p) | p ∈ Q.univ }
  complete := sorry

-- add new start symbol to stack alphabet
inductive add_start_symbol ( σ : Type ) where
  | newstart
  | oldsymbol : σ → ( add_start_symbol σ)

open add_start_symbol

instance : Fintype (add_start_symbol S) where
  elems := ∅ -- Stefan: I want something like: { newstart } ∪ { (oldsymbol Y) | Y ∈ S.univ }
  complete := sorry

-- Stefan: this is awful, what is a better way to do this?
def oldinject1 ( q : Q ) : ( add_init_final Q ) := (oldstate q)
def oldinject2 ( Z : S ) : ( add_start_symbol S ) := (oldsymbol Z)
def oldinject3 ( L : (List S) ) : ( List (add_start_symbol S)) := L.map (λ x => oldinject2 x)
def oldinject4 ( out : Q × (List S) ) : ( (add_init_final Q) × (List (add_start_symbol S)))
  := ( (oldinject1 out.1), (oldinject3 out.2) )
def oldinject5 ( out: Set (Q × (List S))) : Set ((add_init_final Q) × (List (add_start_symbol S)))
  := { oldinject4 x | x ∈ out }

--- define new transition function
abbrev newtransition_fun' (M : PDA Q T S) (q : (add_init_final Q)) (Z : (add_start_symbol S)) : Set ((add_init_final Q) × List (add_start_symbol S)) :=
  match q with
    | newinit => match Z with
      | newstart => {((oldstate M.initial_state),[(oldsymbol M.start_symbol),newstart])}
      | (oldsymbol _) => ∅
    | (oldstate p) => match Z with
      | newstart => {(newfinal,[])}
      | (oldsymbol Y) => (oldinject5 (M.transition_fun' p Y))
    | newfinal => ∅

abbrev newtransition_fun (M : PDA Q T S) (q : (add_init_final Q)) (a : T) (Z : (add_start_symbol S)) : Set ((add_init_final Q) × List (add_start_symbol S)) :=
  match q with
    | newinit => ∅
    | (oldstate p) => match Z with
      | newstart => ∅
      | (oldsymbol Y) => (oldinject5 (M.transition_fun p a Y))
    | newfinal => ∅

-- define translation function of PDAs
abbrev estack_to_fstate (M : PDA Q T S) : PDA (add_init_final Q) T (add_start_symbol S) := {
  initial_state := newinit
  start_symbol := newstart
  final_states := { newfinal }
  transition_fun := newtransition_fun M
  transition_fun' := newtransition_fun' M
}

-- main theorem
theorem fstate_of_estack (M : PDA Q T S) : M.acceptsByFinalState = (estack_to_fstate M).acceptsByEmptyStack := by
 sorry
