import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Data.List.Join
import Mathlib.Util.Delaborators

import Mathlib.Computability.EpsilonNFA

structure PDA  (Q: Type)(T: Type)(S: Type) where
  initial_state : Q
  start_symbol : S
  final_states : Set Q
  transition_fun : Q → T → S → Set (Q × List S)
  transition_fun' : Q → S → Set (Q × List S)

structure PDA_id
    {Q T S: Type} (p : PDA Q T S) where
  state : Q
  input : List T
  stack : List S

namespace PDA



def step {Q T S : Type} {pda : PDA Q T S} (r₁ : PDA_id pda) : Set (PDA_id pda) :=
  match r₁ with
    | ⟨q,a::w,Z::α⟩ =>
        {r₂ : PDA_id pda | ∃ p:Q, ∃β:List S, (p,β) ∈ pda.transition_fun q a Z ∧
                          r₂=⟨p, w, (β ++ α)⟩ } ∪
        {r₂ : PDA_id pda | ∃p:Q, ∃β:List S, (p,β) ∈ pda.transition_fun' q Z ∧
                          r₂=⟨p, a :: w, (β ++ α)⟩}
    | ⟨q,Nil,Z::α⟩ => {r₂ : PDA_id pda | ∃p:Q, ∃β:List S, (p,β) ∈ pda.transition_fun' q Z ∧
                                         r₂=⟨p, Nil, (β ++ α)⟩}
    | ⟨q,w,Nil⟩ => {r₂ : PDA_id pda | r₂ = ⟨q,w,Nil⟩} -- Empty stack

def stepSet {Q T S : Type} {pda : PDA Q T S} (R : Set (PDA_id pda)) : Set (PDA_id pda) :=
  ⋃ r ∈ R , step r

def stepSetN {Q T S : Type} {pda : PDA Q T S} (n : ℕ) (R : Set (PDA_id pda))  : Set (PDA_id pda) :=
  match n with
  | 0 => R
  | Nat.succ m => stepSet (stepSetN m R)

/-def stepRel {Q T S : Type} {pda : PDA Q T S} (r₁ : PDA_id pda)(r₂ : PDA_id pda) : Prop :=
  r₂ ∈ step r₁-/

def stepRelN {Q T S : Type} {pda : PDA Q T S} (n : ℕ) (r₁ : PDA_id pda)(r₂ : PDA_id pda) : Prop :=
  r₂ ∈ stepSetN n {r₁}

def stepRel {Q T S : Type} {pda : PDA Q T S}  (r₁ : PDA_id pda)(r₂ : PDA_id pda) : Prop :=
  ∃n:ℕ, r₂ ∈ stepSetN n {r₁}


def acceptsByEmptyStack {Q T S : Type} (pda : PDA Q T S) : Language T :=
  {w : List T | ∃q:Q, stepRel (⟨pda.initial_state, w, [pda.start_symbol]⟩ : PDA_id pda) ⟨q,[],[]⟩ }

def acceptsByFinalState {Q T S : Type} (pda : PDA Q T S) : Language T :=
  {w : List T | ∃q ∈ pda.final_states,∃ γ:List S,
      stepRel (⟨pda.initial_state, w, [pda.start_symbol]⟩ : PDA_id pda) ⟨q,[],γ⟩ }
