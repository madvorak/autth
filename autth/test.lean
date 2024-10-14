import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Data.List.Join
import Mathlib.Util.Delaborators
import Mathlib.Computability.ContextFreeGrammar

import Mathlib.Computability.EpsilonNFA

structure PDA  (Q: Type)(T: Type)(S: Type) where
  initial_state : Q
  start_symbol : S
  final_states : Set Q
  transition_fun : Q → T → S → Set (Q × List S)
  transition_fun' : Q → S → Set (Q × List S)

namespace PDA

structure conf
    {Q T S: Type} (p : PDA Q T S) where
  state : Q
  input : List T
  stack : List S




def step {Q T S : Type} {pda : PDA Q T S} (r₁ : conf pda) : Set (conf pda) :=
  match r₁ with
    | ⟨q,a::w,Z::α⟩ =>
        {r₂ : conf pda | ∃ (p:Q) (β:List S), (p,β) ∈ pda.transition_fun q a Z ∧
                          r₂=⟨p, w, (β ++ α)⟩ } ∪
        {r₂ : conf pda | ∃(p:Q)(β:List S), (p,β) ∈ pda.transition_fun' q Z ∧
                          r₂=⟨p, a :: w, (β ++ α)⟩}
    | ⟨q,Nil,Z::α⟩ => {r₂ : conf pda | ∃(p:Q)(β:List S), (p,β) ∈ pda.transition_fun' q Z ∧
                                         r₂=⟨p, Nil, (β ++ α)⟩}
    | ⟨q,w,Nil⟩ => {r₂ : conf pda | r₂ = ⟨q,w,Nil⟩} -- Empty stack

def stepSet {Q T S : Type} {pda : PDA Q T S} (R : Set (conf pda)) : Set (conf pda) :=
  ⋃ r ∈ R , step r

def stepSetN {Q T S : Type} {pda : PDA Q T S} (n : ℕ) (R : Set (conf pda))  : Set (conf pda) :=
  match n with
  | 0 => R
  | Nat.succ m => stepSet (stepSetN m R)


/-def stepRel {Q T S : Type} {pda : PDA Q T S} (r₁ : PDA_id pda)(r₂ : PDA_id pda) : Prop :=
  r₂ ∈ step r₁-/

inductive reaches' {Q T S : Type} {pda : PDA Q T S}  : conf pda→ conf pda→Prop :=
  | base : (r₁ : conf pda) → reaches' r₁ r₁
  | step : {r₁ r' r₂ : conf pda} → (r'∈ step r₁) → (reaches' r' r₂) → reaches' r₁ r₂

def reachesN {Q T S : Type} {pda : PDA Q T S} (n : ℕ) (r₁ : conf pda)(r₂ : conf pda) : Prop :=
  r₂ ∈ stepSetN n {r₁}

def reaches {Q T S : Type} {pda : PDA Q T S}  (r₁ : conf pda)(r₂ : conf pda) : Prop :=
  ∃n:ℕ, r₂ ∈ stepSetN n {r₁}


def acceptsByEmptyStack {Q T S : Type} (pda : PDA Q T S) : Language T :=
  {w : List T | ∃q:Q, reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q,[],[]⟩ }

def acceptsByFinalState {Q T S : Type} (pda : PDA Q T S) : Language T :=
  {w : List T | ∃q ∈ pda.final_states,∃ γ:List S,
      reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q,[],γ⟩ }


inductive alph where
  | a
  | b

inductive nt where
  | S

open alph
open nt
open Symbol
open ContextFreeGrammar

def G : ContextFreeGrammar alph := ⟨nt,S,
  [⟨S,[]⟩,
  ⟨nt.S,[terminal a, nonterminal S, terminal b]⟩]⟩

example : [a,a,b,b] ∈ G.language := by
  rw [mem_language_iff]
  simp
  rw [Derives]
  apply Relation.ReflTransGen.tail
  case b => exact [terminal a,terminal a,nonterminal S, terminal b,terminal b]
  case a =>
    apply Relation.ReflTransGen.tail
    case b => exact [terminal a,nonterminal S,terminal b]
    case a =>
      apply Relation.ReflTransGen.tail
      case b => exact [nonterminal S]
      case a => rw [ (by rfl :G.initial = S)]
      case a =>
        use ⟨nt.S,[terminal a, nonterminal S, terminal b]⟩
        constructor
        · simp [G]
        · apply (ContextFreeRule.rewrites_iff [nonterminal S] [terminal a, nonterminal S, terminal b]).mpr
          use []
          use []
          simp
    case a =>
      use ⟨nt.S,[terminal a, nonterminal S, terminal b]⟩
      constructor
      · simp [G]
      · apply ContextFreeRule.Rewrites.cons (terminal a)
        apply ContextFreeRule.Rewrites.head [terminal b]
  case a =>
    use ⟨nt.S,[]⟩
    simp [G]
    apply ContextFreeRule.Rewrites.cons (terminal a)
    apply ContextFreeRule.Rewrites.cons (terminal a)
    apply ContextFreeRule.Rewrites.head [terminal b, terminal b]
