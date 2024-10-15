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

@[ext]
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

variable {Q T S : Type} {pda : PDA Q T S}

theorem reaches_refl (r₁ : conf pda) : reaches r₁ r₁ := by
  use 0; simp [stepSetN];

theorem reachesN_of_add_one  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}{n : ℕ}
        (h₁:reachesN n r₁ r₂)(h₂:reachesN 1 r₂ r₃): reachesN (n+1) r₁ r₃ := by
  simp [reachesN, stepSetN, stepSet] at *
  use r₂

theorem reachesN_trans  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}{n m : ℕ}
        (h₁:reachesN n r₁ r₂)(h₂:reachesN m r₂ r₃):∃k≤n+m, reachesN (k) r₁ r₃ := by
  induction' m with m ih generalizing r₃
  · simp [reachesN,stepSetN] at h₂
    rw [←h₂] at h₁
    use n
    refine ⟨?_, h₁⟩
    linarith
  · rw [reachesN,stepSetN,stepSet] at h₂
    simp at h₂
    obtain ⟨c,h⟩ :=  h₂
    have r₂_reaches_c: reachesN m r₂ c := by
      simp [reachesN, stepSetN, stepSet] at *
      exact h.1
    apply ih at r₂_reaches_c
    have c_reaches_r₃ : reachesN 1 c r₃ := by
      simp [reachesN, stepSetN, stepSet] at *
      exact h.2
    obtain ⟨k,h⟩ := r₂_reaches_c
    use k+1
    constructor
    linarith
    exact reachesN_of_add_one h.2 c_reaches_r₃

theorem reaches_trans  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}
        (h₁:reaches r₁ r₂)(h₂:reaches r₂ r₃): reaches r₁ r₃ := by
  rw [reaches] at *
  obtain ⟨n,h⟩ := h₁
  obtain ⟨m,h'⟩ := h₂
  rw [←reachesN] at *
  rcases reachesN_trans h h' with ⟨k,h⟩
  use k
  exact h.2
