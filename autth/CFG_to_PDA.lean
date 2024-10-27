import autth.PDA
import autth.leftmost_deriv
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Logic.Relation
/-!
# Equivalence of languages accepted by PDAs and languages generated by CFGs

This File contains the proof that the set of languages accepted by some
PDA is exactly the same as the set of languages generated by some cfg.

For the the direction of grammar to pda, we will first define such a
pda and prove than that the languages are equal.
-/

namespace CFG_to_PDA

open ContextFreeGrammar
open Symbol
open PDA
open ContextFreeRule.RewritesLeftmost

-- In this whole section G will be the grammar we want to convert to a pda
variable {T : Type} [DecidableEq T] [Fintype T]
structure Q where loop ::

instance : Fintype Q where
  elems := {Q.loop}
  complete _ := by rw [Finset.mem_singleton]


abbrev S (G : ContextFreeGrammar T) [Fintype G.NT] := Symbol T G.NT

abbrev PDA' (G : ContextFreeGrammar T) [Fintype G.NT] := PDA Q T (S G)

abbrev transition_fun (G : ContextFreeGrammar T) [Fintype G.NT] (_ : Q) (a : T) (Z : S G) : Set (Q × List (S G)) :=
  match Z with
  | terminal b => if a=b then {(Q.loop, [])} else {}
  | _ => ∅

abbrev transition_fun' (G : ContextFreeGrammar T) [Fintype G.NT] (_ : Q) (Z : S G) : Set (Q × List (S G)) :=
  match Z with
  | nonterminal N => { (Q.loop, α) | (α : List (S G)) (_ : ⟨N, α⟩ ∈ G.rules) }
  | _ => ∅

-- Martin: This is not a good name for a function.
abbrev M (G : ContextFreeGrammar T) [Fintype G.NT] : PDA' G:= {
  initial_state := Q.loop
  start_symbol := nonterminal G.initial
  final_states := ∅
  transition_fun := transition_fun G
  transition_fun' := transition_fun' G
}

section
variable {G : ContextFreeGrammar T} [Fintype G.NT]
theorem M_consumes_terminal (a : T) (w : List T) (α : List (S G)):
    (M G).reachesN 1 ⟨Q.loop, a::w, terminal a :: α⟩ ⟨Q.loop, w, α⟩ := by
  rw [reachesN_one,step]
  apply Set.mem_union_left
  rw [Set.mem_setOf]
  use Q.loop, []
  simp [M, CFG_to_PDA.transition_fun]

theorem M_consumes_nonterminal {r : ContextFreeRule T G.NT} (h : r ∈ G.rules) (w : List T) (α : List (S G)):
    (M G).reachesN 1 ⟨Q.loop, w, nonterminal r.input :: α⟩ ⟨Q.loop, w, r.output ++ α⟩ := by
  rw [reachesN_one]
  rcases w with _| ⟨a, w'⟩ <;> dsimp [step]
  · use Q.loop, r.output
    dsimp [transition_fun']
    refine ⟨?_,?_⟩
    · use r.output
    · rfl
  · rw [Set.mem_union]
    right
    use Q.loop, r.output
    dsimp [transition_fun']
    refine ⟨?_,?_⟩
    · use r.output
    · rfl

theorem M_consumes_terminal_string (w w': List T) (α : List (S G)):
    (M G).reaches ⟨Q.loop, w++w', w.map terminal ++ α⟩ ⟨Q.loop, w', α⟩ := by
  induction' w with a w ih
  · rfl
  · apply reaches_trans _ ih
    rw [reaches_iff_reachesN]
    use 1
    apply M_consumes_terminal

theorem M_terminal_stack_of_read (a : T) (w : List T) (α β : List (S G)):
    (M G).reachesN 1 ⟨Q.loop, a::w, α⟩ ⟨Q.loop, w, β ⟩ → α = terminal a::β  := by
  intro h
  rcases α with _|⟨Z,α'⟩ <;> rw [reachesN_one] at h <;> dsimp [step] at h
  · rw [Set.mem_singleton_iff] at h
    have : w = a::w := by apply conf.mk.inj at h; exact h.2.1
    apply List.ne_cons_self at this
    contradiction
  · rw [Set.mem_union] at h
    rcases h with h|h
    <;> rw [Set.mem_setOf] at h
    <;> obtain ⟨_,γ,hγ, hr⟩ := h
    <;> rcases Z with ⟨a₀⟩|⟨N⟩
    <;> dsimp [transition_fun,transition_fun'] at hγ
    · have : a=a₀ ∨ a≠a₀ := by exact Decidable.em (a=a₀)
      rcases this with h|h <;> simp [h] at hγ
      · apply conf.mk.inj at hr
        simp [hr,h,hγ]
    · rw [Set.mem_empty_iff_false] at hγ
      contradiction
    · rw [Set.mem_empty_iff_false] at hγ
      contradiction
    · rw [conf.mk.injEq] at hr
      exfalso
      exact List.cons_ne_self _ _ hr.2.1.symm

theorem M_deterministic_step_of_terminal_stack_cons (a : T) (w v : List T) (β β' : List (S G)) :
    (M G).reachesN 1 ⟨Q.loop, w, terminal a :: β⟩ ⟨Q.loop, v, β'⟩ → w = a::v ∧ β = β' := by
  intro h
  rw [reachesN_one] at h
  rcases w with _|⟨b, w'⟩ <;>  dsimp [step, transition_fun'] at h
  · obtain ⟨_,β',h⟩ := h
    exfalso
    exact (Set.mem_empty_iff_false _).mp h.1
  · rw [Set.mem_union, Set.mem_setOf,Set.mem_setOf] at h
    rcases h with ⟨_, γ, hγ, h⟩|⟨_, γ ,hγ, -⟩
    · rcases dec_em (a = b) with h'|h'<;> simp only [transition_fun, Set.mem_ite_empty_right] at hγ
      · apply conf.mk.inj at h
        rw [Set.mem_singleton_iff, Prod.mk.inj_iff] at hγ
        rw [h.2.1,hγ.1,h',h.2.2,hγ.2.2]
        simp
      · exfalso
        exact h' hγ.1.symm
    · exfalso
      exact (Set.not_mem_empty _) hγ

theorem M_deterministic_of_terminal_stack_cons (a: T) (w : List T) (β : List (S G)):
    (M G).reaches ⟨Q.loop, w, terminal a :: β⟩ ⟨Q.loop, [], []⟩ →
    ∃ w' : List T, w = a :: w' ∧ (M G).reaches ⟨Q.loop, w', β⟩ ⟨Q.loop, [], []⟩ := by
  intro h
  rw [reaches_iff_reachesN] at h
  obtain ⟨n,h⟩ := h
  rcases n with _|⟨n⟩
  · rw [reachesN_zero,conf.mk.injEq] at h
    exfalso
    exact List.cons_ne_nil _ _ h.2.2
  · rw [←reachesN_iff_split_first] at h
    obtain ⟨⟨_,v,β'⟩,h₁,h₂⟩ := h
    apply M_deterministic_step_of_terminal_stack_cons at h₁
    use v
    use h₁.1
    rw [←h₁.2] at h₂
    rw [reaches_iff_reachesN]
    use n

theorem M_deterministic_of_terminal_stack (w v: List T) (β  : List (S G)):
    (M G).reaches ⟨Q.loop, w, v.map terminal ++ β⟩ ⟨Q.loop, [], []⟩ →
    ∃ w' : List T,  w = v ++ w' ∧ (M G).reaches ⟨Q.loop, w', β⟩ ⟨Q.loop, [], []⟩ := by
  intro h
  induction' v with a v' ih generalizing w
  · use w
    simp at h
    simp [h]
  · rw [List.map_cons] at h
    apply M_deterministic_of_terminal_stack_cons at h
    obtain ⟨w₀, hw₀,hr⟩ := h
    apply ih at hr
    obtain ⟨w₁, hw₁,hr⟩ := hr
    use w₁
    refine ⟨?_,?_⟩
    · simp [hw₀, hw₁]
    · exact hr

theorem M_reaches_off_G_derives (α : List (Symbol T G.NT)) (w : List T)
    (h : G.DerivesLeftmost α (w.map terminal)):
    (M G).reaches ⟨Q.loop, w, α⟩ ⟨Q.loop, [], []⟩ := by
  induction' h using Relation.ReflTransGen.head_induction_on with α β hα _ ih
  case refl =>
    induction' w with a w' ih
    case nil =>
      dsimp [reaches]
      use 0
      simp [stepSetN]
    case cons =>
      rw [List.map_cons]
      rw [reaches_iff_reachesN] at ih
      obtain ⟨n, hw'⟩ := ih
      rw [reaches_iff_reachesN]
      use n+1
      rw [←reachesN_iff_split_first]
      use ⟨Q.loop, w', w'.map terminal⟩
      refine ⟨?_,?_⟩
      · apply M_consumes_terminal
      · exact hw'
  case head =>
    obtain ⟨r,hrg,hrα⟩ := hα
    rw [rewrites_leftmost_iff] at hrα
    obtain ⟨p,q,hα',hβ'⟩ := hrα
    rw [hβ'] at ih
    rw [List.append_assoc] at ih
    apply M_deterministic_of_terminal_stack at ih
    obtain ⟨w', hw', hr ⟩ := ih
    have hpart₁ : (M G).reaches ⟨Q.loop, w,α⟩ ⟨Q.loop, w', nonterminal r.input :: q ⟩ := by
      rw [hα', List.append_assoc, hw']
      apply M_consumes_terminal_string p  _
    have hpart₂ : (M G).reaches ⟨Q.loop, w', nonterminal r.input :: q⟩ ⟨Q.loop, w', r.output ++ q⟩ := by
      rw [reaches_iff_reachesN]
      use 1
      exact M_consumes_nonterminal hrg _ q
    have := reaches_trans hpart₁ hpart₂
    exact reaches_trans this hr


theorem G_derives_of_M_reaches {α : List (Symbol T G.NT)} {w : List T}
    (h: (M G).reaches ⟨Q.loop,w,α⟩ ⟨Q.loop,[], []⟩):
    G.Derives α (w.map terminal) := by
  sorry

theorem G_derives_iff_M_reaches {α : List (Symbol T G.NT)} {w : List T} :
    G.Derives α (w.map terminal) ↔
    (M G).reaches ⟨Q.loop,w, α⟩ ⟨Q.loop,[], []⟩ := by
  sorry
end section


theorem pda_of_cfg (G : ContextFreeGrammar T) [Fintype G.NT] :
    G.language = (M G).acceptsByEmptyStack := by
  sorry
