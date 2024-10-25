import autth.PDA
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

-- In this whole section G will be the grammar we want to convert to a pda
variable {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)

structure Q where loop ::
abbrev S := Symbol T G.NT
abbrev PDA' := PDA Q T (S G)

abbrev transition_fun (_ : Q) (a : T) (Z : S G) : Set (Q × List (S G)) :=
  match Z with
  | terminal b => if a=b then {(Q.loop, [])} else {}
  | _ => ∅

abbrev transition_fun' (_ : Q) (Z : S G) : Set (Q × List (S G)) :=
  match Z with
  | nonterminal N => { (Q.loop, α) | (α : List (S G)) (_ : ⟨N, α⟩ ∈ G.rules) }
  | _ => ∅

-- Martin: This is not a good name for a function.
abbrev M : PDA' G := {
  initial_state := Q.loop
  start_symbol := nonterminal G.initial
  final_states := ∅
  transition_fun := transition_fun G
  transition_fun' := transition_fun' G
}

theorem M_consumes_terminal (a : T) (w : List T) (α : List (S G)):
    (M G).reachesN 1 ⟨Q.loop, a::w, terminal a :: α⟩ ⟨Q.loop, w, α⟩ := by
  rw [reachesN_one,step]
  apply Set.mem_union_left
  rw [Set.mem_setOf]
  use Q.loop, []
  simp [M, CFG_to_PDA.transition_fun]


theorem M_reaches_off_G_derives (α : List (Symbol T G.NT)) (w : List T)
    (h : G.Derives α (w.map terminal)):
    (M G).reaches ⟨Q.loop, w, α⟩ ⟨Q.loop, [], []⟩ := by
  generalize def_s : w.map terminal = s at h
  induction' h using Relation.ReflTransGen.head_induction_on with α β hα hβ ih
  case refl =>
    induction' w with a w' ih generalizing s
    case nil =>
      rw [←def_s]
      dsimp [reaches]
      use 0
      simp [stepSetN]
    case cons =>
      rw [List.map_cons] at def_s
      have := ih (w'.map terminal) rfl
      rw [reaches_iff_reachesN] at this
      obtain ⟨n, hw'⟩ := this
      rw [reaches_iff_reachesN]
      use n+1
      rw [←reachesN_iff_split_first]
      use ⟨Q.loop, w', w'.map terminal⟩
      refine ⟨?_,?_⟩
      · rw [←def_s]
        apply M_consumes_terminal
      · exact hw'
  sorry


theorem G_derives_of_M_reaches {α : List (Symbol T G.NT)} {w : List T}
    (h: (M G).reaches ⟨Q.loop,w,α⟩ ⟨Q.loop,[], []⟩):
    G.Derives α (w.map terminal) := by
  sorry

theorem G_derives_iff_M_reaches {α : List (Symbol T G.NT)} {w : List T} :
    G.Derives α (w.map terminal) ↔
    (M G).reaches ⟨Q.loop,w, α⟩ ⟨Q.loop,[], []⟩ := by
  sorry

theorem pda_of_cfg (L : Language T) : L = G.language → L = (M G).acceptsByEmptyStack := by sorry
