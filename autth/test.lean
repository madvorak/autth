import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Data.List.Join
import Mathlib.Util.Delaborators
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.EpsilonNFA

inductive alph where
  | a
  | b

inductive nt where
  | S

open Symbol
open ContextFreeGrammar

abbrev a : Symbol alph nt := terminal alph.a
abbrev b : Symbol alph nt := terminal alph.b
abbrev S : Symbol alph nt := nonterminal nt.S

def G : ContextFreeGrammar alph := ⟨nt, nt.S, [
    ⟨nt.S, []⟩,
    ⟨nt.S, [a, S, b]⟩
  ]⟩

example : [alph.a, alph.a, alph.b, alph.b] ∈ G.language := by
  rw [mem_language_iff, List.map_cons]
  apply Derives.trans_produces (v := [a, a, S, b, b])
  · apply Derives.trans_produces (v := [a, S, b])
    · apply Derives.trans_produces (v := [S])
      · rfl
      · use ⟨nt.S, [a, S, b]⟩
        constructor
        · simp [G]
        · rw [ContextFreeRule.rewrites_iff]
          use []
          use []
          simp
    · use ⟨nt.S, [a, S, b]⟩
      constructor
      · simp [G]
      · right
        left
  · use ⟨nt.S, []⟩
    simp [G]
    right
    right
    left
