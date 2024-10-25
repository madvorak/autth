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

open alph
open nt
open Symbol
open ContextFreeGrammar

abbrev a_ : Symbol alph nt := terminal a
abbrev b_ : Symbol alph nt := terminal b
abbrev S_ : Symbol alph nt := nonterminal S

def G : ContextFreeGrammar alph := ⟨nt, S, [
    ⟨S, []⟩,
    ⟨nt.S, [a_, S_, b_]⟩
  ]⟩

example : [a,a,b,b] ∈ G.language := by
  rw [mem_language_iff]
  simp
  rw [Derives]
  apply Relation.ReflTransGen.tail
  case b => exact [a_, a_, S_, b_, b_]
  case a =>
    apply Relation.ReflTransGen.tail
    case b => exact [a_,S_,b_]
    case a =>
      apply Relation.ReflTransGen.tail
      case b => exact [S_]
      case a => rw [(by rfl : G.initial = S)]
      case a =>
        use ⟨nt.S, [a_, S_, b_]⟩
        constructor
        · simp [G]
        · apply (ContextFreeRule.rewrites_iff [S_] [a_, S_, b_]).mpr
          use []
          use []
          simp
    case a =>
      use ⟨nt.S, [a_, S_, b_]⟩
      constructor
      · simp [G]
      · apply ContextFreeRule.Rewrites.cons (a_)
        apply ContextFreeRule.Rewrites.head [b_]
  case a =>
    use ⟨nt.S, []⟩
    simp [G]
    apply ContextFreeRule.Rewrites.cons (a_)
    apply ContextFreeRule.Rewrites.cons (a_)
    apply ContextFreeRule.Rewrites.head [b_, b_]
