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
