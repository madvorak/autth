import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.RegularExpressions

#check RegularExpression

inductive Alphabet where
  | a | b | c

section
open Alphabet RegularExpression

#check [a, a, b]
#check comp ( star ( char a ) ) ( star ( char b ) )

/-- Example theorem showing that `aab` is in `a*b*`. -/
private theorem my_first_theorem: [a,a,b] ∈ matches' ( comp ( star ( char a ) ) ( star ( char b ) ) ) := by
  simp
  refine Language.mem_mul.mpr ?_
  use [a,a]
  constructor
  refine Language.mem_kstar_iff_exists_nonempty.mpr ?h.left.a
  use [[a],[a]]
  simp
  rfl
  use [b]
  constructor
  refine Language.mem_kstar_iff_exists_nonempty.mpr ?_
  use [[b]]
  simp only [List.join_cons, List.join_nil, List.singleton_append, List.mem_singleton, ne_eq,
    forall_eq, List.cons_ne_self, not_false_eq_true, and_true, true_and]
  rfl
  simp
end

private inductive Nonterminals where
  | S

#check Symbol
#check ( Symbol Alphabet Nonterminals )

private abbrev a : Symbol Alphabet Nonterminals := .terminal Alphabet.a
private abbrev b : Symbol Alphabet Nonterminals := .terminal Alphabet.b
private abbrev c : Symbol Alphabet Nonterminals := .terminal Alphabet.c
private abbrev S : Symbol Alphabet Nonterminals := .nonterminal Nonterminals.S

private def mysymbol : ( Symbol Alphabet Nonterminals ) := ( Symbol.terminal Alphabet.a )

private def myfirstrule : ( ContextFreeRule Alphabet Nonterminals ) where
  input := Nonterminals.S
  output := List.nil

private def mysecondrule : (ContextFreeRule Alphabet Nonterminals) where
  input := Nonterminals.S
  output := [a, S, b]

#check ContextFreeGrammar Alphabet

private def mygrammar : ( ContextFreeGrammar Alphabet ) where
  NT := Nonterminals
  initial := Nonterminals.S
  rules := [ myfirstrule, mysecondrule ]

#print mygrammar
#print myfirstrule
#print mysecondrule

#check ContextFreeGrammar.language mygrammar
#check [a,b]

/-- example theorem showing that ε is in the language of the grammar S -> ε | aSb -/
private theorem my_second_theorem : List.nil ∈ mygrammar.language := by
  apply (ContextFreeGrammar.mem_language_iff mygrammar []).mpr
  apply ContextFreeGrammar.Produces.single
  use myfirstrule
  constructor
  · unfold mygrammar
    simp
  · rw [ContextFreeRule.rewrites_iff]
    use [], []
    simp
    unfold mygrammar myfirstrule
    simp

/-- example theorem showing that ab is in the language of the grammar S -> ε | aSb -/
private theorem my_third_theorem : [.a, .b] ∈ mygrammar.language := by
  apply (ContextFreeGrammar.mem_language_iff mygrammar [.a, .b]).mpr
  have fst : mygrammar.Derives [Symbol.nonterminal mygrammar.initial] [a, S, b] := by
    apply ContextFreeGrammar.Produces.single
    use mysecondrule
    constructor
    · unfold mygrammar
      simp
    · rw [ContextFreeRule.rewrites_iff]
      use [], []
      simp
      unfold mygrammar mysecondrule
      simp
  have snd : mygrammar.Derives [a, S, b] [a, b] := by
    apply ContextFreeGrammar.Produces.single
    use myfirstrule
    constructor
    · unfold mygrammar
      simp
    · apply (ContextFreeRule.rewrites_iff [a, S, b]
      [a, b]).mpr
      use [a], [b]
      unfold myfirstrule
      simp
  exact ContextFreeGrammar.Derives.trans fst snd

/-- example theorem showing that aab is not in the language of the grammar S -> ε | aSb -/
private theorem my_fourth_theorem : [.a, .a, .b] ∉ mygrammar.language := by
 sorry

--#min_imports
