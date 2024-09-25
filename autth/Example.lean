import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.RegularExpressions

#check RegularExpression

inductive Alphabet where
  | a | b | c

open Alphabet RegularExpression

#check [a, a, b]
#check comp ( star ( char a ) ) ( star ( char b ) )

/-- Example theorem showing that `aab` is in `a*b*`. -/
theorem my_first_theorem: [a,a,b] ∈ matches' ( comp ( star ( char a ) ) ( star ( char b ) ) ) := by
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

inductive Nonterminals where
  | S

#check Symbol
#check ( Symbol Alphabet Nonterminals )

def mysymbol : ( Symbol Alphabet Nonterminals ) := ( Symbol.terminal Alphabet.a )

def myfirstrule : ( ContextFreeRule Alphabet Nonterminals ) where
  input := Nonterminals.S
  output := List.nil

def mysecondrule : (ContextFreeRule Alphabet Nonterminals) where
  input := Nonterminals.S
  output := [ ( Symbol.terminal Alphabet.a ) ,
    ( Symbol.nonterminal  Nonterminals.S ),
    ( Symbol.terminal Alphabet.b ) ]

#check ContextFreeGrammar Alphabet

def mygrammar : ( ContextFreeGrammar Alphabet ) where
  NT := Nonterminals
  initial := Nonterminals.S
  rules := [ myfirstrule, mysecondrule ]

#print mygrammar
#print myfirstrule
#print mysecondrule

#check ContextFreeGrammar.language mygrammar
#check [a,b]

/-- example theorem showing that ε is in the language of the grammar S -> ε | aSb -/
theorem my_second_theorem : List.nil ∈ ( ContextFreeGrammar.language mygrammar ) := by
  apply (ContextFreeGrammar.mem_language_iff mygrammar []).mpr
  apply ContextFreeGrammar.Produces.single
  use myfirstrule
  constructor
  · unfold mygrammar
    simp
  · refine (ContextFreeRule.rewrites_iff [Symbol.nonterminal mygrammar.initial]
      (List.map Symbol.terminal [])).mpr
      ?h.right.a
    use [], []
    simp
    unfold mygrammar myfirstrule
    simp

/-- example theorem showing that ab is in the language of the grammar S -> ε | aSb -/
theorem my_third_theorem : [a,b] ∈ ( ContextFreeGrammar.language mygrammar ) := by
  apply (ContextFreeGrammar.mem_language_iff mygrammar [a, b]).mpr
  have fst : mygrammar.Derives [Symbol.nonterminal mygrammar.initial]
    [ ( Symbol.terminal Alphabet.a ) ,
    ( Symbol.nonterminal  Nonterminals.S ),
    ( Symbol.terminal Alphabet.b ) ] := by
    apply ContextFreeGrammar.Produces.single
    use mysecondrule
    constructor
    · unfold mygrammar
      simp
    · apply (ContextFreeRule.rewrites_iff [Symbol.nonterminal mygrammar.initial]
        [Symbol.terminal a, Symbol.nonterminal Nonterminals.S, Symbol.terminal b]).mpr
      use [], []
      simp
      unfold mygrammar mysecondrule
      simp
  have snd : mygrammar.Derives [ ( Symbol.terminal Alphabet.a ) ,
    ( Symbol.nonterminal  Nonterminals.S ),
    ( Symbol.terminal Alphabet.b ) ] [ ( Symbol.terminal Alphabet.a ) ,
    ( Symbol.terminal Alphabet.b ) ] := by
    apply ContextFreeGrammar.Produces.single
    use myfirstrule
    constructor
    · unfold mygrammar
      simp
    · apply (ContextFreeRule.rewrites_iff [Symbol.terminal a, Symbol.nonterminal Nonterminals.S, Symbol.terminal b]
      [Symbol.terminal a, Symbol.terminal b]).mpr
      use [Symbol.terminal a], [Symbol.terminal b]
      unfold myfirstrule
      simp
  exact ContextFreeGrammar.Derives.trans fst snd

/-- example theorem showing that aab is not in the language of the grammar S -> ε | aSb -/
theorem my_fourth_theorem : [a,a,b] ∉ ( ContextFreeGrammar.language mygrammar ) := by
 sorry

--#min_imports
