import Mathlib.Computability.RegularExpressions

-- a language has a regexp iff it has a DFA
-- existence and uniqueness of minimal DFA
-- sum-star equation
-- product-star equation
-- pumping lemma for linear languages
-- pumping lemma for context-free languages

#check RegularExpression

inductive Alphabet where
  | a | b | c

open Alphabet RegularExpression

#check [a, a, b]

#check comp ( star ( char a ) ) ( star ( char b ) )

/- Example theorem showing that `aab` is in `a*b*`. -/
theorem my_example_theorem: [a,a,b] ∈ matches' ( comp ( star ( char a ) ) ( star ( char b ) ) ) := by
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

#min_imports
