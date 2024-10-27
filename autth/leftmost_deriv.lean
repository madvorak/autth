import Mathlib.Computability.ContextFreeGrammar

universe uT uN
variable {T : Type uT}
variable {N : Type uN}

namespace ContextFreeRule
open Symbol

inductive RewritesLeftmost (r : ContextFreeRule T N) : List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replaced nonterminal is the leftmost symbol -/
  | head (s : List (Symbol T N)) :
      r.RewritesLeftmost (Symbol.nonterminal r.input :: s) (r.output ++ s)
  /-- There are terminals further left than the replaced symbol -/
  | cons (x : T) {s₁ s₂ : List (Symbol T N)} (hrs : RewritesLeftmost r s₁ s₂) :
      r.RewritesLeftmost (terminal x :: s₁) (terminal x :: s₂)

theorem RewritesLeftmost.exists_parts {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (hr : r.RewritesLeftmost u v) :
      ∃ (p : List T) (q : List (Symbol T N)),
        u = p.map terminal ++ [nonterminal r.input] ++ q ∧
        v = p.map terminal ++ r.output ++ q := by sorry

theorem RewritesLeftmost.rewrites_leftmost_of_exists_parts {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (hr : r.RewritesLeftmost u v) (p : List T) (q : List (Symbol T N)) :
    r.RewritesLeftmost (p.map terminal ++ [nonterminal r.input] ++ q)
      (p.map terminal ++ r.output ++ q) :=
  by sorry

theorem RewritesLeftmost.rewrites_leftmost_iff {r : ContextFreeRule T N} {u v : List (Symbol T N)} :
    r.RewritesLeftmost u v ↔
    ∃ (p : List T) (q : List (Symbol T N)),
      u = p.map terminal ++ [nonterminal r.input] ++ q ∧
      v = p.map terminal ++ r.output ++ q :=
  by sorry

theorem RewritesLeftmost.append_left {r : ContextFreeRule T N}
    {v w : List (Symbol T N)} (hr : r.RewritesLeftmost v w) (p : List T) :
    r.RewritesLeftmost (p.map terminal ++ v) (p.map terminal ++ w) :=
  by sorry

theorem RewritesLeftmost.append_right {r : ContextFreeRule T N}
    {v w : List (Symbol T N)} (hr : r.RewritesLeftmost v w) (p : List (Symbol T N)) :
    r.RewritesLeftmost (v ++ p) (w ++ p) :=
  by sorry

end ContextFreeRule

namespace ContextFreeGrammar
open Symbol

/-- Given a context-free grammar `g` and strings `u` and `v`
`g.ProducesLeftmost u v` means that one application of a rule from `g` to the leftmost nonterminal
of `u` send `u` to `v`. -/
def ProducesLeftmost (g : ContextFreeGrammar.{uN} T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.RewritesLeftmost u v

/-- Given a context-free grammar `g` and strings `u` and `v`
`g.DerivesLeftmost u v` means that `g` can transform `u` to `v` in some number of rewriting steps,
by applying the transformation always to the leftmost symbol of `u`. -/
abbrev DerivesLeftmost (g : ContextFreeGrammar.{uN} T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.ProducesLeftmost

variable {g : ContextFreeGrammar.{uN} T}

@[refl]
lemma DerivesLeftmost.refl (w : List (Symbol T g.NT)) : g.DerivesLeftmost w w :=
  Relation.ReflTransGen.refl

lemma ProducesLeftmost.single {v w : List (Symbol T g.NT)} (hvw : g.ProducesLeftmost v w) :
    g.DerivesLeftmost v w :=
  Relation.ReflTransGen.single hvw

@[trans]
lemma DerivesLeftmost.trans {u v w : List (Symbol T g.NT)} (huv : g.DerivesLeftmost u v)
    (hvw : g.DerivesLeftmost v w) :
    g.DerivesLeftmost u w :=
  Relation.ReflTransGen.trans huv hvw

lemma DerivesLeftmost.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.DerivesLeftmost u v) (hvw : g.ProducesLeftmost v w) :
    g.DerivesLeftmost u w :=
  huv.trans hvw.single

lemma Leftmost.trans_derives {u v w : List (Symbol T g.NT)}
    (huv : g.ProducesLeftmost u v) (hvw : g.DerivesLeftmost v w) :
    g.DerivesLeftmost u w :=
  huv.single.trans hvw

lemma DerivesLeftmost.eq_or_head {u w : List (Symbol T g.NT)} (huw : g.DerivesLeftmost u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.ProducesLeftmost u v ∧ g.DerivesLeftmost v w :=
  Relation.ReflTransGen.cases_head huw

lemma DerivesLeftmost.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.DerivesLeftmost u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.DerivesLeftmost u v ∧ g.ProducesLeftmost v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr

/-- Add extra prefix to context-free leftmost producing. -/
lemma ProducesLeftmost.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.ProducesLeftmost v w) (p : List T) :
    g.ProducesLeftmost (p.map terminal ++ v) (p.map terminal ++ w) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩

/-- Add extra postfix to context-free leftmost producing. -/
lemma ProducesLeftmost.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.ProducesLeftmost v w) (p : List (Symbol T g.NT)) :
    g.ProducesLeftmost (v ++ p) (w ++ p) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩

/-- Add extra prefix to context-free leftmost deriving. -/
lemma DerivesLeftmost.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesLeftmost v w) (p : List T) :
    g.DerivesLeftmost (p.map terminal ++ v) (p.map terminal ++ w) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free leftmost deriving. -/
lemma DerivesLeftmost.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesLeftmost v w) (p : List (Symbol T g.NT)) :
    g.DerivesLeftmost (v ++ p) (w ++ p) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p

theorem DerivesLeftmost_iff {w : List T}{α : List (Symbol T g.NT)}:
    g.DerivesLeftmost α (w.map terminal)  ↔ g.Derives α (w.map terminal) := by
  sorry

end ContextFreeGrammar
