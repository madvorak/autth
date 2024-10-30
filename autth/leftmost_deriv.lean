import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Tactic

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
        v = p.map terminal ++ r.output ++ q := by
  induction hr with
  | head s =>
    use [], s
    simp
  | cons x _ ih =>
    obtain ⟨p, q, hpq⟩ := ih
    use x::p, q
    simp [hpq]

theorem RewritesLeftmost.rewrites_leftmost_of_exists_parts (r : ContextFreeRule T N)
    (p : List T) (q : List (Symbol T N)) :
    r.RewritesLeftmost (p.map terminal ++ [nonterminal r.input] ++ q)
      (p.map terminal ++ r.output ++ q) := by
  induction p with
  | nil =>
    exact RewritesLeftmost.head q
  | cons x p' ih =>
    rw [List.map_cons]
    exact cons x ih

theorem RewritesLeftmost.rewrites_leftmost_iff {r : ContextFreeRule T N} {u v : List (Symbol T N)} :
    r.RewritesLeftmost u v ↔
    ∃ (p : List T) (q : List (Symbol T N)),
      u = p.map terminal ++ [nonterminal r.input] ++ q ∧
      v = p.map terminal ++ r.output ++ q := by
  constructor
  · exact exists_parts
  · intro ⟨p, q, hu, hv⟩
    rw [hu, hv]
    exact rewrites_leftmost_of_exists_parts r p q

theorem RewritesLeftmost.rewrite_terminal (r : ContextFreeRule T N) (w : List T)
    (u : List (Symbol T N)): ¬ RewritesLeftmost r (w.map terminal) u := by
  intro h
  rw [rewrites_leftmost_iff] at h
  obtain ⟨p,q,h₁,_⟩ := h
  symm at h₁
  rw [List.append_eq_map] at h₁
  obtain ⟨l₁,_,_,h,_⟩ := h₁
  symm at h
  rw [List.append_eq_map] at h
  obtain ⟨_,l₂,_,_,h⟩ := h
  rcases l₂ with _|⟨x, xs⟩ <;> simp at h

theorem RewritesLeftmost.append_left {r : ContextFreeRule T N}
    {v w : List (Symbol T N)} (hr : r.RewritesLeftmost v w) (p : List T) :
    r.RewritesLeftmost (p.map terminal ++ v) (p.map terminal ++ w) := by
  induction p with
  | nil => simp [hr]
  | cons x _ ih => exact ih.cons x

theorem RewritesLeftmost.append_right {r : ContextFreeRule T N}
    {v w : List (Symbol T N)} (hr : r.RewritesLeftmost v w) (p : List (Symbol T N)) :
    r.RewritesLeftmost (v ++ p) (w ++ p) := by
  obtain ⟨s, t, rfl, rfl⟩ := hr.exists_parts
  simpa using rewrites_leftmost_of_exists_parts r s (t ++ p)

theorem RewritesLeftmost.rewrites_of_rewrites_leftmost {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (hr : r.RewritesLeftmost u v) : r.Rewrites u v := by
  induction hr with
  | head s => exact Rewrites.head _
  | cons x _ ih => exact Rewrites.cons (terminal x) ih

theorem rewrites_leftmost_cons {r : ContextFreeRule T N} {x : Symbol T N} {v u : List (Symbol T N)}
    (h : r.RewritesLeftmost (x :: v) u) :
    (∃ (u₁ u₂ : List (Symbol T N)), u = u₁ ++ u₂ ∧ (r.RewritesLeftmost [x] u₁ ∧ u₂ = v)) ∨
    (∃ (w₁ : List T) (u₂ : List (Symbol T N)),
      u = (w₁.map terminal) ++ u₂ ∧ ([x] = w₁.map terminal ∧ r.RewritesLeftmost v u₂)) := by
  rcases h with ⟨_⟩|@⟨x,_,s₂,hrs⟩
  · left
    refine ⟨r.output, v, rfl, ?_, rfl⟩
    convert RewritesLeftmost.head []
    simp
  · right
    exact ⟨[x], s₂, by simp, by simp, hrs⟩

theorem rewrites_leftmost_append {r : ContextFreeRule T N} {v₁ v₂ u : List (Symbol T N)}
    (h : r.RewritesLeftmost (v₁ ++ v₂) u) :
    (∃ (u₁ u₂ : List (Symbol T N)), u = u₁ ++ u₂ ∧ (r.RewritesLeftmost v₁ u₁ ∧ u₂ = v₂)) ∨
    (∃ (w₁ : List T)(u₂ : List (Symbol T N)),
      u = w₁.map terminal ++ u₂ ∧ (v₁ = w₁.map terminal ∧ r.RewritesLeftmost v₂ u₂)) := by
  induction v₁ generalizing u with
  | nil =>
    right
    exact ⟨[], u, by simp, by simp, h⟩
  | cons x v₁' ih =>
    rw [List.cons_append] at h
    apply rewrites_leftmost_cons at h
    obtain ⟨u₁, u₂, h⟩|⟨w₁,u₂, h⟩ := h
    · left
      use u₁++v₁', v₂
      refine ⟨by simp_all, ?_, rfl⟩
      rw [←List.singleton_append]
      apply RewritesLeftmost.append_right
      exact h.2.1
    · obtain ⟨u₂₁,u₂₂,hu⟩|⟨w₂₁,u₂₂,hu⟩ := ih h.2.2
      · left
        use w₁.map terminal ++ u₂₁, v₂
        refine ⟨by simp_all, ?_, rfl⟩
        rw [←List.singleton_append,h.2.1]
        apply RewritesLeftmost.append_left
        exact hu.2.1
      · right
        use (w₁++w₂₁), u₂₂
        refine ⟨by simp_all, ?_, hu.2.2⟩
        · rw [←List.singleton_append, h.2.1, hu.2.1]
          simp

theorem rewrites_cons {r : ContextFreeRule T N} {x : Symbol T N} {v u : List (Symbol T N)}
    (h : r.Rewrites (x :: v) u) :
    ∃ (u₁ u₂ : List (Symbol T N)), u = u₁ ++ u₂ ∧
      ((r.Rewrites [x] u₁ ∧ u₂ = v) ∨ (r.Rewrites v u₂ ∧ [x] = u₁)) := by
  rcases h with ⟨s⟩|@⟨x,_,s₂,hrs⟩
  · use r.output, v
    refine ⟨rfl, ?_⟩
    left
    refine ⟨?_, rfl⟩
    rw [rewrites_iff]
    use [], []
    simp
  · use [x], s₂
    constructor
    · simp
    · right
      exact ⟨hrs, rfl⟩

theorem rewrites_append {r : ContextFreeRule T N}{v₁ v₂ u : List (Symbol T N)}
    (h : r.Rewrites (v₁ ++ v₂) u) :
    ∃ (u₁ u₂ : List (Symbol T N)), u = u₁ ++ u₂ ∧
      ((r.Rewrites v₁ u₁ ∧ v₂ = u₂) ∨ (r.Rewrites v₂ u₂ ∧ v₁ = u₁)) := by
  induction v₁ generalizing u with
  | nil => exact ⟨[], u, rfl, Or.inr ⟨h, rfl⟩⟩
  | cons x v₁ ih =>
    rw [List.cons_append] at h
    apply rewrites_cons at h
    obtain ⟨u₁,u₂,hu⟩ := h
    rcases hu.2 with hu'|hu'
    · refine ⟨u₁++v₁, v₂, ?_, ?_⟩
      · simp [hu.1, hu'.2]
      · left
        exact ⟨hu'.1.append_right v₁, rfl⟩
    · obtain ⟨s₁,s₂,hs,hs'⟩ := ih hu'.1
      rcases hs' with hs'|hs'
      · refine ⟨x::s₁, s₂, ?_, ?_⟩
        · rw [List.cons_append,←hs, ←List.singleton_append,hu'.2]
          exact hu.1
        · left
          exact ⟨hs'.1.append_left [x], hs'.2⟩
      · refine ⟨x::s₁, s₂, ?_, ?_⟩
        · rw [List.cons_append,←hs, ←List.singleton_append,hu'.2]
          exact hu.1
        · right
          exact ⟨hs'.1, congr_arg _ hs'.2⟩

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

theorem produces_of_produces_leftmost {u v : List (Symbol T g.NT)} (h : g.ProducesLeftmost u v):
      g.Produces u v := by
  obtain ⟨r,hr⟩ := h
  use r, hr.1
  apply ContextFreeRule.RewritesLeftmost.rewrites_of_rewrites_leftmost
  exact hr.2

theorem derives_of_derives_leftmost {u v : List (Symbol T g.NT)}(h:g.DerivesLeftmost u v) :
    g.Derives u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head h₁ _ ih => exact Produces.trans_derives (produces_of_produces_leftmost h₁) ih

theorem derives_leftmost_cons {x : Symbol T g.NT} {v u : List (Symbol T g.NT)}
    (h : g.DerivesLeftmost (x :: v) u) :
    (∃ (u' : List (Symbol T g.NT)), u = u' ++ v ∧ g.DerivesLeftmost [x] u') ∨
    (∃ (w₁ : List T) (u₂ : List (Symbol T g.NT)), u = w₁.map terminal ++ u₂ ∧
      g.DerivesLeftmost [x] (w₁.map terminal) ∧ g.DerivesLeftmost v u₂) := by
  induction h with
  | refl =>
    left
    use [x]
    exact ⟨by simp, by rfl⟩
  | tail _ last ih =>
    obtain ⟨u₁,hu⟩|⟨w₁,u₂,hu⟩ := ih
    · rw [hu.1] at last
      obtain ⟨r,hr,last⟩ := last
      obtain ⟨o₁,o₂,ho⟩|⟨w₁,o₂,ho⟩ := ContextFreeRule.rewrites_leftmost_append last
      · left
        exact ⟨o₁, by simp_all, hu.2.trans_produces ⟨r,hr,ho.2.1⟩⟩
      · right
        exact ⟨w₁, o₂, by simp_all, by simp_all, ProducesLeftmost.single ⟨r,hr,ho.2.2⟩⟩
    · rw [hu.1] at last
      right
      use w₁
      obtain ⟨r,hr,last⟩ := last
      obtain ⟨o₁,o₂,ho⟩|⟨w₁',o₂,ho⟩ := ContextFreeRule.rewrites_leftmost_append last
      · exfalso
        exact ContextFreeRule.RewritesLeftmost.rewrite_terminal _ _ _ ho.2.1
      · exact ⟨o₂, by simp_all, hu.2.1, hu.2.2.trans_produces ⟨r,hr,ho.2.2⟩⟩

theorem derives_leftmost_append {v₁ v₂ u : List (Symbol T g.NT)}
    (h : g.DerivesLeftmost (v₁ ++ v₂) u) :
    (∃ (u' : List (Symbol T g.NT)), u = u' ++ v₂ ∧ g.DerivesLeftmost v₁ u') ∨
    (∃ (w₁ : List T) (u₂ : List (Symbol T g.NT)), u = w₁.map terminal ++ u₂ ∧
      g.DerivesLeftmost v₁ (w₁.map terminal) ∧ g.DerivesLeftmost v₂ u₂) := by
  induction v₁ generalizing u with
  | nil =>
    right
    exact ⟨[], u, by simp_all, by rfl, by simp_all⟩
  | cons x v₁' ih =>
    apply derives_leftmost_cons at h
    obtain ⟨u₁,hu⟩|⟨w₁,u₂,hu⟩ := h
    · left
      exact ⟨u₁++v₁', by simp [hu], hu.2.append_right _⟩
    · obtain ⟨u₂₁,hu₂⟩|⟨w₂₁,u₂₂,hu₂⟩ := ih hu.2.2
      · left
        exact ⟨w₁.map terminal ++ u₂₁, by simp_all,
          (hu.2.1.append_right v₁').trans (hu₂.2.append_left w₁)⟩
      · right
        use w₁++w₂₁, u₂₂
        rw [List.map_append]
        exact ⟨by simp_all, (hu.2.1.append_right v₁').trans (hu₂.2.1.append_left w₁), hu₂.2.2⟩

theorem derives_cons {x : Symbol T g.NT} {v u : List (Symbol T g.NT)} (h : g.Derives (x :: v) u) :
    ∃ (u₁ u₂ : List (Symbol T g.NT)), u = u₁ ++ u₂ ∧ g.Derives [x] u₁ ∧ g.Derives v u₂ := by
  induction h with
  | refl =>
    use [x], v
    simp_all [Derives.refl]
  | tail h₁ h₂ ih =>
    obtain ⟨u₁,u₂,hu₁,hu₂⟩ := ih
    rw [hu₁] at h₁ h₂
    obtain ⟨r,hr,huc⟩ := h₂
    obtain ⟨v₁,v₂,huv⟩ := ContextFreeRule.rewrites_append huc
    use v₁, v₂
    use huv.1
    rcases huv.2 with huv|huv
    · use hu₂.1.trans_produces ⟨r, hr, huv.1⟩
      convert hu₂.2
      exact huv.2.symm
    · rw [huv.2.symm]
      exact ⟨hu₂.1, hu₂.2.trans_produces ⟨r, hr, huv.1⟩⟩

theorem derives_leftmost_iff {w : List T} {α : List (Symbol T g.NT)} :
    g.DerivesLeftmost α (w.map terminal) ↔ g.Derives α (w.map terminal) := by
  constructor
  · exact derives_of_derives_leftmost
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head first _ ih =>
      obtain ⟨r,hr,first⟩ := first
      rw [ContextFreeRule.rewrites_iff] at first
      obtain ⟨v₁,v₂,hv⟩ := first
      rw [hv.2, List.append_assoc] at ih
      obtain ⟨u₁,hu⟩|⟨w₁,u₂,hu⟩ := derives_leftmost_append ih
      · obtain ⟨w₁₁, w₂₂, hw⟩ := (List.map_eq_append _).mp hu.1
        have d₁ : g.DerivesLeftmost ([nonterminal r.input] ++ v₂) (r.output ++ v₂) := by
          apply ProducesLeftmost.single
          use r, hr
          rw [ContextFreeRule.RewritesLeftmost.rewrites_leftmost_iff]
          use [], v₂
          simp
        have d₂ := DerivesLeftmost.append_left d₁ w₁₁
        rw [hw.2.1] at d₂
        have d₃ :=  DerivesLeftmost.append_right hu.2 ([nonterminal r.input] ++ v₂)
        convert DerivesLeftmost.trans d₃ d₂ <;> simp_all
      · have d₁ : g.DerivesLeftmost ([nonterminal r.input] ++ v₂) (r.output ++ v₂) := by
          apply ProducesLeftmost.single
          use r, hr
          rw [ContextFreeRule.RewritesLeftmost.rewrites_leftmost_iff]
          use [], v₂
          simp
        have d₂ := (d₁.trans hu.2.2).append_left w₁
        have d₃ := hu.2.1.append_right ([nonterminal r.input] ++ v₂)
        convert DerivesLeftmost.trans d₃ d₂ <;> simp_all

end ContextFreeGrammar
