import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Data.List.Join
import Mathlib.Util.Delaborators
import Mathlib.Computability.ContextFreeGrammar

import Mathlib.Computability.EpsilonNFA

structure PDA  (Q: Type)(T: Type)(S: Type) where
  initial_state : Q
  start_symbol : S
  final_states : Set Q
  transition_fun : Q → T → S → Set (Q × List S)
  transition_fun' : Q → S → Set (Q × List S)

namespace PDA

@[ext]
structure conf
    {Q T S: Type} (p : PDA Q T S) where
  state : Q
  input : List T
  stack : List S

namespace conf

def appendInput  {Q T S: Type} {pda : PDA Q T S}(r : conf pda)(x : List T): conf pda :=
  ⟨r.state,r.input++x,r.stack⟩

def appendStack  {Q T S: Type} {pda : PDA Q T S}(r : conf pda)(β : List S): conf pda :=
  ⟨r.state,r.input,r.stack++β⟩

def stackPostfix' {Q T S: Type} {pda : PDA Q T S}(r : conf pda)(β : List S): Prop :=
  ∃α:List S, r.stack = α++β

def stackPostfix {Q T S: Type} {pda : PDA Q T S}(r : conf pda)(β : List S): Prop :=
  ∃α:List S, α.length > 0 ∧ r.stack = α++β

end conf

def step {Q T S : Type} {pda : PDA Q T S} (r₁ : conf pda) : Set (conf pda) :=
  match r₁ with
    | ⟨q,a::w,Z::α⟩ =>
        {r₂ : conf pda | ∃ (p:Q) (β:List S), (p,β) ∈ pda.transition_fun q a Z ∧
                          r₂=⟨p, w, (β ++ α)⟩ } ∪
        {r₂ : conf pda | ∃(p:Q)(β:List S), (p,β) ∈ pda.transition_fun' q Z ∧
                          r₂=⟨p, a :: w, (β ++ α)⟩}
    | ⟨q,Nil,Z::α⟩ => {r₂ : conf pda | ∃(p:Q)(β:List S), (p,β) ∈ pda.transition_fun' q Z ∧
                                         r₂=⟨p, Nil, (β ++ α)⟩}
    | ⟨q,w,Nil⟩ => {r₂ : conf pda | r₂ = ⟨q,w,Nil⟩} -- Empty stack

def stepSet {Q T S : Type} {pda : PDA Q T S} (R : Set (conf pda)) : Set (conf pda) :=
  ⋃ r ∈ R , step r

def stepSetN {Q T S : Type} {pda : PDA Q T S} (n : ℕ) (R : Set (conf pda))  : Set (conf pda) :=
  match n with
  | 0 => R
  | Nat.succ m => stepSet (stepSetN m R)

inductive reaches' {Q T S : Type} {pda : PDA Q T S}  : conf pda→ conf pda→Prop :=
  | base : (r₁ : conf pda) → reaches' r₁ r₁
  | step : {r₁ r' r₂ : conf pda} → (r'∈ step r₁) → (reaches' r' r₂) → reaches' r₁ r₂

def reachesN {Q T S : Type} {pda : PDA Q T S} (n : ℕ) (r₁ : conf pda)(r₂ : conf pda) : Prop :=
  r₂ ∈ stepSetN n {r₁}

def reaches {Q T S : Type} {pda : PDA Q T S}  (r₁ : conf pda)(r₂ : conf pda) : Prop :=
  ∃n:ℕ, r₂ ∈ stepSetN n {r₁}


def acceptsByEmptyStack {Q T S : Type} (pda : PDA Q T S) : Language T :=
  {w : List T | ∃q:Q, reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q,[],[]⟩ }

def acceptsByFinalState {Q T S : Type} (pda : PDA Q T S) : Language T :=
  {w : List T | ∃q ∈ pda.final_states,∃ γ:List S,
      reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q,[],γ⟩ }

variable {Q T S : Type} {pda : PDA Q T S}

theorem reaches_refl (r₁ : conf pda) : reaches r₁ r₁ := by
  use 0; simp [stepSetN];


theorem reaches_iff_reachesN  {r₁ : conf pda}{r₂ : conf pda}: reaches r₁ r₂ ↔ ∃n:ℕ, reachesN n r₁ r₂ := by
  simp only [reaches, reachesN]


theorem reachesN_of_n_one  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}{n : ℕ}
        (h₁:reachesN n r₁ r₂)(h₂:reachesN 1 r₂ r₃): reachesN (n+1) r₁ r₃ := by
  simp [reachesN, stepSetN, stepSet] at *
  use r₂

theorem reachesN_one {r₁ : conf pda}{r₂ : conf pda}: reachesN 1 r₁ r₂ ↔ r₂ ∈ step r₁ := by
  rw [reachesN,stepSetN,stepSet,stepSetN]
  simp

theorem reachesN_iff_split_last  {r₁ : conf pda}{r₂ : conf pda}{n : ℕ}:
        (∃c:conf pda, (reachesN n r₁ c)∧(reachesN 1 c r₂)) ↔ reachesN (n+1) r₁ r₂ := by
  constructor
  · intro h
    obtain ⟨c,h⟩ := h
    exact reachesN_of_n_one h.1 h.2
  · intro h
    simp [reachesN, stepSetN,stepSet] at h
    obtain ⟨c,h⟩ := h
    use c
    constructor
    · rw [reachesN]
      exact h.1
    · simp [reachesN,stepSet,stepSetN]
      exact h.2

theorem reachesN_of_one_n  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}{n : ℕ}
        (h₁:reachesN 1 r₁ r₂)(h₂:reachesN n r₂ r₃): reachesN (n+1) r₁ r₃ := by
  induction' n with n ih generalizing r₃
  case zero =>
    rw [reachesN,stepSetN] at h₂
    apply Set.eq_of_mem_singleton at h₂
    rw [h₂]
    simp [h₁]
  case succ =>
    rw [←reachesN_iff_split_last] at h₂
    obtain ⟨c,h₂⟩:=h₂
    have := ih h₂.1
    rw [←reachesN_iff_split_last]
    use c
    exact ⟨this,h₂.2⟩


theorem reachesN_iff_split_first  {r₁ : conf pda}{r₂ : conf pda}{n : ℕ}:
        (∃c:conf pda, (reachesN 1 r₁ c)∧(reachesN n c r₂)) ↔ reachesN (n+1) r₁ r₂ := by
  constructor
  case mp =>
    intro h
    obtain ⟨c,h⟩ := h
    apply reachesN_of_one_n h.1
    exact h.2
  case mpr =>
    intro h
    induction' n with n ih generalizing r₂
    case zero =>
      use r₂
      use h
      dsimp [reachesN,stepSetN]
      apply Set.mem_singleton
    case succ =>
      rw [←reachesN_iff_split_last] at h
      obtain ⟨c',hc'⟩:= h
      have := ih hc'.1
      obtain ⟨c,hc⟩ := this
      use c
      use hc.1
      apply reachesN_of_n_one hc.2
      exact hc'.2

theorem reachesN_trans  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}{n m : ℕ}
        (h₁:reachesN n r₁ r₂)(h₂:reachesN m r₂ r₃):∃k≤n+m, reachesN (k) r₁ r₃ := by
  induction' m with m ih generalizing r₃
  · simp [reachesN,stepSetN] at h₂
    rw [←h₂] at h₁
    use n
    refine ⟨?_, h₁⟩
    linarith
  · rw [reachesN,stepSetN,stepSet] at h₂
    simp at h₂
    obtain ⟨c,h⟩ :=  h₂
    have r₂_reaches_c: reachesN m r₂ c := by
      simp [reachesN, stepSetN, stepSet] at *
      exact h.1
    apply ih at r₂_reaches_c
    have c_reaches_r₃ : reachesN 1 c r₃ := by
      simp [reachesN, stepSetN, stepSet] at *
      exact h.2
    obtain ⟨k,h⟩ := r₂_reaches_c
    use k+1
    constructor
    linarith
    exact reachesN_of_n_one h.2 c_reaches_r₃

theorem reaches_trans  {r₁ : conf pda}{r₂ : conf pda}{r₃ : conf pda}
        (h₁:reaches r₁ r₂)(h₂:reaches r₂ r₃): reaches r₁ r₃ := by
  rw [reaches] at *
  obtain ⟨n,h⟩ := h₁
  obtain ⟨m,h'⟩ := h₂
  rw [←reachesN] at *
  rcases reachesN_trans h h' with ⟨k,h⟩
  use k
  exact h.2

theorem decreasing_input_one {r₁ : conf pda}{r₂ : conf pda}(h:reachesN 1 r₁ r₂) :
        ∃w : List T, r₁.input = w ++ r₂.input := by
  apply reachesN_one.mp at h
  rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩
  · simp [PDA,conf,step] at *
    rw [h]
  · simp [PDA,conf,step] at *
    obtain ⟨_,_,h⟩ := h
    rw [h.2]
  · simp [PDA,conf,step] at *
    rw [h]
    simp [PDA]
  · simp [PDA,conf,step] at *
    rcases h with h|h
    · obtain ⟨p,β,h⟩ := h
      rw [h.2]
      simp
      use [a]
      simp
    · obtain ⟨p,β,h⟩ := h
      rw [h.2]
      simp

theorem decreasing_input {r₁ : conf pda}{r₂ : conf pda}(h:reaches r₁ r₂) :
        ∃w : List T, r₁.input = w ++ r₂.input := by
  rw [reaches] at h
  obtain ⟨n,h'⟩ := h
  rw [←reachesN] at h'
  induction' n with n ih generalizing r₂
  · simp [reachesN, stepSetN, stepSet, step] at h'
    use []
    rw [h']
    simp
  · apply reachesN_iff_split_last.mpr at h'
    obtain ⟨c,h',h''⟩ := h'
    apply ih at h'
    apply decreasing_input_one at h''
    obtain ⟨w₁,hw₁⟩ :=  h'
    obtain ⟨w₂,hw₂⟩ :=  h''
    use w₁++w₂
    simp [hw₁,hw₂]


private theorem append_cancel (v x w: List T)
      : v ++ x =  w ++ x ↔ v = w := by
  constructor
  · intro h
    rw [List.append_eq_append_iff] at h
    rcases h with h|h
    · obtain ⟨a',h'⟩ := h
      have := List.append_left_eq_self.mp h'.2.symm
      rw [this] at h'
      simp at h'
      exact h'.symm
    · obtain ⟨a',h'⟩ := h
      have := List.append_left_eq_self.mp h'.2.symm
      rw [this] at h'
      simp at h'
      exact h'
  · intro h; rw [h]

theorem unconsumed_input_one {r₁ : conf pda}{r₂ : conf pda}:
      ∀x:List T, reachesN 1 r₁ r₂ ↔ reachesN 1 (r₁.appendInput x) (r₂.appendInput x) := by
  intro x
  constructor
  case mp =>
    intro h
    rcases r₂ with ⟨p,v,α⟩
    rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;>
    simp [reachesN,conf.appendInput,stepSetN,stepSet,step] at *
    · assumption
    · rcases x with _|⟨a,w⟩
      · simp
        assumption
      · simp
        right
        assumption
    · simp [h]
    · rw [←List.cons_append]
      rw [append_cancel]
      exact h
  case mpr =>
    intro h
    rcases r₂ with ⟨p,v,α⟩
    rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;>
    simp [reachesN,conf.appendInput,stepSetN,stepSet,step] at *
    · assumption
    · rcases x with _|⟨a,w⟩
      · simp at h; assumption
      · simp at h
        rcases h with h|h
        · obtain ⟨p,β,h⟩ := h
          have := h.2.2.1
          have : (v ++ a :: w).length = w.length := by rw[this]
          rw  [List.length_append,List.length_cons] at this
          linarith
        · assumption
    · rw [←List.cons_append,append_cancel] at h
      assumption
    · rw [←List.cons_append,append_cancel] at h
      assumption

theorem unconsumed_input_N {n:ℕ} {r₁ : conf pda}{r₂ : conf pda}:
      ∀x:List T, reachesN n r₁ r₂ ↔ reachesN n (r₁.appendInput x) (r₂.appendInput x) := by
  intro x
  constructor
  case mp =>
    induction' n with n ih generalizing r₁ r₂
    case zero =>
      intro h
      simp [reachesN,stepSetN] at h
      rw [h]
      simp [reachesN, stepSetN]
    case succ =>
      intro h
      apply reachesN_iff_split_last.mpr at h
      obtain ⟨c,h'⟩ := h
      have : reachesN n (r₁.appendInput x) (c.appendInput x) := ih h'.1
      apply And.right at h'
      rw [unconsumed_input_one x] at h'
      rw [←reachesN_iff_split_last]
      use c.appendInput x
  case mpr =>
    induction' n with n ih generalizing r₁ r₂
    · simp [reachesN, stepSetN]
      intro h
      rcases r₁ with ⟨p₁,x₁,α₁⟩
      rcases r₂ with ⟨p₂,x₂,α₂⟩
      simp [conf.appendInput] at *
      assumption
    · intro h
      rw [←reachesN_iff_split_last] at *
      obtain ⟨c,h⟩ := h
      have := decreasing_input_one h.2
      obtain ⟨w,h'⟩ := this
      set c' : conf pda := ⟨c.state,w++r₂.input,c.stack⟩ with def_c'
      have : c'.appendInput x = c := by
        rcases c with ⟨q,l,β⟩
        simp [def_c',h',conf.appendInput,conf] at *
        exact h'.symm
      rw [←this] at h
      use c'
      constructor
      · apply ih
        exact h.1
      · apply (unconsumed_input_one x).mpr
        exact h.2

theorem unconsumed_input {r₁ : conf pda}{r₂ : conf pda}:
      ∀x:List T, reaches r₁ r₂ ↔ reaches (r₁.appendInput x) (r₂.appendInput x) := by
  intro x
  constructor
  · intro h
    rw [reaches] at *
    obtain ⟨n,h'⟩ := h
    use n
    rw [←reachesN] at *
    apply (unconsumed_input_N x).mp
    assumption
  · intro h
    rw [reaches] at *
    obtain ⟨n,h'⟩ := h
    use n
    rw [←reachesN] at *
    apply (unconsumed_input_N x).mpr
    assumption

theorem reachesN_one_iff {r₁ : conf pda}{r₂ : conf pda}: reachesN 1 r₁ r₂ ↔
     ∃c : ℕ → conf pda, reachesN 1 r₁ (c 0) ∧
      (∀i<0,  reachesN 1 (c i) (c (i+1))) ∧ c 0 = r₂ := by
  constructor
  case mp =>
    intro h
    use λ_↦r₂
    simpa
  case mpr =>
    intro h
    obtain ⟨c,h'⟩:= h
    convert h'.1
    tauto

theorem reachesN_iff {r₁ : conf pda}{r₂ : conf pda} {n:ℕ}(hn:0<n): reachesN n r₁ r₂ ↔
     ∃c : ℕ → conf pda, reachesN 1 r₁ (c 0) ∧
      (∀i<n-1 ,  reachesN 1 (c i) (c (i+1))) ∧ c (n-1) = r₂ := by
  constructor
  case mp =>
    rcases n with _|⟨n⟩
    case zero => contradiction
    case succ =>
      induction' n with n ih generalizing r₂
      case zero =>
        intro h
        rw [reachesN_one_iff] at h
        simp
        tauto
      case succ =>
        simp
        intro h
        rw [←reachesN_iff_split_last] at h
        obtain ⟨cₙ,h₁,h₂⟩ := h
        apply ih (Nat.zero_lt_succ n) at h₁
        obtain ⟨c₀,h₀⟩ := h₁
        simp at h₀
        set c := λm↦if m < n+1 then c₀ m else r₂
        use c
        refine ⟨?_,?_,?_⟩
        · simp [c,hn, h₀]
        · intro i hi
          by_cases hin : i=n
          <;> simp [c, hin,hi]
          · simp [h₀,h₂]
          · apply Nat.le_of_lt_succ at hi
            have := lt_iff_le_and_ne.mpr (And.intro hi hin)
            simp [this]
            exact h₀.2.1 i this
        · simp [c]
  case mpr  =>
    rcases n with _|⟨n⟩
    case zero => contradiction
    case succ =>
      induction' n with n ih generalizing r₂
      case zero =>
        rw [reachesN_one_iff]
        tauto
      case succ =>
        intro h
        simp at h
        obtain ⟨c,h'⟩ := h
        have : reachesN (n+1) r₁ (c n) := by
          apply ih
          linarith
          use c
          refine ⟨?_,?_,?_⟩
          · tauto
          · intro i hi
            have : i<n+1:=by simp at hi; linarith
            apply h'.2.1 i this
          · simp
        have cₙr₂ : reachesN 1 (c n) r₂ := by
          rw [←h'.2.2]
          apply h'.2.1
          norm_num
        apply reachesN_of_n_one
        exact this
        exact cₙr₂

theorem reachesN_pos_of_not_self  {r₁ : conf pda}{r₂ : conf pda}{n:ℕ}(h:r₁≠r₂) :
      reachesN n r₁ r₂ → n>0 := by
  contrapose h
  simp at h
  simp [h,reachesN,stepSetN] at h
  simp [h.symm]

theorem reaches_iff {r₁ : conf pda}{r₂ : conf pda}(h:r₁≠r₂): reaches r₁ r₂ ↔
    ∃(n:ℕ)(c : ℕ → conf pda), reachesN 1 r₁ (c 0) ∧
    (∀i<n ,  reachesN 1 (c i) (c (i+1))) ∧ c n = r₂ := by
  constructor
  case mp =>
    intro h
    rw [reaches] at h
    obtain ⟨n,h'⟩ := h
    rw [←reachesN] at h'
    have n_pos:n>0 := reachesN_pos_of_not_self h h'
    rw [reachesN_iff n_pos] at h'
    obtain ⟨c,h''⟩ := h'
    use (n-1), c
  case mpr =>
    intro h
    obtain ⟨n,h'⟩ :=  h
    set m:=n+1 with m_def
    have m_pos : m>0 := by linarith
    have : n=m-1 := by simp [m_def]
    rw [this] at h'
    rw [←reachesN_iff m_pos] at h'
    rw [reaches]
    use m
    rwa[←reachesN]

theorem unconsumed_stack_one {r₁ : conf pda}{r₂ : conf pda}(hr₁s : r₁.stack ≠ List.nil):
      ∀γ:List S, reachesN 1 r₁ r₂ ↔ reachesN 1 (r₁.appendStack γ) (r₂.appendStack γ) := by
  intro γ
  constructor
  case mp =>
    intro h
    rw [reachesN_one] at *
    rcases r₁ with ⟨q,x,α⟩
    rcases r₂ with ⟨p,y,β⟩
    simp [conf.appendStack] at *
    rcases x with _|⟨a,w⟩ <;>
    rcases α with _|⟨Z,ν⟩ <;>
    rcases γ with _|⟨X,μ⟩ <;>
    simp [step] at *
    <;> try assumption
    · obtain ⟨p₁,beta₁,h'⟩ := h
      use p₁, beta₁
      simp [h']
    · rcases h with h|h
      · left
        obtain ⟨p₁,beta₁,h'⟩ := h
        use p₁, beta₁
        simp [h']
      · right
        obtain ⟨p₁,beta₁,h'⟩ := h
        use p₁, beta₁
        simp [h']
  case mpr =>
    intro h
    rw [reachesN_one] at *
    rcases r₁ with ⟨q,x,α⟩
    rcases r₂ with ⟨p,y,β⟩
    simp [conf.appendStack] at *
    rcases x with _|⟨a,w⟩ <;>
    rcases α with _|⟨Z,ν⟩ <;>
    rcases γ with _|⟨X,μ⟩ <;>
    simp [step] at *
    <;> try assumption
    · rw [List.append_cons,List.append_cons  ν X μ] at h
      obtain ⟨p₁,β₁,h'⟩ := h
      use p₁, β₁
      simp [h' ]
      have : β ++ ([X] ++ μ) = (β₁ ++ ν) ++ ([X] ++ μ) := by
        have := h'.2.2.2
        rw [←List.append_assoc,this]
        simp
      rwa [append_cancel] at this
    · rcases h with h|h
      left
      obtain ⟨p₁,β₁,h'⟩ := h
      use p₁, β₁
      use h'.1, h'.2.1, h'.2.2.1
      have : β ++ ([X] ++ μ) = (β₁ ++ ν) ++ ([X] ++ μ) := by
        repeat rw [List.append_cons _ X μ] at h'
        have := h'.2.2.2
        rw [←List.append_assoc,this]
        simp
      rwa [append_cancel] at this
      right
      obtain ⟨p₁,β₁,h'⟩ := h
      use p₁, β₁
      use h'.1, h'.2.1, h'.2.2.1
      have : β ++ ([X] ++ μ) = (β₁ ++ ν) ++ ([X] ++ μ) := by
        repeat rw [List.append_cons _ X μ] at h'
        have := h'.2.2.2
        rw [←List.append_assoc,this]
        simp
      rwa [append_cancel] at this


theorem unconsumed_stackN {n : ℕ}{r₁ : conf pda}{r₂ : conf pda}
    (hr₁s : r₁.stack ≠ List.nil)(hr₂s : r₂.stack ≠ List.nil): ∀γ, reachesN n r₁ r₂ ↔
    ∃c : ℕ → conf pda, reachesN 1 (r₁.appendStack γ) (c 0) ∧
      (∀i<n, (c i).stackPostfix γ) ∧
      (∀i<n-1 ,  reachesN 1 (c i) (c (i+1))) ∧ c (n-1) = r₂.appendStack γ := by sorry
