import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Data.List.Join
import Mathlib.Util.Delaborators
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.EpsilonNFA

structure PDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  initial_state : Q
  start_symbol : S
  final_states : Set Q
  transition_fun : Q → T → S → Set (Q × List S)
  transition_fun' : Q → S → Set (Q × List S)

namespace PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

@[ext]
structure conf (p : PDA Q T S) where
  state : Q
  input : List T
  stack : List S

variable {pda : PDA Q T S}

namespace conf

abbrev appendInput (r : conf pda) (x : List T) : conf pda :=
  ⟨r.state, r.input++x, r.stack⟩

abbrev appendStack (r : conf pda) (β : List S) : conf pda :=
  ⟨r.state, r.input, r.stack++β⟩

abbrev stackPostfix (r : conf pda) (β : List S) : Prop :=
  ∃ α : List S, r.stack = α++β

abbrev stackPostfixNontriv (r : conf pda) (β : List S): Prop :=
  ∃ α : List S, α.length > 0 ∧ r.stack = α++β

end conf

def step (r₁ : conf pda) : Set (conf pda) :=
  match r₁ with
    | ⟨q, a::w, Z::α⟩ =>
        { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun q a Z ∧
                          r₂ = ⟨p, w, (β ++ α)⟩ } ∪
        { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun' q Z ∧
                          r₂ = ⟨p, a :: w, (β ++ α)⟩ }
    | ⟨q, [], Z::α⟩ => { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun' q Z ∧
                                          r₂ = ⟨p, [], (β ++ α)⟩ }
    | ⟨q, w, []⟩ => { r₂ : conf pda | r₂ = ⟨q, w, []⟩ } -- Empty stack

def stepSet (R : Set (conf pda)) : Set (conf pda) :=
  ⋃ r ∈ R, step r

def stepSetN (n : ℕ) (R : Set (conf pda))  : Set (conf pda) :=
  match n with
  | 0 => R
  | Nat.succ m => stepSet (stepSetN m R)

-- Martin: Could you use?
#check Relation.ReflTransGen
inductive reaches' : conf pda → conf pda → Prop :=
  | base : (r₁ : conf pda) → reaches' r₁ r₁
  | step : {r₁ r' r₂ : conf pda} → (r'∈ step r₁) → (reaches' r' r₂) → reaches' r₁ r₂

def reachesN (n : ℕ) (r₁ r₂ : conf pda) : Prop :=
  r₂ ∈ stepSetN n {r₁}

def reaches (r₁ r₂ : conf pda) : Prop :=
  ∃ n : ℕ, r₂ ∈ stepSetN n {r₁}


def acceptsByEmptyStack (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q : Q,
      reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], []⟩ }

def acceptsByFinalState (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q  ∈ pda.final_states, ∃ γ : List S,
      reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], γ⟩ }

-- Martin: This theorem already exists.
private theorem append_cancel (v x w : List T) : v ++ x = w ++ x ↔ v = w := by
  apply List.append_left_inj

@[refl]
theorem reaches_refl (r₁ : conf pda) : reaches r₁ r₁ := by
  use 0; simp [stepSetN];

variable {r₁ r₂ : conf pda}

-- Martin: I have certain doubts about the usefullness of `reachesN` for your project.
theorem reaches_iff_reachesN : reaches r₁ r₂ ↔ ∃ n : ℕ, reachesN n r₁ r₂ := by
  simp only [reaches, reachesN]

theorem reachesN_of_n_one {r₃ : conf pda} {n : ℕ} (h₁ : reachesN n r₁ r₂) (h₂ : reachesN 1 r₂ r₃) :
    reachesN (n+1) r₁ r₃ := by
  simp [reachesN, stepSetN, stepSet] at *
  use r₂

theorem reachesN_one : reachesN 1 r₁ r₂ ↔ r₂ ∈ step r₁ := by
  simp [reachesN,stepSetN,stepSet,stepSetN]

theorem reachesN_iff_split_last {n : ℕ} :
    (∃ c : conf pda, reachesN n r₁ c ∧ reachesN 1 c r₂) ↔ reachesN (n+1) r₁ r₂ := by
  constructor
  · intro ⟨c, h⟩
    exact reachesN_of_n_one h.1 h.2
  · intro h
    simp [reachesN, stepSetN,stepSet] at h
    obtain ⟨c, hc⟩ := h
    use c
    constructor
    · rw [reachesN]
      exact hc.1
    · simp [reachesN,stepSet,stepSetN]
      exact hc.2

theorem reachesN_of_one_n {r₃ : conf pda} {n : ℕ} (h₁ : reachesN 1 r₁ r₂) (h₂ : reachesN n r₂ r₃) :
    reachesN (n+1) r₁ r₃ := by
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

theorem reachesN_iff_split_first {n : ℕ}:
    (∃ c : conf pda, reachesN 1 r₁ c ∧ reachesN n c r₂) ↔ reachesN (n+1) r₁ r₂ := by
  constructor
  · intro h
    obtain ⟨c,h⟩ := h
    apply reachesN_of_one_n h.1
    exact h.2
  · intro h
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

theorem reachesN_trans {r₃ : conf pda} {n m : ℕ} (h₁ : reachesN n r₁ r₂) (h₂ : reachesN m r₂ r₃) :
    ∃ k ≤ n+m, reachesN k r₁ r₃ := by
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

theorem reaches_trans {r₃ : conf pda} (h₁ : reaches r₁ r₂) (h₂ : reaches r₂ r₃) :
    reaches r₁ r₃ := by
  rw [reaches] at *
  obtain ⟨n,hn⟩ := h₁
  obtain ⟨m,hm⟩ := h₂
  rw [←reachesN] at *
  obtain ⟨k,hk⟩ := reachesN_trans hn hm
  use k
  exact hk.2

theorem decreasing_input_one (h : reachesN 1 r₁ r₂) :
    ∃ w : List T, r₁.input = w ++ r₂.input := by
  apply reachesN_one.mp at h
  rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;> simp [PDA,conf,step] at *
  · rw [h]
  · obtain ⟨_,_,h⟩ := h
    rw [h.2]
  · rw [h]
    simp [PDA]
  · rcases h with h|h
    · obtain ⟨p,β,h⟩ := h
      rw [h.2]
      simp
      use [a]
      simp
    · obtain ⟨p,β,h⟩ := h
      rw [h.2]
      simp

theorem decreasing_input (h : reaches r₁ r₂) :
    ∃ w : List T, r₁.input = w ++ r₂.input := by
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

theorem unconsumed_input_one (x : List T) :
    reachesN 1 r₁ r₂ ↔ reachesN 1 (r₁.appendInput x) (r₂.appendInput x) := by
  constructor
  · intro h
    rcases r₂ with ⟨p,v,α⟩
    rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;>
    simp [reachesN,conf.appendInput,stepSetN,stepSet,step] at *
    · assumption
    · rcases x with _|⟨a,w⟩
      · simp
        exact h
      · simp
        right
        exact h
    · simp [h]
    · rw [←List.cons_append]
      rw [append_cancel]
      exact h
  · intro h
    rcases r₂ with ⟨p,v,α⟩
    rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;>
    simp [reachesN,conf.appendInput,stepSetN,stepSet,step] at *
    · assumption
    · rcases x with _|⟨a,w⟩
      · simp at h; assumption
      · simp at h
        rcases h with h|h
        · obtain ⟨p,β,h⟩ := h
          have : (v ++ a :: w).length = w.length := by rw [h.2.2.1]
          rw [List.length_append,List.length_cons] at this
          linarith
        · assumption
    · rwa [←List.cons_append, append_cancel] at h
    · rwa [←List.cons_append, append_cancel] at h

theorem unconsumed_input_N {n : ℕ} (x : List T) :
    reachesN n r₁ r₂ ↔ reachesN n (r₁.appendInput x) (r₂.appendInput x) := by
  constructor
  · induction' n with n ih generalizing r₁ r₂
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
  · induction' n with n ih generalizing r₁ r₂
    · simp [reachesN, stepSetN]
      intros
      ext <;> aesop
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

theorem unconsumed_input (x : List T) :
    reaches r₁ r₂ ↔ reaches (r₁.appendInput x) (r₂.appendInput x) := by
  constructor <;> intro ⟨n,h'⟩ <;> use n
  · exact (unconsumed_input_N x).mp h'
  · exact (unconsumed_input_N x).mpr h'

theorem reachesN_one_iff : reachesN 1 r₁ r₂ ↔
     ∃ c : ℕ → conf pda, reachesN 1 r₁ (c 0) ∧
      (∀ i < 0, reachesN 1 (c i) (c i.succ)) ∧ c 0 = r₂ := by
  constructor
  · intro h
    use λ_↦r₂
    simpa
  · intro h
    obtain ⟨c, hr, -, hc⟩:= h
    convert hr
    exact hc.symm

theorem reachesN_iff {n : ℕ} (hn : 0 < n) : reachesN n r₁ r₂ ↔
    ∃ c : ℕ → conf pda, reachesN 1 r₁ (c 0) ∧
      (∀ i < n - 1, reachesN 1 (c i) (c i.succ)) ∧ c (n-1) = r₂ := by
  constructor
  · rcases n with _|⟨n⟩
    case zero => contradiction
    case succ =>
      induction' n with n ih generalizing r₂
      case zero =>
        intro h
        rw [reachesN_one_iff] at h
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
        refine ⟨c, ?_,?_,?_⟩
        · simp [c, hn, h₀]
        · intro i hi
          by_cases hin : i=n <;> simp [c, hin,hi]
          · simp [h₀,h₂]
          · apply Nat.le_of_lt_succ at hi
            have := lt_iff_le_and_ne.mpr (And.intro hi hin)
            simp [this]
            exact h₀.2.1 i this
        · simp [c]
  · rcases n with _|⟨n⟩
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
          · linarith
          refine ⟨c, ?_,?_,?_⟩
          · tauto
          · intro i hi
            have : i<n+1 := by simp at hi; linarith
            apply h'.2.1 i this
          · simp
        have cₙr₂ : reachesN 1 (c n) r₂ := by
          rw [←h'.2.2]
          apply h'.2.1
          norm_num
        apply reachesN_of_n_one
        exact this
        exact cₙr₂

theorem reachesN_zero : reachesN 0 r₁ r₂ ↔ r₁ = r₂ := by
  constructor
  · rw [reachesN,stepSetN,Set.mem_singleton_iff]
    exact Eq.symm
  · intro h
    simp [h, reachesN, stepSetN]

theorem reachesN_pos_of_not_self {n : ℕ} (h : r₁ ≠ r₂) :
    reachesN n r₁ r₂ → n > 0 := by
  rcases n with _ | ⟨n⟩
  · intro h
    apply reachesN_zero.mp at h
    contradiction
  · intro _
    apply Nat.zero_lt_succ

theorem reaches_iff (h : r₁ ≠ r₂) : reaches r₁ r₂ ↔
    ∃ (n : ℕ) (c : ℕ → conf pda), reachesN 1 r₁ (c 0) ∧
      (∀ i < n, reachesN 1 (c i) (c i.succ)) ∧ c n = r₂ := by
  constructor
  · intro h
    rw [reaches] at h
    obtain ⟨n,h'⟩ := h
    rw [←reachesN] at h'
    have n_pos : n>0 := reachesN_pos_of_not_self h h'
    rw [reachesN_iff n_pos] at h'
    obtain ⟨c,h''⟩ := h'
    use n-1, c
  · intro ⟨n,hn⟩
    set m := n+1 with m_def
    have m_pos : m>0 := by linarith
    rw [show n = m-1 by simp [m_def]] at hn
    rw [←reachesN_iff m_pos] at hn
    rw [reaches]
    use m
    rwa [←reachesN]

theorem unconsumed_stack_one (hr₁s : r₁.stack ≠ []) (γ : List S) :
    reachesN 1 r₁ r₂ ↔ reachesN 1 (r₁.appendStack γ) (r₂.appendStack γ) := by
  rcases r₁ with ⟨q,x,α⟩
  rcases r₂ with ⟨p,y,β⟩
  constructor
  <;> intro h
  <;> rw [reachesN_one] at *
  <;> simp [conf.appendStack] at *
  <;> rcases x with _|⟨a,w⟩
  <;> rcases α with _|⟨Z,ν⟩
  <;> rcases γ with _|⟨X,μ⟩
  <;> simp [step] at *
  <;> try assumption
  · obtain ⟨p₁, beta₁, h'⟩ := h
    use p₁, beta₁
    simp [h']
  · rcases h with h|h
    · left
      obtain ⟨p₁, beta₁, h'⟩ := h
      use p₁, beta₁
      simp [h']
    · right
      obtain ⟨p₁, beta₁, h'⟩ := h
      use p₁, beta₁
      simp [h']
  · rw [List.append_cons, List.append_cons ν X μ] at h
    obtain ⟨p₁, β₁, h'⟩ := h
    use p₁, β₁
    simp [h' ]
    have : β ++ ([X] ++ μ) = (β₁ ++ ν) ++ ([X] ++ μ) := by
      have := h'.2.2.2
      rw [←List.append_assoc,this]
      simp
    rwa [append_cancel] at this
  · rcases h with ⟨p₁,β₁,h'⟩|⟨p₁,β₁,h'⟩
    · left
      use p₁, β₁
      use h'.1, h'.2.1, h'.2.2.1
      have : β ++ ([X] ++ μ) = (β₁ ++ ν) ++ ([X] ++ μ) := by
        rw [List.append_cons _ X μ] at h'
        rw [←List.append_assoc, h'.2.2.2]
        simp
      rwa [append_cancel] at this
    · right
      use p₁, β₁
      use h'.1, h'.2.1, h'.2.2.1
      have : β ++ ([X] ++ μ) = (β₁ ++ ν) ++ ([X] ++ μ) := by
        repeat rw [List.append_cons _ X μ] at h'
        rw [←List.append_assoc, h'.2.2.2]
        simp
      rwa [append_cancel] at this

theorem unconsumed_stackN {n : ℕ} (hr₁s : r₁.stack ≠ []) (hr₂s : r₂.stack ≠ [])
    (γ : List S) :
  reachesN n r₁ r₂ ↔
    ∃ c : ℕ → conf pda, reachesN 1 (r₁.appendStack γ) (c 0) ∧
      (∀ i < n, (c i).stackPostfix γ) ∧
      (∀ i < n - 1, reachesN 1 (c i) (c i.succ)) ∧ c (n-1) = r₂.appendStack γ := by sorry

theorem reachesN_one_on_empty_stack {q p: Q}{w w': List T}{α : List S}:
    pda.reachesN 1 ⟨q, w, []⟩ ⟨p, w', α⟩ → w=w' ∧ α = [] ∧ q=p:= by
  intro h
  rw [reachesN_one] at h
  simp only [step] at h
  rw [Set.mem_setOf, conf.mk.injEq] at h
  simp [h]

theorem reaches_on_empty_stack {q p: Q}{w w': List T}{α : List S}:
    pda.reaches ⟨q, w, []⟩ ⟨p, w', α⟩ → w=w' ∧ α = [] := by
  intro h
  rw [reaches_iff_reachesN] at h
  obtain ⟨n,hr⟩ := h
  induction' n with n ih
  · rw [reachesN_zero,conf.mk.injEq] at hr
    simp [hr]
  · rw [←reachesN_iff_split_first] at hr
    obtain ⟨⟨q',v,α'⟩,h₁,h₂⟩ := hr
    apply reachesN_one_on_empty_stack at h₁
    rw  [←h₁.1, h₁.2.1, ←h₁.2.2] at h₂
    apply ih at h₂
    simp [h₂]

theorem reaches_of_reachesN  {n: ℕ}(h: pda.reachesN n r₁ r₂) : pda.reaches r₁ r₂ := by
  rw [reaches_iff_reachesN]
  use n
