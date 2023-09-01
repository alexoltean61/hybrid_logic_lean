import Hybrid.Tautology

theorem empty_list (L : List {x : Form N | False}) : L = [] := by
  match L with
  | [] => simp
  | h :: t =>
      exfalso
      have := h.2
      simp at this

def List.max_form {Γ : Set (Form N)} : List Γ → (Form N → ℕ) → ℕ
| .nil, f      => f ⊥
| .cons h t, f => if (f h) > (t.max_form f) then (f h) else (t.max_form f)

theorem List.max_is_max {Γ : Set (Form N)} (L : List Γ) (f : Form N → ℕ) : ∀ φ, φ ∈ L → f φ ≤ L.max_form f := by
  intro φ in_list
  induction L with
  | nil => contradiction
  | cons h t ih =>
      simp at in_list
      apply Or.elim in_list
      . intro hyp
        rw [hyp, max_form]
        split
        . apply Nat.le.refl
        . simp at *
          assumption
      . intro hyp
        rw [max_form]
        have ih := ih hyp
        by_cases hc : f h > max_form t f
        . simp [hc]
          exact Nat.le_trans ih (Nat.le_of_lt hc)
        . simp [hc]
          exact ih

-- The standard implementation of these coerces the list
-- to the type of element we are filtering / searching.
-- It's overkill to coerce the whole list. We can use
-- h.val to compare an formula h : Set (Form N) to a formula
-- φ : Form.
def filter' {Γ : Set (Form N)} : List Γ → Form N → List Γ
| [],   _   => []
| h::t, φ => match h.val == φ with
  | true  => filter' t φ
  | false => h::(filter' t φ)

def elem' {Γ : Set (Form N)} : List Γ → Form N → Bool
| [], _    => false
| h::t, φ => match h.val == φ with
  | true  => true
  | false => elem' t φ

theorem filter'_filters {Γ : Set (Form N)} {φ : Form N} {L : List ↑(Γ ∪ {φ})} : ¬elem' (filter' L φ) φ := by
  induction L with
  | nil           => simp [filter', elem']
  | cons h t ih   => cases c : ↑h == φ
                     repeat simp [filter', c, elem', ih]

theorem filter'_doesnt_filter {Γ : Set (Form N)} {L : List Γ} (hyp : ¬elem' L φ) : (filter' L φ) = L := by
  induction L with
  | nil         => simp [filter']
  | cons h t ih => cases c : ↑h == φ
                   . simp [elem', c] at hyp
                     simp [filter', elem', c, ih, hyp]
                   . simp [elem', c] at hyp

-- Trivial fact, ugly implementation (but it works!):
--    Let Γ and Δ be two sets of formulas s.t. Γ ⊆ Δ. 
--    Then, any list L of formulas taken from Γ can be
--      converted to a list L' of formulas from Δ
--      s.t. L and L' have the same elements.
def list_convert_general {Γ Δ : Set (Form N)} (h_incl : Γ ⊆ Δ) (L : List Γ) : List Δ :=
  match L with
  | []      => []
  | h :: t  => ⟨h.val, (h_incl h.prop)⟩ :: list_convert_general h_incl t

--  And any conjunction of elements from Γ is a conjunction
--    of elements from Δ.
theorem conj_incl_general {Γ Δ : Set (Form N)} (h_incl : Γ ⊆ Δ) (L : List Γ) : conjunction Γ L = conjunction Δ (list_convert_general h_incl L) := by
  match L with
  | []      =>
      simp [conjunction]
  | h :: t  =>
      simp [conjunction]
      exact conj_incl_general h_incl t

--    Let Γ be a set of formulas and ψ a formula.
--    Then, any list L of formulas taken from Γ can be
--      converted to a list L' of formulas from Γ ∪ {ψ}
--      s.t. L and L' have the same elements.
def list_convert {Γ : Set (Form N)} {ψ : Form N} (L : List Γ) : List ↑(Γ ∪ {ψ}) := by
  have incl : Γ ⊆ (Γ ∪ {ψ}) := by simp
  apply list_convert_general incl L

-- Any conjunction of formulas from Γ is a conjunction
-- of formulas from Γ ∪ {ψ}.
theorem conj_incl {Γ : Set (Form N)} {ψ : Form N} (L : List Γ) : conjunction Γ L = conjunction (Γ ∪ {ψ}) (list_convert L) := by
  have incl : Γ ⊆ (Γ ∪ {ψ}) := by simp
  exact conj_incl_general incl L


-- If L is a list of elements from Γ ∪ {φ}, and φ ∉ L,
-- then we can convert L to a list L' of elements from Γ,
--   s.t. L and L' have the same elements.
--   duuuh
theorem help {α : Type u} {Γ : Set α} {φ ψ : α} (h1 : φ ∈ ↑(Γ ∪ {ψ})) (h2 : φ ≠ ψ) : φ ∈ Γ := by
  simp [h2] at h1
  exact h1

theorem help2 {Γ : Set (Form N)} {h : Γ} {a : Form N} {t : List Γ} : elem' (h::t) a = false → (elem' t a) = false := by
  intro hyp
  cases c : h.val == a
  . simp [elem', c] at hyp
    exact hyp
  . simp [elem', c] at hyp

def list_convert_rev {Γ : Set (Form N)} {ψ : Form N} (L : List ↑(Γ ∪ {ψ})) (hyp : elem' L ψ = false) : List Γ :=
  match L with
  | []     => []
  | h ::t  => dite (ψ = ↑h)
                (λ _ => list_convert_rev t (help2 hyp))
                (λ neq => by
                    simp at neq
                    have prop := help h.prop (Ne.symm neq)
                    exact ⟨h.val, prop⟩ :: (list_convert_rev t (help2 hyp))
                )

-- Any conjunction of formulas from Γ ∪ {ψ} that doesn't include ψ
-- is a conjunction of formulas from Γ.
theorem conj_incl_rev {Γ : Set (Form N)} {ψ : Form N} (L : List ↑(Γ ∪ {ψ})) (hyp : elem' L ψ = false): conjunction (Γ ∪ {ψ}) L = conjunction Γ (list_convert_rev L hyp) := by
  match L with
  | []      =>
      simp [conjunction]
  | h :: t  =>
      by_cases eq : ψ = h
      . simp [elem', eq] at hyp
      . simp [list_convert_rev, eq, conjunction]
        exact conj_incl_rev t (help2 hyp)

-- This might be the ugliest Lean code I've written.
-- What this says is that if you have two sets of formulas, Γ and Δ,
--  and some conjunction of formulas in Γ such that all formulas in that
--  conjunction belong to Δ as well;
--    then that conjunction of Γ-formulas is also a conjunction of Δ-formulas.
-- *So* trivially sounding, but such a pain to prove! Due to the typing system
--    which makes Γ and Δ behave as different (sub)types.
--
-- This is used in Lemma LindenbaumConsistent.
theorem conj_incl_linden {Γ Δ : Set (Form N)} (L : List Γ) (hyp : {↑φ | φ ∈ L} ⊆ Δ): ∃ L', conjunction Γ L = conjunction Δ L' := by
  induction L with
  | nil =>
      let L' : List Δ := []
      exists L'
  | cons h t ih =>
      rw [conjunction]
      have : {x | ∃ φ, φ ∈ t ∧ ↑φ = x} ⊆ Δ := by
        intro x x_mem
        simp only [Set.mem_setOf_eq] at x_mem
        simp only [List.mem_cons] at hyp
        let ⟨φ, a, b⟩ := x_mem 
        have : ∃ φ, (φ = h ∨ φ ∈ t) ∧ ↑φ = x := by
          exists φ
          apply And.intro
          . apply Or.inr a
          . exact b
        clear φ a b
        exact hyp this
      let ⟨L'', conj⟩ := ih this
      let h_d : Δ := ⟨↑h, by
          have h_d_mem : ∃ φ, φ ∈ (h :: t) ∧ φ.val = ↑h := by simp
          exact hyp h_d_mem
        ⟩
      have : h_d.val = h.val := by simp
      let L' := ↑h_d :: L''
      exists L'
      rw [conjunction, this, conj]

theorem conj_idempotent {e : Eval N} {Γ : Set (Form N)} {L : List Γ} (hyp : elem' L φ) : e.f (conjunction Γ L) ∧ e.f φ ↔ e.f (conjunction Γ L) := by
  induction L with
  | nil => simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == φ
      . have := Eq.symm ((beq_iff_eq h.val φ).mp eq)
        simp only [conjunction, e_conj, this, conj_comm, and_self_left]
      . simp [elem', show (h.val == φ) = false by simp [eq]] at hyp
        simp only [conjunction, e_conj, and_assoc, ih hyp]

-- Instead of proving conjunction is associative, commutative and idempotent, we do 3-in-1:
theorem conj_helper {e : Eval N} {Γ : Set (Form N)} {L : List Γ} (hyp : elem' L φ) : e.f (conjunction Γ (filter' L φ)⋀φ) = true ↔ e.f (conjunction Γ L) = true := by
  induction L with
  | nil         =>
      simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == φ
      . simp only [filter', eq, conjunction]
        have := (beq_iff_eq h.val φ).mp eq
        rw [this]
        by_cases phi_in_t : elem' t φ
        . conv => rhs; rw [e_conj, and_comm, conj_idempotent phi_in_t]
          simp only [ih, phi_in_t]
        . simp only [filter'_doesnt_filter, phi_in_t, e_conj, and_comm]
      . simp [elem', eq] at hyp
        simp only [hyp, e_conj, conj_comm, forall_true_left] at ih 
        rw [and_comm] at ih
        simp only [filter', eq, conjunction, e_conj, and_assoc, ih]

theorem deduction_helper {Γ : Set (Form N)} (L : List Γ) (φ ψ : Form N) (h : elem' L φ) :
  Tautology ((conjunction Γ L ⟶ ψ) ⟶ (conjunction Γ (filter' L φ) ⟶ φ ⟶ ψ)) := by
  intro e
  rw [e_impl, e_impl, e_impl, e_impl]
  intro h1 h2 h3
  have l1 := (@e_conj N (conjunction Γ (filter' L φ)) φ e).mpr ⟨h2, h3⟩
  rw [conj_helper h] at l1
  exact h1 l1