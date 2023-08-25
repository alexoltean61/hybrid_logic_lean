import Hybrid.Form

structure Eval where
  f  : Form → Bool
  p1 : f ⊥ = false
  p2 : ∀ φ ψ : Form, (f (φ ⟶ ψ) = true) ↔ (¬(f φ) = true ∨ (f ψ) = true)

def Tautology (φ : Form) : Prop := ∀ e : Eval, e.f φ = true

theorem e_dn {e : Eval} : e.f (∼φ) = false ↔ e.f φ = true := by
  simp only [Form.neg, ←Bool.not_eq_true, e.p1, e.p2, not_or, not_not, and_true]

theorem e_neg {e : Eval} : e.f (∼φ) = true ↔ e.f φ = false := by
  have c := @not_congr (e.f (∼φ) = false) (e.f φ = true) e_dn
  rw [Bool.not_eq_false, Bool.not_eq_true] at c
  exact c

theorem e_conj {e : Eval} : e.f (φ ⋀ ψ) = true ↔ (e.f φ = true ∧ e.f ψ = true) := by
  rw [Form.conj, ←Bool.not_eq_false, e_dn, e.p2, not_or, not_not, Bool.not_eq_true, e_dn]

theorem e_disj {e : Eval} : e.f (φ ⋁ ψ) = true ↔ (e.f φ = true ∨ e.f ψ = true) := by
  rw [Form.disj, e.p2, Bool.not_eq_true, e_dn]

theorem e_impl {e : Eval} : e.f (φ ⟶ ψ) = true ↔ (e.f φ = true → e.f ψ = true) := by
  simp only [e.p2, implication_disjunction]

syntax "eval" : tactic
macro_rules
  | `(tactic| eval) => `(tactic| intro e; simp [e.p1, e.p2, e_dn, e_neg, e_conj, e_disj, e_impl, -Form.neg, -Form.conj, -Form.disj, -Form.iff])

theorem hs : Tautology ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) := by
    admit

theorem ax_1 : Tautology (φ ⟶ ψ ⟶ φ) := by
  intro e
  simp only [e.p2, Bool.not_eq_true, or_comm, ←or_assoc, Bool.dichotomy, true_or]

theorem neg_intro : Tautology ((φ ⟶ ψ) ⟶ (φ ⟶ ∼ψ) ⟶ ∼φ) := by
    eval
    admit

theorem dne : Tautology (∼∼φ ⟶ φ) := by
  eval

theorem dni : Tautology (φ ⟶ ∼∼φ) := by
  eval

theorem dn : Tautology (φ ⟷ ∼∼φ) := by
  intro e
  rw [Form.iff, e_conj]
  exact ⟨dni e, dne e⟩ 

theorem conj_intro : Tautology (φ ⟶ ψ ⟶ (φ ⋀ ψ)) := by
  eval
  admit

theorem conj_elim_l : Tautology ((φ ⋀ ψ) ⟶ φ) := by
  eval
  simp [←or_assoc, or_comm, Bool.dichotomy]

theorem conj_elim_r : Tautology ((φ ⋀ ψ) ⟶ ψ) := by
  eval
  simp [or_assoc, Bool.dichotomy]

theorem disj_intro_l : Tautology (φ ⟶ (φ ⋁ ψ)) := by
  eval
  admit

theorem disj_intro_r : Tautology (φ ⟶ (ψ ⋁ φ)) := by
  eval
  admit

theorem disj_elim : Tautology ((φ ⋁ ψ) ⟶ (φ ⟶ χ) ⟶ (ψ ⟶ χ) ⟶ χ) := by
  eval
  admit

theorem idem : Tautology ((χ ⟶ ψ ⟶ ψ ⟶ φ) ⟶ (χ ⟶ ψ ⟶ φ)) := by
  eval

theorem exp : Tautology (((φ ⋀ ψ) ⟶ χ) ⟶ (φ ⟶ ψ ⟶ χ)) := by
  intro e
  simp only [e.p2, negated_disjunction, not_not, e_conj, Bool.not_eq_true]
  let a := (e.f φ = true ∧ e.f ψ = true) ∧ e.f χ = false
  have notate₁ : a ↔ (e.f φ = true ∧ e.f ψ = true) ∧ e.f χ = false := by simp
  have notate₂ : ¬a ↔ e.f φ = false ∨ e.f ψ = false ∨ e.f χ = true := by simp [or_assoc]
  rw [←notate₁, ←notate₂]
  apply em

theorem imp : Tautology ((φ ⟶ ψ ⟶ χ) ⟶ ((φ ⋀ ψ)) ⟶ χ) := by
  intro e
  simp [e.p1, e.p2, not_or, not_not, Bool.not_eq_true, e_conj]
  let a := (e.f φ = true ∧ e.f ψ = true ∧ e.f χ = false)
  have notate₁ : a ↔ (e.f φ = true ∧ e.f ψ = true ∧ e.f χ = false) := by simp
  have notate₂ : ¬a ↔ ((e.f φ = false ∨ e.f ψ = false) ∨ e.f χ = true) := by simp [or_assoc]
  rw [←notate₁, ←notate₂]
  apply em

theorem impexp : Tautology (((φ ⋀ ψ) ⟶ χ) ⟷ (φ ⟶ ψ ⟶ χ)) := by
  intro e
  rw [Form.iff, e_conj]
  exact ⟨exp e, imp e⟩

theorem com12 : Tautology ((φ ⟶ (ψ ⟶ χ)) ⟶ (ψ ⟶ (φ ⟶ χ))) := by
  intro e
  simp only [e_impl]
  intro h1 h2 h3
  exact h1 h3 h2

syntax "tautology" : tactic
macro_rules
  | `(tactic| tautology) => `(tactic| first | apply dne)

def Eval.nom_variant (e e' : Eval) (i : NOM) (x : SVAR) : Prop :=
  e'.f = (λ φ : Form => if φ = i then (e.f x) else (e.f φ))