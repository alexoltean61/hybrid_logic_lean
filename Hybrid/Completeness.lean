import Hybrid.Truth
import Hybrid.ProofUtils
import Hybrid.FormCountable

section Lemmas
  theorem satisfiable_iff_nocontradiction (Γ : Set Form) : Γ.satisfiable ↔ Γ ⊭ ⊥ := by
    apply Iff.intro <;> {
    . intro h
      simp at h ⊢
      conv => rhs; intro M; rhs; intro s; rhs; intro g; intro φ; rw [disj_comm]
      exact h
    }
  
  theorem unsatisfiable_iff_contradiction (Γ : Set Form) : ¬Γ.satisfiable ↔ Γ ⊨ ⊥ := by
    conv => rhs; rw [←@not_not (Γ ⊨ ⊥)]
    apply Iff.not
    apply satisfiable_iff_nocontradiction
  
  theorem notsatnot {Γ : Set Form} {φ : Form} : (Γ⊨φ) ↔ ¬(Γ ∪ {∼φ}).satisfiable := by
    rw [unsatisfiable_iff_contradiction, ←SemanticDeduction, ←Form.neg, Entails, Entails]
    conv => rhs; intro M s g h; rw [neg_sat, neg_sat, not_not]

  theorem notprove_consistentnot : (Γ ⊬ φ) ↔ (Γ ∪ {∼φ}).consistent := by
    apply Iff.intro
    . intro h
      rw [←@not_not ((Γ ∪ {∼φ}).consistent)]
      intro habs
      rw [Set.consistent, not_not, ←Proof.Deduction, ←Form.neg, Proof.dn_equiv_premise] at habs
      contradiction
    . intro h
      rw [Set.consistent, ←Proof.Deduction, ←Form.neg,  Proof.dn_equiv_premise] at h
      exact h
end Lemmas


def completeness_statement := (∀ (Γ : Set Form) (φ : Form), Γ ⊨ φ → Γ ⊢ φ)
def cons_sat_statement     := (∀ (Γ : Set Form), Γ.consistent → Γ.satisfiable)

theorem ModelExistence : completeness_statement ↔ cons_sat_statement := by
  apply Iff.intro
  . intro h
    rw [←@not_not (cons_sat_statement)]
    intro habs
    rw [cons_sat_statement, negated_universal] at habs
    match habs with
    | ⟨Δ, hw⟩ =>
      rw [negated_impl] at hw
      have ⟨consistent, not_satisfiable⟩  := hw
      rw [unsatisfiable_iff_contradiction] at not_satisfiable
      have by_completeness := (h Δ ⊥) not_satisfiable
      contradiction
  . rw [contraposition cons_sat_statement completeness_statement]
    intro h
    simp only [completeness_statement, not_forall, negated_impl,
            notprove_consistentnot, notsatnot, ←conj_comm] at h
    simp only [cons_sat_statement, not_forall, negated_impl]
    have ⟨Γ, φ, wit⟩ := h
    exists (Γ ∪ {∼φ})

theorem Completeness : (∀ (Γ : Set Form) (φ : Form), Γ ⊨ φ → Γ ⊢ φ) := by
  rw [←completeness_statement, ModelExistence]
  unfold cons_sat_statement
  admit