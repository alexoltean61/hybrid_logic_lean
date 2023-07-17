import Hybrid.Truth
import Hybrid.ProofUtils
import Hybrid.FormCountable

section Lemmas
  theorem satisfiable_iff_nocontradiction (Γ : Set Form) : Γ.satisfiable ↔ Γ ⊭ ⊥ := by
    apply Iff.intro
    . intro h
      simp at h
      simp
      conv => rhs; intro M; rhs; intro s; rhs; intro g; intro φ; rw [disj_comm]
      exact h
    . intro h
      simp at h
      simp
      conv => rhs; intro M; rhs; intro s; rhs; intro g; intro φ; rw [disj_comm]
      exact h
  
  theorem unsatisfiable_iff_contradiction (Γ : Set Form) : ¬Γ.satisfiable ↔ Γ ⊨ ⊥ := by
    apply Iff.intro
    . intro h
      have := (contraposition (Γ ⊭ ⊥) Γ.satisfiable).mp
      have := this (satisfiable_iff_nocontradiction Γ).mpr
      exact not_not.mp (this h)
    . intro h
      have t := (contraposition (Γ ⊨ ⊥) ¬Γ.satisfiable).mpr
      conv at t => lhs; lhs; rw [not_not]
      have := t (satisfiable_iff_nocontradiction Γ).mp
      exact this h
  
  theorem notsatnot {Γ : Set Form} {φ : Form} : (Γ⊨φ) ↔ ¬(Γ ∪ {∼φ}).satisfiable := by
    apply Iff.intro
    . intro h sat_set
      match sat_set with
      | ⟨M, s, g, hmsg⟩ =>
          have : (∼φ) ∈ Γ ∪ {∼φ} := by simp
          have sat_not_φ := hmsg (∼φ) this
          have sat_Γ : (M,s,g) ⊨ Γ := by
              intro γ hγ
              have incl : Γ ⊆ (Γ ∪ {∼φ}) := by simp only [Set.union_singleton, Set.subset_insert]
              exact hmsg γ (incl hγ)
          have sat_φ := h M s g sat_Γ
          exact sat_not_φ sat_φ
    . rw [unsatisfiable_iff_contradiction]
      intro h M s g M_sat_Γ
      rw [←(@not_not ((M,s,g)⊨φ)), ←neg_sat]
      intro M_sat_notφ
      have : (M,s,g) ⊨ (Γ ∪ {∼φ}) := by
        intro γ hγ
        simp only [Set.union_singleton, Set.mem_insert_iff] at hγ
        apply Or.elim hγ
        . intro γnotφ
          rw [←γnotφ] at M_sat_notφ
          exact M_sat_notφ
        . intro γinΓ
          exact M_sat_Γ γ γinΓ
      exact h M s g this

  theorem notprove_consistentnot : (Γ ⊬ φ) ↔ (Γ ∪ {∼φ}).consistent := by
    apply Iff.intro
    . intro h
      by_cases c : (Γ ∪ {∼φ}).consistent
      . exact c
      . rw [Set.consistent, not_not, ←Proof.Deduction, ←Form.neg, Proof.dn_equiv_premise] at c
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
    by_cases c : cons_sat_statement
    . exact c
    . rw [cons_sat_statement, negated_universal] at c
      match c with
      | ⟨Δ, hw⟩ =>
        rw [negated_impl] at hw
        have consistent  := hw.left
        have not_satisfiable := hw.right
        rw [unsatisfiable_iff_contradiction] at not_satisfiable
        have by_completeness := (h Δ ⊥) not_satisfiable
        unfold Set.consistent at consistent
        contradiction
  . rw [contraposition cons_sat_statement completeness_statement]
    intro h
    unfold completeness_statement at h
    conv at h => rw [negated_universal]; rhs; intro Γ;
                 rw [negated_universal]; rhs; intro φ;
                 rw [negated_impl];
                 rw [conj_comm];
                 rw [notprove_consistentnot, notsatnot]
    
    conv => rw [cons_sat_statement, negated_universal]; rhs; intro Γ;
            rw [negated_impl] 
    match h with
    | ⟨Γ, φ, wit⟩ => exists (Γ ∪ {∼φ})

theorem Completeness : (∀ (Γ : Set Form) (φ : Form), Γ ⊨ φ → Γ ⊢ φ) := by
  rw [←completeness_statement, ModelExistence]
  unfold cons_sat_statement
  admit