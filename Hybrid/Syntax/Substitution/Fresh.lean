import Hybrid.Syntax.Substitution.Basic
import Hybrid.Syntax.Lemma
namespace Hybrid

-- Taking a variable x ≥ φ.new_var is the same as taking a fresh variable for φ
-- Similarly, taking a nominal i ≥ φ.new_nom.
def Form.new_var  : Form N → SVAR
| .svar x   => x+1
| .impl ψ χ => max (ψ.new_var) (χ.new_var)
| .box  ψ   => ψ.new_var
| .bind x ψ => max (x+1) (ψ.new_var)
| _         => ⟨0⟩

def Form.new_nom  : Form TotalSet → NOM TotalSet
| .nom  i   => i+1
| .impl ψ χ => max (ψ.new_nom) (χ.new_nom)
| .box  ψ   => ψ.new_nom
| .bind _ ψ => ψ.new_nom
| _         => ⟨0, trivial⟩

@[simp] def SVAR.fresh : SVAR → Form N → Prop := λ x φ => x ≥ φ.new_var
@[simp] def NOM.fresh  : NOM TotalSet → Form TotalSet → Prop := λ i φ => i ≥ φ.new_nom

section Variables
  lemma new_var_min {φ : Form N} : 0 ≤ φ.new_var := by
    apply Nat.zero_le

  lemma new_var_neg : (∼ψ).new_var = ψ.new_var := by
    simp only [Form.new_var, max_eq_left_iff]
    apply new_var_min

  lemma subst_neg : is_substable (∼ψ) y x ↔ is_substable ψ y x := by
    simp [is_substable]

  lemma new_var_gt {x : SVAR}     : occurs x φ → x < φ.new_var   := by
    induction φ with
    | svar y          =>
        simp [occurs, Form.new_var, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self y.letter
    | impl ψ χ ih1 ih2 =>
        intro hocc
        simp [occurs, Form.new_var] at hocc ⊢
        apply Or.elim hocc
        . intro hocc; apply Or.inl; apply ih1
          assumption
        . intro hocc; apply Or.inr; apply ih2
          assumption
    | box ψ ih      =>
        simp only [occurs, Form.new_var]
        assumption
    | bind y ψ ih   =>
        intro hocc
        simp [occurs, Form.new_var] at hocc ⊢
        apply Or.inr; apply ih
        assumption
    | _ => simp [occurs]

  lemma new_var_is_new  : occurs (φ.new_var) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_var_gt h
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a

  lemma ge_new_var_is_new {x : SVAR} (h : x ≥ φ.new_var) : occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_var_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a

  lemma ge_new_var_subst_nom {φ : Form N} {i : NOM N} {y : SVAR} : φ.new_var ≥ φ[i // y].new_var := by
    induction φ with
    | svar x =>
        simp [Form.new_var, subst, LE.le, ite_true]
        split
        . apply Nat.zero_le
        . trivial
    | impl φ ψ ih1 ih2 =>
        simp only [Form.new_var]
        apply max_le_max
        repeat assumption
    | box φ ih =>
        simp only [Form.new_var]
        repeat assumption
    | bind x φ ih =>
        simp only [Form.new_var, subst]
        by_cases h : y = x
        . simp only [h, ite_true, Form.new_var]
          apply le_refl
        . simp only [h, ite_false, Form.new_var]
          apply max_le_max
          apply le_refl
          assumption
    | _         => simp [Form.new_var, subst]

  lemma fresh_bound {x : SVAR} : y.fresh (all x, φ) → x ≠ y := by
    simp [Form.new_var, -implication_disjunction]
    intro _ h2 habs
    rw [habs] at h2
    simp [LE.le] at h2
    rw [Iff.symm Nat.not_lt] at h2
    apply h2
    apply Nat.lt.base

  lemma new_var_geq1 : x ≥ (φ ⟶ ψ).new_var → (x ≥ φ.new_var ∧ x ≥ ψ.new_var) := by
    intro h
    simp [Form.new_var] at *
    assumption

  lemma new_var_geq2 : x ≥ (all y, ψ).new_var → (x ≥ (y+1) ∧ x ≥ ψ.new_var) := by
    intro h
    simp [Form.new_var] at *
    assumption

  lemma new_var_geq3 : x ≥ (□ φ).new_var → (x ≥ φ.new_var) := by simp [Form.new_var]

lemma fresh_substable {φ : Form N} {x y : SVAR} (h : x.fresh φ) : is_substable φ x y := by
  induction φ with
  | impl φ ψ ih1 ih2 =>
      simp [Form.new_var] at h
      simp [is_substable, h, ih1, ih2]
  | box φ ih =>
      simp [Form.new_var] at h
      simp [is_substable, h, ih]
  | bind z φ ih =>
      simp [fresh_bound h, is_substable]
      apply Or.inr ; apply ih
      simp [Form.new_var] at h
      exact h.1
  | _     => simp [is_substable]

lemma new_var_subst {φ : Form N} {i : NOM N} {x y : SVAR} (h : x.fresh φ) : is_substable (φ[y//i]) x y := by
  admit

lemma new_var_subst' {φ : Form N} (i : NOM N) {x y : SVAR} (h1 : is_substable φ v y) (h2 : x ≥ φ.new_var) (h3 : y ≠ x) : is_substable (φ[x//i]) v y := by
  admit

lemma new_var_subst'' {φ : Form N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable φ x y := by
  admit

lemma scz {φ : Form N} (i : NOM N) (h : x ≥ φ.new_var) (hy : y ≠ x) : (is_free y φ) ↔ (is_free y (φ[x // i])) := by
  admit

/-
lemma new_var_subst {φ : Form N} {i : NOM N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable (φ[y//i]) x y := by
  induction φ with
  | nom  j  =>
      simp [subst]
      split <;> simp [is_substable]
  | bind z ψ ih =>
      simp only [Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
          bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_false, Bool.and_eq_true] at h ⊢
      intro _
      by_cases hc : (z + 1) > (Form.new_var ψ)
      . simp only [hc, ite_true] at h
        simp only [gt_iff_lt, ge_iff_le] at hc ih
        have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
        have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
      . simp only [hc, ite_false] at h
        rw [gt_iff_lt] at hc
        rw [not_lt] at hc
        simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih
        have ih := ih h
        have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
  | impl ψ χ ih1 ih2 =>
      simp [Form.new_var, max, is_substable, subst] at h ⊢
      by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact ⟨ih1 h, ih2 this⟩
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact ⟨ih1 this, ih2 h⟩
  | box ψ ih         =>
      simp [Form.new_var, is_substable, subst] at h ⊢
      exact ih h
  | _  =>
      simp [is_substable]

lemma new_var_subst'' {φ : Form N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable φ x y := by
  induction φ with
  | bind z ψ ih =>
      simp only [Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
          bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_false, Bool.and_eq_true] at h ⊢
      intro _
      by_cases hc : (z + 1).letter > (Form.new_var ψ).letter
      . simp [hc] at h
        simp only [gt_iff_lt, ge_iff_le] at hc ih
        have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
        have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
      . simp [hc] at h
        simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih
        have ih := ih h
        have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
  | impl ψ χ ih1 ih2 =>
      simp [Form.new_var, max, is_substable, subst] at h ⊢
      by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact ⟨ih1 h, ih2 this⟩
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact ⟨ih1 this, ih2 h⟩
  | box ψ ih         =>
      simp [Form.new_var, is_substable, subst] at h ⊢
      exact ih h
  | _  =>
      simp [is_substable]

lemma scz {φ : Form N} (i : NOM N) (h : x ≥ φ.new_var) (hy : y ≠ x) : (is_free y φ) ↔ (is_free y (φ[x // i])) := by
  induction φ with
  | nom a       =>
      simp [subst] ; split <;> simp [is_free, hy]
  | bind z ψ ih =>
      simp [is_free, -implication_disjunction]
      simp [new_var_geq2 h] at ih
      simp [ih]
  | impl ψ χ ih1 ih2 =>
      have ⟨ih1_cond, ih2_cond⟩ := new_var_geq1 h
      simp [ih1_cond, ih2_cond] at ih1 ih2
      simp [is_free, ih1, ih2]
  | box ψ ih         =>
      simp [Form.new_var] at h
      simp [h] at ih
      simp [is_free, ih]
  | _ => simp [is_free]

lemma new_var_subst' {φ : Form N} (i : NOM N) {x y : SVAR} (h1 : is_substable φ v y) (h2 : x ≥ φ.new_var) (h3 : y ≠ x) : is_substable (φ[x//i]) v y := by
  induction φ with
  | nom  a      => simp [nom_subst_svar]; split <;> simp [is_substable]
  | bind z ψ ih =>
      have xge := (new_var_geq2 h2).right
      have := @scz N x y ψ i xge h3
      simp [←this, nom_subst_svar, is_substable, -implication_disjunction]
      clear this
      intro h
      simp [is_substable, h] at h1
      simp [h1, xge, ih]
  | impl ψ χ ih1 ih2  =>
      simp [is_substable] at h1
      simp [Form.new_var] at h2
      have ⟨ih1_cond, ih2_cond⟩ := new_var_geq1 h2
      simp [h1, h2, ih1_cond, ih2_cond] at ih1 ih2
      simp [is_substable, ih1, ih2]
  | box ψ ih          =>
      simp [is_substable] at h1
      simp [Form.new_var] at h2
      simp [h1, h2] at ih
      simp [is_substable, ih]
  | _       =>  simp [nom_subst_svar, h1]
-/

lemma nom_subst_trans {φ : Form N} (i : NOM N) (x y : SVAR) (h : y.fresh φ) : φ[y // i][x // y] = φ[x // i] := by
  induction φ with
  | bttm   => simp [subst]
  | prop   => simp [subst]
  | nom j  => by_cases c : i = j <;> simp [c, subst]
  | svar z =>
      simp [subst, -implication_disjunction]
      intro heq
      exfalso
      simp [Form.new_var, heq, LE.le] at h
      rw [Iff.symm Nat.not_lt] at h
      apply h
      apply Nat.lt.base
  | impl φ ψ ih1 ih2 =>
      have ⟨fresh_1, fresh_2⟩ := new_var_geq1 h
      simp [subst, fresh_1, fresh_2, ih1, ih2]
  | box φ ih =>
      simp [subst]
      apply ih
      exact h
  | bind x φ ih =>
      simp [subst, Ne.symm (fresh_bound h), Form.new_var] at h ⊢
      apply ih
      exact h.1

  lemma ge_new_var_subst_helpr {φ χ : Form N} {i : NOM N} {x : SVAR} (h : y ≥ (χ⟶ψ).new_var) : y ≥ Form.new_var (χ⟶ψ[i//x]⟶⊥) := by
    simp [Form.new_var, max]
    split <;> split
    . exact (new_var_geq1 h).left
    . apply Nat.le_trans
      apply ge_new_var_subst_nom
      exact (new_var_geq1 h).right
    . exact (new_var_geq1 h).left
    . simp [SVAR.le]

end Variables
