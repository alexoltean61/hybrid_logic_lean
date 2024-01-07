import Hybrid.Syntax.Substitution.Basic
import Hybrid.Syntax.Lemma
namespace Hybrid

lemma subst_self_is_self (φ : Form N) : φ [x // x] = φ := by
  induction φ with
  | nom  i   =>
      match x with
      | .SVAR z =>
          simp [subst, -implication_disjunction]
      | .NOM  i =>
          simp [subst]
  | svar y   =>
      by_cases xy : x = y
      . simp [subst, if_pos xy, xy]
      . simp [subst, if_neg xy]
  | impl φ ψ ih1 ih2 =>
      rw [subst, ih1, ih2]
  | box  φ ih  =>
      rw [subst, ih]
  | bind y φ ih =>
      match x with
      | .SVAR z =>
          simp [subst, -implication_disjunction]
          intro; assumption
      | .NOM  i =>
          simp [subst, ih]
  | _        => rfl

lemma notfree_after_subst {φ : Form N} {x y : SVAR} (h : x ≠ y) : is_free x (φ[y // x]) = false := by
  induction φ with
  | svar z   =>
      by_cases xz : x = z
      . simp [subst, if_pos xz, is_free, h]
      . simp [subst, if_neg xz, is_free, xz]
  | impl _ _ ih1 ih2 =>
      simp [subst, is_free, ih1, ih2]
  | box _ ih    =>
      simp [subst, is_free, ih]
  | bind z _ ih =>
      by_cases xz : x = z
      . simp [subst, xz, is_free]
      . simp [subst, if_neg xz, is_free, ih]
  | _        => simp only [is_free]

lemma notocc_beforeafter_subst {φ : Form N} {x y : SVAR} (h : occurs x φ = false) : occurs x (φ[y // x]) = false := by
  induction φ with
  | svar z   =>
      by_cases xz : x = z
      <;> simp [subst, if_pos xz, xz, occurs, h] at *
  | impl _ _ ih1 ih2 =>
      simp [subst, occurs, not_or, ih1, ih2, -implication_disjunction] at *
      exact ⟨ih1 h.left, ih2 h.right⟩
  | box _ ih    =>
      simp [subst, occurs, ih, -implication_disjunction] at *
      exact ih h
  | bind z ψ ih =>
      by_cases xz : x = z
      . simp [subst, xz, occurs] at *
        exact h
      . simp [subst, if_neg xz, occurs, ih, xz, h, -implication_disjunction] at *
        exact ih h
  | _        => simp [occurs]

lemma notoccursbind : occurs x φ = false → occurs x (all v, φ) = false := by
  simp [occurs]

lemma notoccurs_notfree {x : SVAR} : (occurs x φ = false) → (is_free x φ = false) := by
  induction φ with
  | svar _ => simp [occurs, is_free]
  | impl _ _ ih1 ih2 =>
      intro h
      simp [occurs] at h
      simp [is_free, ih1, ih2, h]
  | box _ ih        =>
      intro h
      rw [occurs] at h
      simp [is_free, ih, h]
  | bind _ _ ih     =>
      intro h
      rw [occurs] at h
      simp [is_free, ih, h]
  | _ =>
      intro h
      rfl

lemma subst_notfree_var {φ : Form N} {x y : SVAR} (h : is_free x φ = false) : (φ[y // x] = φ) ∧ (occurs x φ = false → is_substable φ y x) := by
  induction φ with
  | svar z =>
      by_cases heq : x = z
      . simp only [is_free, heq, beq_self_eq_true] at h
      . simp only [subst, StateSymb.SVAR.injEq, heq, ite_false, occurs, beq_eq_false_iff_ne, ne_eq,
        not_false_eq_true, is_substable, forall_true_left, and_self]
  | impl ψ χ ih1 ih2 =>
      simp only [is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h
      apply And.intro
      . simp [subst, h, ih1, ih2]
      . intro nocc
        simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at nocc
        simp [is_substable, h, nocc, ih1, ih2]
  | box ψ ih  =>
      rw [is_free] at h
      apply And.intro
      . simp [subst, ih, h]
      . intro nocc
        rw [occurs] at nocc
        simp [is_substable, ih, nocc, h]
  | bind z ψ ih =>
      apply And.intro
      . by_cases heq : x = z
        . simp [←heq, subst, if_pos (Eq.refl x)]
        . simp only [is_free, bne, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false', beq_iff_eq,
          Ne.symm heq, false_or] at h
          simp [subst, heq, ih, h]
      . intro nocc
        rw [occurs] at nocc
        simp [is_substable, notoccurs_notfree, nocc]
  | _   =>
      simp [subst, is_substable]

lemma preserve_notfree {φ : Form N} (x v : SVAR) : (is_free x φ = false) → (is_free x (all v, φ) = false) := by
  intro h
  simp only [is_free, h, Bool.and_false]

lemma rereplacement (φ : Form N) (x y : SVAR) (h1 : occurs y φ = false) (h2 : is_substable φ y x) : (is_substable (φ[y // x]) x y) ∧ φ[y // x][x // y] = φ := by
  induction φ with
  | svar z =>
      simp [occurs] at h1
      by_cases xz : x = z
      repeat simp [subst, xz, h1, is_substable]
  | impl ψ χ ih1 ih2 =>
      simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1
      simp only [is_substable, Bool.and_eq_true] at h2
      simp [subst, ih1, ih2, h1, h2, is_substable]
  | box ψ ih =>
      simp only [occurs] at h1
      simp only [is_substable] at h2
      simp [subst, ih, h1, h2, is_substable]
  | bind z ψ ih =>
      by_cases yz : y = z
      . rw [←yz]
        rw [←yz] at h1

        simp only [is_substable, beq_iff_eq, ←yz, bne_self_eq_false, Bool.false_and, ite_eq_left_iff,
          Bool.not_eq_false, implication_disjunction, Bool.not_eq_true, or_false] at h2
        have h2 := @preserve_notfree N ψ x y h2
        simp [subst_notfree_var, h2]

        have := @subst_notfree_var N (all y, ψ) y x (notoccurs_notfree h1)
        simp [@subst_notfree_var N (all y, ψ) y x, notoccurs_notfree, h1]
      . by_cases xz : x = z
        . have : is_free x (all x, ψ) = false := by simp [is_free]
          rw [←xz] at h1
          simp [←xz, subst_notfree_var, this, notoccurs_notfree, h1]
        . simp only [occurs] at h1
          simp [subst, xz, yz]
          by_cases xfree : is_free x ψ
          . simp [is_substable, xfree, Ne.symm yz, bne] at h2
            simp [ih, h1, h2, is_substable, bne, Ne.symm xz]
          . rw [show (¬is_free x ψ = true ↔ is_free x ψ = false) by simp] at xfree
            simp [subst_notfree_var, xfree, is_substable, (notoccurs_notfree h1)]
  | _     =>
      apply And.intro
      repeat rfl

lemma pos_subst {m : ℕ} {φ : Form N} {i : NOM N} {v : SVAR} : (iterate_pos m (v⋀φ))[i//v] = iterate_pos m (i⋀φ[i//v]) := by
  induction m with
  | zero =>
      simp [iterate_pos, iterate_pos.loop, subst]
  | succ n ih =>
      simp [iterate_pos, iterate_pos.loop, subst] at ih ⊢
      rw [ih]

lemma nec_subst {m : ℕ} {φ : Form N} {i : NOM N} {v : SVAR} : (iterate_nec m (v⟶φ))[i//v] = iterate_nec m (i⟶φ[i//v]) := by
  induction m with
  | zero =>
      simp [iterate_nec, iterate_nec.loop, subst]
  | succ n ih =>
      simp [iterate_nec, iterate_nec.loop, subst] at ih ⊢
      rw [ih]

theorem iff_subst_svar {y x : SVAR} : (φ ⟷ ψ)[y // x] = (φ[y//x] ⟷ ψ[y//x]) := by
  simp [subst]

theorem subst_depth {x : SVAR} {s : StateSymb N} : φ[s // x].depth = φ.depth := by
  induction φ <;> simp [subst, Form.depth, *] at *
  . (split <;> simp [Form.depth, *])

theorem subst_depth' {x : SVAR} {φ : Form N} : (φ[s//x]).depth < (ex x, φ).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply ex_depth

lemma notfreeset {Γ : Set (Form N)} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ.1 = false) : is_free x (conjunction Γ L) = false := by
  induction L with
  | nil         =>
      simp only [conjunction, is_free]
  | cons h t ih =>
      simp only [is_free, Bool.or_false, Bool.or_eq_false_eq_eq_false_and_eq_false]
      apply And.intro
      . exact hyp h
      . exact ih
