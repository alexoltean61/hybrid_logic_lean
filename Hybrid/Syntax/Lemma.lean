import Hybrid.Syntax.Basic
namespace Hybrid

/-
lemma SVAR.le_refl {x : SVAR} : x ≤ x := by simp

lemma max_l {x y : SVAR} : x ≤ max x y := by simp; split <;> simp at *; assumption
lemma max_r {x y : SVAR} : y ≤ max x y := by simp; split <;> {
    try simp;
    try apply Nat.le_of_lt;
    try assumption
}

lemma max_le {x y z w : SVAR} : x ≤ y → z ≤ w → max x z ≤ max y w := by
  intros h1 h2
  simp at h1 h2 ⊢
  split <;> split
  . assumption
  . apply Nat.le_of_lt ; apply Nat.lt_of_le_of_lt; assumption; assumption
  . rename (¬w.letter < y.letter) => h3
    simp [SVAR.lt] at h3
    apply Nat.le_trans h1 h3
  . assumption

lemma max_ge {x y z w : SVAR} : x ≥ y → z ≥ w → max x z ≥ max y w := by
  simp only [GE.ge]
  apply max_le
-/
theorem ex_depth {x : SVAR} : Form.depth φ < Form.depth (ex x, φ) := by
  simp [Form.depth]
  rw [←Nat.add_assoc, ←Nat.add_assoc, Nat.add_comm]
  apply Nat.lt_add_of_pos_right
  simp

theorem NOM.gt_iff_ge_and_ne {a b : (NOM N)} : a > b ↔ (a ≥ b ∧ a ≠ b) := by
  simp only [NOM.mk, ne_eq, NOM_eq']
  apply Iff.intro
  . intro h
    apply And.intro
    . exact (Nat.lt_iff_le_and_ne.mp h).1
    . have := (Nat.lt_iff_le_and_ne.mp h).2
      intro habs
      simp [habs] at this
  . rw [←ne_eq]
    intro ⟨h1, h2⟩
    apply Nat.lt_iff_le_and_ne.mpr
    apply And.intro
    . exact h1
    . intro habs
      apply h2
      apply Subtype.eq
      assumption

-- We defined Form.list_noms such that it returns a decreasing, nonrepeating, list.
--  We prove these properties:
theorem list_noms_sorted_ge {φ : Form N} : φ.list_noms.Sorted GE.ge := by
  induction φ with
  | nom  i   => simp [Form.list_noms]
  | impl φ ψ ih1 ih2 =>
      exact List.Pairwise.sublist ((List.merge GE.ge φ.list_noms ψ.list_noms).dedup_sublist) (List.Sorted.merge ih1 ih2)
  | box _ ih    => exact ih
  | bind _ _ ih => exact ih
  | _        => simp [Form.list_noms]

theorem list_noms_nodup {φ : Form N} : φ.list_noms.Nodup := by
  induction φ <;> simp [Form.list_noms, List.nodup_dedup, *]

theorem list_noms_sorted_gt {φ : Form N} : φ.list_noms.Sorted GT.gt := by
  simp [List.Sorted, List.Pairwise, GT.gt, NOM.gt_iff_ge_and_ne, and_comm]
  apply List.Pairwise.and
  apply list_noms_nodup
  apply list_noms_sorted_ge

theorem list_noms_chain' {φ : Form N} : φ.list_noms.Chain' GT.gt := by
  rw [List.chain'_iff_pairwise]
  exact list_noms_sorted_gt
