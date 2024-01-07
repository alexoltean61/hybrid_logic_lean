import Std.Logic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Fin.Basic

open Classical

def TypeIff (a : Type u) (b : Type v) := Prod (a → b) (b → a)
def TypeIff.intro (a : Type u) (b : Type v) : (a → b) → (b → a) → (TypeIff a b) := by
  apply Prod.mk
def TypeIff.mp  (p : TypeIff a b) : a → b := p.1
def TypeIff.mpr (p : TypeIff a b) : b → a := p.2
theorem TypeIff.refl : TypeIff a a := by
  apply TypeIff.intro <;> (intro; assumption)
theorem TypeIff.trans {h1 : TypeIff a b} {h2 : TypeIff b c} : TypeIff a c := by
  apply TypeIff.intro
  . intro h
    exact h2.mp (h1.mp h)
  . intro h
    exact h1.mpr (h2.mpr h)
infix:300 "iff" => TypeIff

theorem choice_intro (q : α → Sort u) (p : α → Prop) (P : ∃ a, p a) : (∀ a, p a → q a) → q P.choose := by
  intro h
  exact (h P.choose P.choose_spec)

/-
theorem eq_symm : (a = b) ↔ (b = a) := by
  exact eq_comm
-/

-- Wrappers for Std proofs, so that we can use them in simp:
@[simp]
theorem double_negation : ¬¬p ↔ p := by
  exact not_not

@[simp]
theorem implication_disjunction : (p → q) ↔ (¬p ∨ q) := by
  exact imp_iff_not_or

@[simp]
theorem negated_disjunction : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  exact not_or

@[simp]
theorem negated_conjunction : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  exact not_and_or

@[simp]
theorem negated_impl : ¬(p → q) ↔ p ∧ ¬q := by
  exact not_imp

@[simp]
theorem conj_comm : p ∧ q ↔ q ∧ p := by
  exact and_comm

@[simp]
theorem apply_ite' (f : α → β) (p : Prop) [Decidable p] : f ((ite p) a b) = (ite p) (f a) (f b) := by
  exact apply_ite f p a b

theorem contraposition : (p → q) ↔ (¬q → ¬p) := by
  exact Iff.symm not_imp_not
