import Hybrid.Soundness
import Hybrid.Substitutions
import Hybrid.ProofUtils

def Form.replace_bound : Form N → SVAR → Form N
  | (all z, φ), x =>
        if z = x then
          let y := (φ.replace_bound x).new_var + x.letter + 1
          all y, (φ.replace_bound x)[y//x]
        else all z, φ.replace_bound x
  | (φ ⟶ ψ), x => (φ.replace_bound x) ⟶ (ψ.replace_bound x)
  | (□φ), x     => □ (φ.replace_bound x)
  | φ, _        => φ

theorem replace_neg : (∼φ).replace_bound x = ∼(φ.replace_bound x) := by
  admit

theorem replace_bound_depth {φ : Form N} {x : SVAR} : (φ.replace_bound x).depth = φ.depth := by
  admit

theorem replace_bound_depth' {ψ : Form N} {x z : SVAR} : ((ψ.replace_bound x)[x//z]).depth < (ex x, ψ).depth := by
  rw [subst_depth', replace_bound_depth]
  apply ex_depth

theorem substable_after_replace (φ : Form N) : is_substable (φ.replace_bound y) y x := by
  induction φ with
  | bind z φ ih =>
      simp only [Form.replace_bound]
      split
      . rw [is_substable]
        split
        . simp
        . simp
          apply And.intro
          . have : (φ.replace_bound y).new_var + y.letter ≥ y := by simp [SVAR.le, SVAR.add]

            admit
          .
            admit
      . admit
  | impl φ ψ ih1 ih2 => admit
  | box φ ih => admit
  | _ =>
      simp only [Form.replace_bound, is_substable]

theorem rename_all_bound_pf (φ : Form N) (x : SVAR) : ⊢ (φ ⟷ (φ.replace_bound x)) := by
  induction φ with
  | bind z φ ih =>
      rw [Form.replace_bound]
      by_cases h : z = x
      . simp only [h, ite_true]
        let l1 := Proof.mp Proof.b363 (Proof.general x (Proof.mp (Proof.tautology iff_elim_l) ih))
        let l2 := Proof.mp Proof.b363 (Proof.general x (Proof.mp (Proof.tautology iff_elim_r) ih))
        let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
        let y := (φ.replace_bound x).new_var + x.letter + 1
        have : y ≥ (φ.replace_bound x).new_var := by simp [SVAR.le, SVAR.add, Nat.add_assoc]
        let l4 := @Proof.rename_bound N y x (φ.replace_bound x) (ge_new_var_is_new this) (new_var_subst'' this)
        let l5 := Proof.mp (Proof.mp (Proof.tautology iff_rw) l3) l4
        exact l5
      . simp only [h, ite_false]
        let l1 := Proof.mp Proof.b363 (Proof.general z (Proof.mp (Proof.tautology iff_elim_l) ih))
        let l2 := Proof.mp Proof.b363 (Proof.general z (Proof.mp (Proof.tautology iff_elim_r) ih))
        let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
        exact l3
  | impl φ ψ ih1 ih2 =>
      exact Proof.mp (Proof.mp (Proof.tautology iff_imp) ih1) ih2
  | box φ ih =>
      let l1 := Proof.mp Proof.ax_k (Proof.necess (Proof.mp (Proof.tautology iff_elim_l) ih))
      let l2 := Proof.mp Proof.ax_k (Proof.necess (Proof.mp (Proof.tautology iff_elim_r) ih))
      let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
      exact l3
  | _ =>
      exact Proof.mp (Proof.mp (Proof.tautology iff_intro) (Proof.tautology imp_refl)) (Proof.tautology imp_refl)

theorem rename_all_bound (φ : Form N) (x : SVAR) : ⊨ (φ ⟷ (φ.replace_bound x)) := by
  exact WeakSoundness (rename_all_bound_pf φ x)

theorem exists_replace : ⊢ ((ex x, φ.replace_bound y) ⟶ (ex x, φ)) := by
  let l1 := replace_neg ▸ Proof.mp (Proof.tautology iff_elim_l) (rename_all_bound_pf (∼φ) y)
  let l2 := Proof.mp Proof.b363 (Proof.general x l1)
  let l3 := Proof.mp (Proof.tautology contrapositive) l2
  exact l3
