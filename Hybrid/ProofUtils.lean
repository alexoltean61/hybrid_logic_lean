import Hybrid.Substitutions
import Hybrid.Proof
import Hybrid.ListUtils

namespace Proof

theorem iff_mp (h : ⊢ (φ ⟷ ψ)) : ⊢ (φ ⟶ ψ) :=
  mp (tautology conj_elim_l) h

theorem iff_mpr (h : ⊢ (φ ⟷ ψ)) : ⊢ (ψ ⟶ φ) :=
  mp (tautology conj_elim_r) h

theorem hs (h1 : ⊢ (φ ⟶ ψ)) (h2 : ⊢ (ψ ⟶ χ)) : ⊢ (φ ⟶ χ) :=
  mp (mp (tautology hs_taut) h1) h2

theorem rename_bound {φ : Form N} (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((all x, φ) ⟷ all y, φ[y // x]) := by
  rw [Form.iff]
  apply mp
  . apply mp
    . apply tautology
      apply conj_intro
    . have l1 := ax_q2_svar φ x y h2
      have l2 := general y l1
      have l3 := ax_q1 (all x, φ) (φ[y // x]) (notoccurs_notfree h1)
      have l4 := mp l3 l2
      exact l4
  . have ⟨resubst, reid⟩ := rereplacement φ x y h1 h2
    have l1 := ax_q2_svar (φ[y//x]) y x resubst
    rw [reid] at l1
    have l3 := general x l1
    by_cases xy : x = y
    . rw [←xy] at h1
      have notf := preserve_notfree x y (notoccurs_notfree (@notocc_beforeafter_subst N φ x y h1))
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := mp l4 l3
      exact l5
    . have notf := preserve_notfree x y (@notfree_after_subst N φ x y xy)
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := mp l4 l3
      exact l5

theorem rename_bound_ex (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((ex x, φ) ⟷ ex y, φ[y // x]) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply mp
    . apply tautology
      apply iff_elim_l
    . apply tautology
      apply iff_not
  .
    apply rename_bound
    repeat { simp [occurs, is_substable]; assumption }

-- Quite bothersome to work with subtypes and coerce properly.
-- The code looks ugly, but in essence it follows the proof given
-- in LaTeX.
theorem Deduction {Γ : Set (Form N)} : Γ ⊢ (ψ ⟶ φ) iff (Γ ∪ {ψ}) ⊢ φ := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hpf⟩ =>
        have l1 := mp (tautology com12) hpf
        have l2 := mp (tautology imp) l1
        have pfmem : ψ ∈ Γ ∪ {ψ} := by simp
        let L' : List ↑(Γ ∪ {ψ}) := ⟨ψ, pfmem⟩ :: list_convert L
        rw [conj_incl] at l2
        exact ⟨L', l2⟩
  . intro h
    match h with
    | ⟨L', hpf⟩ =>
      have t_ax1 := tautology (@ax_1 N (conjunction (Γ ∪ {ψ}) L'⟶φ) ψ)
      have l1 := mp t_ax1 hpf
      have l2 := mp (tautology com12) l1
      by_cases elem : elem' L' ψ
      . have t_help := tautology (deduction_helper L' ψ (ψ⟶φ) elem)
        have l3 := mp t_help l2
        have l4 := mp (tautology idem) l3
        have not_elem_L' := eq_false_of_ne_true (@filter'_filters N Γ ψ L')
        let L : List Γ := list_convert_rev (filter' L' ψ) not_elem_L'
        rw [conj_incl_rev (filter' L' ψ) not_elem_L'] at l4
        exact ⟨L, l4⟩
      . have elem : elem' L' ψ = false := by simp only [elem]
        let L : List Γ := list_convert_rev L' elem
        rw [conj_incl_rev L' elem] at l2
        exact ⟨L, l2⟩

lemma increasing_consequence (h1 : Γ ⊢ φ) (h2 : Γ ⊆ Δ) : Δ ⊢ φ := by
  simp [SyntacticConsequence] at h1 ⊢
  let ⟨L, pf⟩ := h1
  clear h1
  let L' := list_convert_general h2 L
  exists L'
  rw [conj_incl_general h2 L] at pf
  exact pf

theorem Γ_empty {φ : Form N} : ∅ ⊢ φ iff ⊢ φ := by
  unfold SyntacticConsequence
  apply TypeIff.intro
  . intro pf
    have ⟨L, pf⟩ := pf
    have := empty_list L
    simp [this, conjunction] at pf
    apply mp
    . have : ⊢(((⊥⟶⊥)⟶φ)⟶φ) := by
        apply tautology
        apply imp_taut
        eval
      exact this
    . exact pf
  . intro pf
    let L : List ↑{x : Form N | False} := []
    exists L
    simp [conjunction]
    apply mp
    . apply tautology
      apply ax_1
    . exact pf

theorem Γ_theorem : ⊢ φ → (∀ Γ, Γ ⊢ φ) := by
  intro h Γ
  apply increasing_consequence
  apply Γ_empty.mpr h
  simp

theorem Γ_theorem_rev : (∀ Γ, Γ ⊢ φ) → ⊢ φ := by
  intro h
  apply Γ_empty.mp
  apply h

theorem Γ_theorem_iff : ⊢ φ iff (∀ Γ, Γ ⊢ φ) := by
  apply TypeIff.intro <;> first | apply Γ_theorem | apply Γ_theorem_rev

theorem Γ_premise : φ ∈ Γ → Γ ⊢ φ := by
  intro mem
  have : Γ = Γ ∪ {φ} := by simp [mem]
  rw [this]
  apply Deduction.mp
  apply Γ_theorem
  apply tautology
  eval

theorem Γ_mp_helper1 {Γ : Set (Form N)} {φ ψ χ : Form N} : (Γ ⊢ ((φ ⋀ ψ) ⟶ χ)) iff ((Γ ∪ {φ}) ⊢ (ψ ⟶ χ)) := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hL⟩ =>
        have l1 := hs hL (tautology exp)
        have l2 : Γ ⊢ (φ ⟶ ψ ⟶ χ) := ⟨L, l1⟩
        have l3 := Deduction.mp l2
        exact l3
  . intro h
    have h := Deduction.mpr h
    match h with
    | ⟨L, hL⟩ =>
        have l1 := hs hL (tautology imp)
        have l2 : Γ ⊢ (φ ⋀ ψ ⟶ χ) := ⟨L, l1⟩
        exact l2

theorem Γ_mp_helper2 {Γ : Set (Form N)} {L : List Γ} (h : Γ⊢(conjunction Γ L⟶ψ)) : Γ ⊢ ψ := by
  induction L with
  | nil =>
      rw [conjunction] at h
      have ⟨L, hL⟩ := h
      have l1 := mp (tautology com12) hL
      have l2 := mp (tautology (imp_taut imp_refl)) l1
      exists L
  | cons head tail ih =>
      have h := Γ_mp_helper1.mp h
      have : (Γ ∪ {↑head}) = Γ := by simp [head.2]
      rw [this] at h
      exact ih h

theorem Γ_mp (h1: Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ φ) : Γ ⊢ ψ := by
  match h1 with
  | ⟨L1, hL1⟩ =>
    match h2 with
    | ⟨L2, hL2⟩ =>
        have := mp (mp (tautology mp_help) hL1) hL2
        have : Γ ⊢ (conjunction Γ L2⟶ψ) := ⟨L1, this⟩
        exact Γ_mp_helper2 this

theorem Γ_neg_intro {φ : Form N} (h1 : Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ (φ ⟶ ∼ψ)) : Γ ⊢ (∼φ) := by
  have l1 := tautology (@neg_intro N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

theorem Γ_neg_elim {φ : Form N} {φ : Form N} (h : Γ ⊢ (∼∼φ)) : Γ ⊢ φ := by
  have l1 := tautology (@dne N φ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_conj_intro {φ : Form N} (h1 : Γ ⊢ φ) (h2 : Γ ⊢ ψ) : Γ ⊢ (φ ⋀ ψ) := by
  have l1 := tautology (@conj_intro N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

theorem Γ_conj_elim_l {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ φ := by
  have l1 := tautology (@conj_elim_l N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_conj_elim_r {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ ψ := by
  have l1 := tautology (@conj_elim_r N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_disj_intro_l {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (φ ⋁ ψ) := by
  have l1 := tautology (@disj_intro_l N φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

theorem Γ_disj_intro_r {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (ψ ⋁ φ) := by
  have l1 := tautology (@disj_intro_r N φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

theorem Γ_disj_elim {φ : Form N} (h1 : Γ ⊢ (φ ⋁ ψ)) (h2 : Γ ⊢ (φ ⟶ χ)) (h3 : Γ ⊢ (ψ ⟶ χ)) : Γ ⊢ χ := by
  have l1 := tautology (@disj_elim N φ ψ χ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  have l5 := Γ_mp l4 h3
  exact l5

theorem Γ_univ_intro {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) (h2 : occurs y φ = false) (h3 : is_substable φ y x) : Γ ⊢ φ → Γ ⊢ (all y, φ[y // x]) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Γ L) φ this
      have l4 := mp l3 l2
      have l5 := iff_mp (rename_bound h2 h3)
      have l6 := hs l4 l5
      exact ⟨L, l6⟩

theorem Γ_univ_intro' {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) : Γ ⊢ φ → Γ ⊢ (all x, φ) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Γ L) φ this
      have l4 := mp l3 l2
      exists L

theorem dn_equiv_premise {φ : Form N} : Γ ⊢ (∼∼φ) iff Γ ⊢ φ := by
  have l1 := tautology (@dne N φ)
  have l2 := tautology (@dni N φ)
  rw [SyntacticConsequence, SyntacticConsequence]
  apply TypeIff.intro
  repeat (
    intro ⟨L, _⟩;
    exists L;
    apply hs;
    repeat assumption
  )

section Nominals

theorem generalize_constants {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) : ⊢ φ → ⊢ (all x, φ[x // i]) := by
    intro pf
    apply general x
    induction pf generalizing x with
    | @tautology φ ht      =>
        apply tautology
        simp [Tautology] at ht ⊢
        intro e
        let f'  : Form N → Bool := λ φ => if (e.f <| φ[x//i]) then true else false
        let e'  : Eval N := ⟨f', by simp [e.p1, nom_subst_svar], by simp [e.p2, nom_subst_svar]⟩
        rw [show ((e.f <| φ[x//i]) ↔ e'.f φ) by simp]
        exact ht e'
    | @general φ v _ ih   =>
        simp only [nom_subst_svar, Form.new_var, max] at h ⊢
        by_cases hc : (v + 1).letter > (Form.new_var φ).letter
        . simp [hc] at h
          simp only [gt_iff_lt] at hc
          have := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
          exact general v this
        . simp [hc] at h
          exact general v (ih h)
    | @necess   ψ _ ih     =>
        simp only [nom_subst_svar, occurs] at h ⊢
        apply necess; apply ih; assumption
    | @mp φ ψ _ _ ih1 ih2  =>
        simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false, not_and,
          Bool.not_eq_false] at ih1
        -- show ψ[y // i] for some y that does not
        --    occur in either φ or ψ
        -- generalize, get  all y, ψ[y // i]
        -- then apply axiom Q2 and get:
        --                   (ψ[y // i])[x // y]
        -- this should bring you to:
        --                   ψ[x // i]
        let y := (φ ⟶ ψ).new_var
        have ih1_cond : y ≥ (φ⟶ψ).new_var := Nat.le.refl
        have ⟨ih2_cond, sub_cond⟩ := new_var_geq1 ih1_cond
        have ih1 := ih1 ih1_cond
        have ih2 := ih2 ih2_cond
        rw [nom_subst_svar] at ih1
        have l1  := general y (mp ih1 ih2)
        have l2  := ax_q2_svar (ψ[y//i]) y x (new_var_subst h)
        have l3  := mp l2 l1
        rw [nom_subst_trans i x y sub_cond] at l3
        exact l3
    | @ax_k φ ψ            =>
        simp only [nom_subst_svar]
        apply ax_k
    | @ax_q1 φ ψ v h2       =>
        simp only [nom_subst_svar]
        apply ax_q1
        have := new_var_geq2 (new_var_geq1 h).left
        have ha : x ≥ φ.new_var := (new_var_geq1 this.right).left
        have hb : v ≠ x := diffsvar this.left
        have := (scz i ha hb).mpr
        rw [contraposition, Bool.not_eq_true, Bool.not_eq_true] at this
        apply this
        exact h2
    | @ax_q2_svar φ y v h2  =>
        have := new_var_geq2 (new_var_geq1 h).left
        have c2 : x ≥ φ.new_var := this.right
        have c3 : y ≠ x := diffsvar this.left
        have c  := new_var_subst' i h2 c2 c3
        have l1 := ax_q2_svar (φ[x//i]) y v c
        rw [nom_svar_subst_symm c3] at l1
        exact l1
    | @ax_q2_nom  φ v j    =>
        simp [nom_subst_svar]
        have f3 := diffsvar (new_var_geq2 (new_var_geq1 h).left).left
        by_cases ji : j = i
        . rw [ji] at h ⊢
          have f2 := (new_var_geq2 (new_var_geq1 h).left).right
          have f1 := @new_var_subst'' N φ x v f2
          have := new_var_subst' i f1 f2 f3
          have := ax_q2_svar (φ[x//i]) v x this
          rw [subst_collect_all]
          exact this
        . rw [←(nom_nom_subst_symm ji f3)]
          exact ax_q2_nom (φ[x//i]) v j
    | @ax_name    v        =>
        exact ax_name v
    | @ax_nom   φ v m n    =>
        simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom]
        apply ax_nom
    | @ax_brcn  φ v        =>
        apply ax_brcn

  lemma generalize_constants_rev {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) : ⊢ (all x, φ[x // i]) → ⊢ φ := by
    intro pf
    have l1 := ax_q2_nom (φ[x//i]) x i
    have l2 := mp l1 pf
    rw [svar_svar_nom_subst h, nom_subst_self] at l2
    exact l2

  theorem generalize_constants_iff {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) : ⊢ φ iff ⊢ (all x, φ[x // i]) := by
    apply TypeIff.intro
    . apply generalize_constants; assumption
    . apply generalize_constants_rev; assumption

  theorem rename_constants (j i : NOM N) (h : nom_occurs j φ = false) : ⊢ φ iff ⊢ (φ[j // i]) := by
    apply TypeIff.intro
    . intro pf
      let x := φ.new_var
      have x_geq : x ≥ φ.new_var := by simp; apply Nat.le_refl
      have l1 := generalize_constants i x_geq pf
      have l2 := ax_q2_nom (φ[x // i]) x j
      have l3 := mp l2 l1
      have : φ[x//i][j//x] = φ[j//i] := svar_svar_nom_subst x_geq
      rw [this] at l3
      exact l3
    . intro pf
      let x := (φ[j//i]).new_var
      have x_geq : x ≥ (φ[j//i]).new_var := by simp; apply Nat.le_refl
      have l1 := generalize_constants j x_geq pf
      have : φ[j//i][x//j] = φ[x//i] := dbl_subst_nom i h
      rw [this] at l1
      have l2 := ax_q2_nom (φ[x // i]) x i
      have l3 := mp l2 l1
      rw [←eq_new_var] at x_geq
      have : φ[x//i][i//x] = φ[i//i] := svar_svar_nom_subst x_geq
      rw [nom_subst_self] at this
      rw [this] at l3
      exact l3

  theorem proof_sketch (h : nocc_bulk_property l₁ l₂ φ) : ⊢ φ iff ⊢ (φ.bulk_subst l₁ l₂) := by
    induction l₁ generalizing φ l₂ with
    | nil => cases l₂ <;> (simp [Form.bulk_subst]; apply TypeIff.refl)
    | cons h_new t_new ih =>
        cases l₂ with
        | nil => simp [Form.bulk_subst]; apply TypeIff.refl
        | cons h_old t_old =>
            simp [Form.bulk_subst]
            have : nom_occurs h_new φ = false := by
                apply @nocc_bulk TotalSet h_new [] []
                simp
                unfold nocc_bulk_property at h
                let n: Fin (List.length (h_new :: t_new)) := ⟨0, by simp⟩
                have : h_new = (h_new :: t_new)[n] := by get_elem_tactic
                have := @h n h_new this
                simp [show ↑n = 0 by simp] at this
                simp
                assumption
            have := rename_constants h_new h_old this
            apply this.trans
            apply ih
            apply nocc_bulk_property_induction
            assumption

  theorem pf_odd_noms : ⊢ φ iff ⊢ φ.odd_noms := by
    apply proof_sketch
    apply has_nocc_bulk_property

  theorem pf_odd_noms_set : Γ ⊢ φ iff Γ.odd_noms ⊢ φ.odd_noms := by
    simp [SyntacticConsequence]
    apply TypeIff.intro
    . intro ⟨L, h⟩
      have h := (odd_conj Γ L) ▸ odd_impl ▸ pf_odd_noms.mp h
      exists L.to_odd
    . intro ⟨L', h'⟩
      have h' := pf_odd_noms.mpr (odd_impl.symm ▸ (odd_conj_rev Γ L').symm ▸ h')
      exists L'.odd_to

  theorem odd_noms_set_cons (Γ : Set (Form TotalSet)) : consistent Γ ↔ consistent Γ.odd_noms := by
    unfold consistent
    have : Form.bttm = Form.bttm.odd_noms := by simp [Form.odd_noms, Form.odd_list_noms, Form.bulk_subst]
    conv => rhs; rw [this]
    apply Iff.intro <;> (
      intro h1 h2
      apply h1
      first | apply pf_odd_noms_set.mp | apply pf_odd_noms_set.mpr
      assumption
    )

end Nominals

theorem ax_nom_instance {φ : Form N} (i : NOM N) (m n : ℕ) : ⊢ (iterate_pos m (i ⋀ φ) ⟶ iterate_nec n (i ⟶ φ)) := by
  let x := φ.new_var
  have x_geq : x ≥ φ.new_var := by simp [SVAR.le]
  have l1 := @ax_nom N (φ[x//i]) x m n
  have l2 := ax_q2_nom (iterate_pos m (x⋀(φ[x//i]))⟶iterate_nec n (x⟶(φ[x//i]))) x i
  have l3 := mp l2 l1
  clear l1 l2
  rw [subst_nom, pos_subst, nec_subst, nom_svar_rereplacement x_geq] at l3
  exact l3

theorem ax_q2_svar_instance : ⊢ ((all x, φ) ⟶ φ) := by
  have : φ.new_var ≥ φ.new_var := by simp [SVAR.le]
  apply hs
  apply mp
  . apply tautology
    apply iff_elim_l
  apply rename_bound
  apply new_var_is_new
  apply new_var_subst''
  assumption
  have ⟨l, r⟩ := (rereplacement φ x (φ.new_var) new_var_is_new (new_var_subst'' this))
  conv => rhs; rhs; rw [←r]
  apply ax_q2_svar
  assumption

theorem Γ_univ_elim (h : Γ ⊢ (all x, φ)) : Γ ⊢ φ := by
  exact Γ_mp (Γ_theorem ax_q2_svar_instance Γ) h

theorem rename_var (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ φ iff ⊢ (φ[y // x]) := by
  apply TypeIff.intro
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact y
    apply mp
    . apply mp
      apply tautology
      apply iff_elim_l
      apply rename_bound
      repeat assumption
    . apply general
      assumption
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact x
    apply mp
    . apply mp
      apply tautology
      apply iff_elim_r
      apply rename_bound
      repeat assumption
    . apply general
      assumption

theorem ax_q2_contrap {i : NOM N} {x : SVAR} : ⊢ (φ[i//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply tautology
    apply dni
  . apply mp
    apply tautology
    apply contrapositive
    apply ax_q2_nom

theorem ax_q2_svar_contrap {x y : SVAR} (h : is_substable φ y x) : ⊢ (φ[y//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply tautology
    apply dni
  . apply mp
    apply tautology
    apply contrapositive
    apply ax_q2_svar
    simp [is_substable]
    exact h

theorem ax_nom_instance' (x : SVAR) (m n : ℕ) : ⊢ (iterate_pos m (x ⋀ φ) ⟶ iterate_nec n (x ⟶ φ)) := by
  apply mp
  apply ax_q2_svar_instance
  assumption
  apply ax_nom

-- Lemma 3.6.1
lemma b361 {φ : Form N} : ⊢ ((φ ⟶ ex x, ψ) ⟶ ex x, (φ ⟶ ψ)) := by
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) := {∼(ex x, φ⟶ψ)}
    have l1 : Γ ⊢ (∼(ex x, φ⟶ψ)) := by apply Γ_premise; simp
    rw [Form.bind_dual] at l1
    have l2 := Γ_theorem (tautology (@dne N (all x, ∼(φ⟶ψ)))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_q2_svar_instance x N (∼(φ⟶ψ))) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (tautology (taut_iff_mp (@imp_neg N φ ψ))) Γ
    have l7 := Γ_mp l6 l5
    have l8 := Γ_conj_elim_l l7
    have l9 := Γ_conj_elim_r l7
    have l10 : Γ ⊢ (∼(ex x, ψ)) := by
      rw [Form.bind_dual]
      apply Γ_mp; apply Γ_theorem; apply tautology; apply dni
      apply Γ_univ_intro'
      . simp [is_free, -implication_disjunction]
      . exact l9
    have l11 := Γ_conj_intro l8 l10
    have l12 := Γ_mp (Γ_theorem (tautology (taut_iff_mpr (@imp_neg N φ (ex x, ψ)))) Γ) l11
    exact l12

-- Lemma 3.6.2
lemma b362 {φ : Form N} (h : is_free x φ = false) : ⊢ ((φ ⋀ ex x, ψ) ⟶ ex x, (φ ⋀ ψ)) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) :=  {∼∼(all x, ∼(φ⋀ψ))}
    have l1 : Γ ⊢ (all x, ∼(φ⋀ψ)) := by
      apply Γ_mp; apply Γ_theorem; apply tautology; apply dne
      apply Γ_premise; simp
    have l2 := Γ_theorem (@ax_q2_svar_instance x N (∼(φ⋀ψ))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_mp (Γ_theorem (tautology (taut_iff_mpr (@neg_conj N φ ψ))) Γ) l3
    have l5 : Γ⊢ (all x, (φ⟶∼ψ)) := by
      apply Γ_univ_intro'
      simp [is_free, -implication_disjunction]
      exact l4
    have l6 := Deduction.mp (Γ_mp (Γ_theorem (ax_q1 φ (∼ψ) h) Γ) l5)
    have l7 := Deduction.mpr (Γ_mp (Γ_theorem (tautology (@dni N (all x, ∼ψ))) (Γ ∪ {φ})) l6)
    have l8 := Γ_mp (Γ_theorem (tautology (taut_iff_mp (@neg_conj N φ (∼(all x, ∼ψ))))) Γ) l7
    exact l8

lemma ex_conj_comm {φ : Form N} : ⊢ ((ex x, (φ ⋀ ψ)) ⟶ (ex x, (ψ ⋀ φ))) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) := {∼∼(all x, ∼(ψ⋀φ))}
    have l1 : Γ ⊢ (∼∼(all x, ∼(ψ⋀φ))) := by apply Γ_premise; simp
    have l2 := Γ_theorem (tautology (@dne N (all x, ∼(ψ⋀φ)))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_q2_svar_instance x N (∼(ψ⋀φ))) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (tautology (@conj_comm_t' N ψ φ)) Γ
    have l7 := Γ_mp l6 l5
    have l8 : Γ⊢(all x, ∼(φ⋀ψ)) := by
      apply Γ_univ_intro'
      simp [is_free, -implication_disjunction]
      exact l7
    have l9 := Γ_theorem (tautology (@dni N (all x, ∼(φ⋀ψ)))) Γ
    have l10 := Γ_mp l9 l8
    exact l10

lemma b362' {φ : Form N} (h : is_free x φ = false) : ⊢ (((ex x, ψ) ⋀ φ) ⟶ ex x, (ψ ⋀ φ)) := by
  have l1 := tautology (@conj_comm_t N (ex x, ψ) φ)
  have l2 := @b362 N x ψ φ h
  have l3 := hs l2 ex_conj_comm
  have l4 := hs l1 l3
  exact l4

-- Lemma 3.6.3
lemma b363  {φ : Form N} : ⊢ ((all x, (φ ⟶ ψ)) ⟶ ((all x, φ) ⟶ (all x, ψ))) := by
  let Γ : Set (Form N) := ∅ ∪ {all x, φ⟶ψ} ∪ {all x, φ}
  have l1 : Γ ⊢ (all x, (φ ⟶ ψ)) := by apply Γ_premise; simp
  have l2 : Γ⊢(φ⟶ψ) := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l1
  have l3 : Γ⊢(all x, φ) := by apply Γ_premise; simp
  have l4 : Γ⊢φ := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l3
  have l5 : ⊢((all x, φ⟶ψ)⟶((all x, φ) ⟶ ψ)) := by
    apply Γ_empty.mp; apply Deduction.mpr; apply Deduction.mpr
    apply Γ_mp
    repeat assumption
  have l6 := general x l5
  have : is_free x (all x, φ⟶ψ) = false := by simp [is_free]
  have l7 := @ax_q1 N (all x, φ⟶ψ) ((all x, φ)⟶ψ) x this
  have l8 := mp l7 l6
  have : is_free x (all x, φ) = false := by simp [is_free]
  have l9 := @ax_q1 N (all x, φ) ψ x this
  have l10 := hs l8 l9
  exact l10

theorem dn_nec : ⊢ (□ φ ⟷ □ ∼∼φ) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply tautology
  apply conj_intro
  repeat (
    apply mp
    apply ax_k
    apply necess
    apply tautology
    first | apply dni | apply dne
  )

theorem dn_all : ⊢ ((all x, φ) ⟷ all x, ∼∼φ) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply tautology
  apply conj_intro
  repeat (
    apply mp
    apply b363
    apply general
    apply tautology
    first | apply dni | apply dne
  )

lemma bind_dual : ⊢((all x, ψ)⟷∼(ex x, ∼ψ)) := by
    rw [Form.bind_dual]
    apply mp; apply mp
    apply tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply tautology
        apply iff_elim_l
        apply dn_all
      . apply tautology
        apply dni
    . apply hs
      . apply tautology
        apply dne
      . apply mp
        apply tautology
        apply iff_elim_r
        apply dn_all

lemma nec_dual : ⊢((□ ψ)⟷∼(◇ ∼ψ)) := by
    rw [Form.diamond]
    apply mp; apply mp
    apply tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply tautology
        apply iff_elim_l
        apply dn_nec
      . apply tautology
        apply dni
    . apply hs
      . apply tautology
        apply dne
      . apply mp
        apply tautology
        apply iff_elim_r
        apply dn_nec

lemma diw_impl (h : ⊢(φ ⟶ ψ)) : ⊢ (◇φ ⟶ ◇ψ) := by
  have l1 := mp (tautology contrapositive) h
  have l2 := necess l1
  have l3 := mp ax_k l2
  have l4 := mp (tautology contrapositive) l3
  exact l4

lemma ax_brcn_contrap {φ : Form N} : ⊢ ((◇ ex x, φ) ⟶ (ex x, ◇ φ)) := by
  simp only [Form.diamond, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) := {all x, ∼∼(□∼φ)}
    have l1 : Γ ⊢ (all x, ∼∼(□∼φ)) := by apply Γ_premise; simp
    have l2 := Γ_theorem (mp (tautology iff_elim_r) (@dn_all x N (□∼φ))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_brcn N (∼φ) x) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (mp (tautology iff_elim_l) (@dn_nec N (all x, ∼φ))) Γ
    have l7 := Γ_mp l6 l5
    exact l7

section MCS

theorem MCS_pf (h : MCS Γ) : Γ ⊢ φ → φ ∈ Γ := by
  intro pf
  rw [←(@not_not (φ ∈ Γ))]
  intro habs
  have ⟨cons, pf_bot⟩ := h
  have ⟨pf_bot, _⟩ := not_forall.mp (pf_bot habs)
  clear h
  apply cons
  apply Γ_mp
  apply Deduction.mpr
  assumption
  assumption

theorem MCS_thm (h : MCS Γ) : ⊢ φ → φ ∈ Γ := by
  intro
  apply MCS_pf h
  apply Γ_theorem
  assumption

theorem MCS_mp (h : MCS Γ) (h1 : φ ⟶ ψ ∈ Γ) (h2 : φ ∈ Γ) : ψ ∈ Γ := by
  rw [←@not_not (ψ ∈ Γ)]
  intro habs
  have ⟨pf_bot, _⟩ := not_forall.mp (h.right habs)
  apply h.left
  apply Γ_mp
  apply Deduction.mpr
  assumption
  apply Γ_mp
  repeat (apply Γ_premise; assumption)

theorem MCS_conj {Γ : Set (Form N)} (hmcs : MCS Γ) (φ ψ : Form N) : (φ ∈ Γ ∧ ψ ∈ Γ) ↔ (φ ⋀ ψ) ∈ Γ := by
  apply Iff.intro
  . intro ⟨l, r⟩
    apply MCS_pf hmcs
    exact Γ_conj_intro (Γ_premise l) (Γ_premise r)
  . intro h
    apply And.intro <;> apply MCS_pf hmcs
    exact Γ_conj_elim_l (Γ_premise h)
    exact Γ_conj_elim_r (Γ_premise h)

theorem MCS_max {Γ : Set (Form N)} (hmcs : MCS Γ) : (φ ∉ Γ ↔ (∼φ) ∈ Γ) := by
  apply Iff.intro
  . intro h
    have ⟨pf_bot, _⟩ := not_forall.mp (hmcs.2 h)
    apply MCS_pf hmcs; apply Deduction.mpr
    exact pf_bot
  . intro h habs
    apply hmcs.1
    apply Γ_mp (Γ_premise h) (Γ_premise habs)

theorem MCS_impl {Γ : Set (Form N)} (hmcs : MCS Γ) : (φ ∈ Γ → ψ ∈ Γ) ↔ ((φ⟶ψ) ∈ Γ) := by
  apply Iff.intro
  . intro h
    by_cases hc : φ ∈ Γ
    . apply MCS_pf hmcs
      apply Deduction.mpr
      apply increasing_consequence
      exact Γ_premise (h hc)
      simp
    . simp only [MCS_max, hmcs, Form.neg] at hc
      apply MCS_pf hmcs; apply Deduction.mpr
      apply Γ_mp
      apply @Γ_theorem N (⊥ ⟶ ψ)
      apply tautology
      eval
      exact Deduction.mp (Γ_premise hc)
  . intro h1 h2
    apply MCS_pf hmcs
    exact Γ_mp (Γ_premise h1) (Γ_premise h2)

theorem MCS_iff {Γ : Set (Form N)} (hmcs : MCS Γ) : ((φ⟷ψ) ∈ Γ) ↔ (φ ∈ Γ ↔ ψ ∈ Γ) := by
  simp only [Form.iff, ←MCS_conj, ←MCS_impl, hmcs]
  apply Iff.intro
  <;> intros; apply Iff.intro
  . apply And.left
    assumption
  . apply And.right
    assumption
  apply And.intro <;> simp [*]

theorem MCS_rw {Γ : Set (Form N)} (hmcs : MCS Γ) (pf : ⊢ (φ ⟷ ψ)) : φ ∈ Γ ↔ ψ ∈ Γ := by
  rw [←MCS_iff hmcs]
  apply MCS_pf hmcs
  exact Γ_theorem pf Γ

lemma MCS_rich : ∀ {Θ : Set (Form N)}, (MCS Θ) → (witnessed Θ) → ∃ i : NOM N, ↑i ∈ Θ := by
  intro Θ mcs wit
  have := Proof.MCS_thm mcs (Proof.ax_name ⟨0⟩)
  have := wit this
  simp [subst_nom] at this
  exact this

lemma MCS_with_svar_witness : ∀ {Θ : Set (Form N)} {x y : SVAR} (_ : is_substable φ y x), (MCS Θ) → φ[y//x] ∈ Θ → (ex x, φ) ∈ Θ := by
  intro Θ x y h1 mcs h2
  apply MCS_mp mcs
  apply MCS_thm mcs
  apply ax_q2_svar_contrap h1
  repeat assumption

end MCS

theorem iff_subst : ⊢ ((φ ⟷ ψ) ⟶ (ψ ⟷ χ) ⟶ (φ ⟷ χ)) := by
  apply tautology
  admit

theorem pf_iff_subst : ⊢ (φ ⟷ ψ) → ⊢ (ψ ⟷ χ) → ⊢ (φ ⟷ χ) := by
  intro h1 h2
  apply mp
  apply mp
  apply iff_subst
  exact ψ
  repeat assumption
