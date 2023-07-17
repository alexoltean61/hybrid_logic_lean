import Hybrid.Proof
import Hybrid.ListUtils
import Std.Data.List.Basic
import Mathlib.Data.List.Nodup

namespace Proof

theorem iff_mp (h : ⊢ (φ ⟷ ψ)) : ⊢ (φ ⟶ ψ) := by
  rw [Form.iff] at h
  have := tautology (@conj_elim_l (φ ⟶ ψ) (ψ ⟶ φ))
  exact mp this h

theorem hs (h1 : ⊢ (φ ⟶ ψ)) (h2 : ⊢ (ψ ⟶ χ)) : ⊢ (φ ⟶ χ) := by
  admit

theorem rename_bound (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((all x, φ) ⟷ all y, φ[y // x]) := by
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
      have notf := preserve_notfree x y (notoccurs_notfree (@notocc_beforeafter_subst φ x y h1))
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := mp l4 l3
      exact l5
    . have notf := preserve_notfree x y (@notfree_after_subst φ x y xy)
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := mp l4 l3
      exact l5

-- Quite bothersome to work with subtypes and coerce properly.
-- The code looks ugly, but in essence it follows the proof given
-- in LaTeX.
theorem Deduction (Γ : Set Form) : Γ ⊢ (ψ ⟶ φ) ↔ (Γ ∪ {ψ}) ⊢ φ := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨L, hpf⟩ =>
        have t_com12 := tautology (@com12 (conjunction Γ L) ψ φ)
        have l1 := mp t_com12 hpf
        have t_imp := tautology (@imp ψ (conjunction Γ L) φ)
        have l2 := mp t_imp l1
        have pfmem : ψ ∈ Γ ∪ {ψ} := by simp
        let L' : List ↑(Γ ∪ {ψ}) := ⟨ψ, pfmem⟩ :: list_convert L
        rw [conj_incl] at l2
        exact ⟨L', l2⟩ 
  . intro h
    match h with
    | ⟨L', hpf⟩ =>
      have t_ax1 := tautology (@ax_1 (conjunction (Γ ∪ {ψ}) L'⟶φ) ψ)
      have l1 := mp t_ax1 hpf
      have t_com12 := tautology (@com12 ψ (conjunction (Γ ∪ {ψ}) L') φ)
      have l2 := mp t_com12 l1
      by_cases elem : elem' L' ψ
      . have t_help := tautology (deduction_helper L' ψ (ψ⟶φ) elem)
        have l3 := mp t_help l2
        have t_idem := tautology (@idem (conjunction (Γ ∪ {ψ}) (filter' L' ψ)) ψ φ)
        have l4 := mp t_idem l3
        have not_elem_L' := eq_false_of_ne_true (@filter'_filters Γ ψ L')
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

theorem Γ_theorem : ⊢ φ → (∀ Γ, Γ ⊢ φ) := by
  intro h Γ
  let L : List Γ := []
  exists L
  rw [conjunction]
  have l1 := tautology (@ax_1 φ (⊥ ⟶ ⊥))
  exact mp l1 h

theorem Γ_mp (h1: Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ φ) : Γ ⊢ ψ := by
  match h1 with
  | ⟨L1, hL1⟩ =>
    match h2 with
    | ⟨L2, hL2⟩ =>
        let L3 := L1.append L2
        exists L3
        admit

theorem Γ_neg_intro (h1 : Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ (φ ⟶ ∼ψ)) : Γ ⊢ (∼φ) := by
  have l1 := tautology (@neg_intro φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

theorem Γ_neg_elim (h : Γ ⊢ (∼∼φ)) : Γ ⊢ φ := by
  have l1 := tautology (@dne φ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_conj_intro (h1 : Γ ⊢ φ) (h2 : Γ ⊢ ψ) : Γ ⊢ (φ ⋀ ψ) := by
  have l1 := tautology (@conj_intro φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

theorem Γ_conj_elim_l (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ φ := by
  have l1 := tautology (@conj_elim_l φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h 
  exact l3

theorem Γ_conj_elim_r (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ ψ := by
  have l1 := tautology (@conj_elim_r φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h 
  exact l3

theorem Γ_disj_intro_l (h : Γ ⊢ φ) : Γ ⊢ (φ ⋁ ψ) := by
  have l1 := tautology (@disj_intro_l φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

theorem Γ_disj_intro_r (h : Γ ⊢ φ) : Γ ⊢ (ψ ⋁ φ) := by
  have l1 := tautology (@disj_intro_r φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

theorem Γ_disj_elim (h1 : Γ ⊢ (φ ⋁ ψ)) (h2 : Γ ⊢ (φ ⟶ χ)) (h3 : Γ ⊢ (ψ ⟶ χ)) : Γ ⊢ χ := by
  have l1 := tautology (@disj_elim φ ψ χ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  have l5 := Γ_mp l4 h3
  exact l5

theorem Γ_univ_intro {Γ : Set Form} {φ : Form} (h1 : ∀ ψ : Γ, is_free x ψ = false) (h2 : occurs y φ = false) (h3 : is_substable φ y x) : Γ ⊢ φ → Γ ⊢ (all y, φ[y // x]) := by
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

theorem dn_equiv_premise : Γ ⊢ (∼∼φ) ↔ Γ ⊢ φ := by
  admit
  /-
  have l1 := tautology (@dne φ)
  have l2 := tautology (@dni φ)
  rw [SyntacticConsequence, SyntacticConsequence]
  admit
  -/

section Nominals

lemma new_var_geq1 : x ≥ (φ ⟶ ψ).new_var → (x ≥ φ.new_var ∧ x ≥ ψ.new_var) := by
  intro h
  simp [Form.new_var, max] at *
  split at h
  . apply And.intro
    . assumption
    . apply Nat.le_trans _ h
      apply Nat.le_of_lt
      assumption
  . apply And.intro
    . simp at *
      apply Nat.le_trans _ h
      assumption
    . assumption

lemma new_var_geq2 : x ≥ (all y, ψ).new_var → (x ≥ (y+1) ∧ x ≥ ψ.new_var) := by
  intro h
  simp [Form.new_var, max] at *
  split at h
  . apply And.intro
    . apply Nat.le_trans _ h
      apply Nat.le_of_lt
      assumption
    . assumption
  . apply And.intro
    . assumption
    . simp at *
      apply Nat.le_trans _ h
      assumption

lemma new_var_subst {φ : Form} {i : NOM} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable (φ[y//i]) x y := by
  induction φ with
  | nom  j  =>
      simp [nom_subst_svar]
      split <;> simp [is_substable]
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
      simp [Form.new_var, max, is_substable, nom_subst_svar] at h ⊢
      by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact ⟨ih1 h, ih2 this⟩
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact ⟨ih1 this, ih2 h⟩
  | box ψ ih         =>
      simp [Form.new_var, is_substable, nom_subst_svar] at h ⊢
      exact ih h
  | _  =>
      simp [is_substable]

lemma new_var_subst'' {φ : Form} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable φ x y := by
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
      simp [Form.new_var, max, is_substable, nom_subst_svar] at h ⊢
      by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact ⟨ih1 h, ih2 this⟩
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact ⟨ih1 this, ih2 h⟩
  | box ψ ih         =>
      simp [Form.new_var, is_substable, nom_subst_svar] at h ⊢
      exact ih h
  | _  =>
      simp [is_substable]

lemma scz {φ : Form} (i : NOM) (h : x ≥ φ.new_var) (hy : y ≠ x) : (is_free y φ) ↔ (is_free y (φ[x // i])) := by
  induction φ with
  | nom a       =>
      simp [nom_subst_svar] ; split <;> simp [is_free, hy]
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

lemma new_var_subst' {φ : Form} (i : NOM) {x y : SVAR} (h1 : is_substable φ v y) (h2 : x ≥ φ.new_var) (h3 : y ≠ x) : is_substable (φ[x//i]) v y := by
  induction φ with
  | nom  a      => simp [nom_subst_svar]; split <;> simp [is_substable]
  | bind z ψ ih =>
      have xge := (new_var_geq2 h2).right
      have := @scz x y ψ i xge h3
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

lemma nom_subst_trans (i : NOM) (x y : SVAR) (h : y ≥ φ.new_var) : φ[y // i][x // y] = φ[x // i] := by
  induction φ with
  | bttm => simp [nom_subst_svar, subst_svar]
  | prop => simp [nom_subst_svar, subst_svar]
  | nom _ =>
    simp [nom_subst_svar]
    split <;> simp [subst_svar]
  | svar z =>
    have nocc := ge_new_var_is_new h
    simp [subst_svar]
    split <;> simp [nom_subst_svar, occurs] at *; contradiction
  | bind z ψ ih =>
    simp [subst_svar]
    have := new_var_geq2 h
    by_cases hc : y = z
    . exfalso
      have := this.left
      simp [hc] at this
      have := Nat.ne_of_lt (Nat.lt_succ_of_le this)
      contradiction
    . simp [nom_subst_svar, ih this.right, hc]
  | impl ψ χ ih1 ih2 =>
      simp [nom_subst_svar, subst_svar, ih1, ih2, new_var_geq1 h]
  | box ψ ih         =>
      simp [Form.new_var] at h
      simp [nom_subst_svar, subst_svar, ih, h]

lemma nom_svar_subst_symm {v x y : SVAR} {i : NOM} (h : y ≠ x) : φ[x//i][v//y] = φ[v//y][x//i] := by
  induction φ <;> simp [subst_svar, nom_subst_svar, *] at *
  . split <;> simp[nom_subst_svar]
  . split <;> simp [subst_svar, h]
  . split <;> simp [nom_subst_svar]

lemma nom_nom_subst_symm {x y : SVAR} {j i : NOM} (h1 : j ≠ i) (h2 : y ≠ x) : φ[x//i][j//y] = φ[j//y][x//i] := by
  induction φ <;> simp [nom_subst_svar, subst_nom, *] at *
  . split <;> simp [nom_subst_svar, *]
  . split <;> simp [subst_nom, *]
  . split <;> simp [nom_subst_svar]

lemma subst_collect_all {x y : SVAR} {i : NOM} : φ[i//y][x//i] = φ[x//i][x//y] := by
  induction φ <;> simp [subst_svar, subst_nom, nom_subst_svar, *] at *
  . split <;> simp [nom_subst_svar]
  . split <;> simp [subst_svar]
  . split <;> simp [nom_subst_svar, *]

lemma pos_subst_nom {m : ℕ} {i : NOM} {v x : SVAR} : (iterate_pos m (v⋀φ))[x//i] = iterate_pos m (Form.svar v⋀φ[x//i]) := by
  induction m with
  | zero =>
      simp [iterate_pos, iterate_pos.loop, nom_subst_svar]
  | succ n ih =>
      simp [iterate_pos, iterate_pos.loop, nom_subst_svar] at ih ⊢
      rw [ih]

lemma nec_subst_nom {m : ℕ} {i : NOM} {v x : SVAR} : (iterate_nec m (v⟶φ))[x//i] = iterate_nec m (Form.svar v⟶φ[x//i]) := by
  induction m with
  | zero =>
      simp [iterate_nec, iterate_nec.loop, nom_subst_svar]
  | succ n ih =>
      simp [iterate_nec, iterate_nec.loop, nom_subst_svar] at ih ⊢
      rw [ih]

lemma diffsvar {v x : SVAR} (h : x ≥ v+1) : v ≠ x := by
  simp; intro abs; exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self v.letter) h)) (SVAR.mk.inj abs)  


theorem generalize_constants {φ : Form} {x : SVAR} (i : NOM) (h : x ≥ φ.new_var) : ⊢ φ → ⊢ (all x, φ[x // i]) := by
    intro pf
    apply general x
    induction pf generalizing x with
    | @tautology φ ht      =>  
        apply tautology
        simp [Tautology] at ht ⊢
        intro e
        let f'  : Form → Bool := λ φ => if (e.f <| φ[x//i]) then true else false
        let e'  : Eval := ⟨f', by simp [e.p1, nom_subst_svar], by simp [e.p2, nom_subst_svar]⟩
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
    | necess   ψ _ ih     =>  
        simp only [nom_subst_svar, occurs] at h ⊢
        exact necess (ψ[x//i]) (ih h)
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
        have l2  := @ax_q2_svar (ψ[y//i]) y x (new_var_subst h)
        have l3  := mp l2 l1
        rw [nom_subst_trans i x y sub_cond] at l3
        exact l3
    | @ax_k φ ψ            =>
        simp only [nom_subst_svar]
        exact @ax_k (φ[x//i]) (ψ[x//i])
    | @ax_q1 φ ψ v h2       =>
        simp only [nom_subst_svar]
        apply @ax_q1 (φ[x//i]) (ψ[x//i]) v
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
          have f1 := @new_var_subst'' φ x v f2
          have := new_var_subst' i f1 f2 f3
          have := ax_q2_svar (φ[x//i]) v x this
          rw [subst_collect_all]
          exact this
        . rw [←(nom_nom_subst_symm ji f3)]
          exact ax_q2_nom (φ[x//i]) v j
    | @ax_name    v        =>
        simp only [nom_subst_svar]
        exact ax_name v
    | @ax_nom   φ v m n    =>  
        simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom]
        exact @ax_nom (φ[x//i]) v m n
    | @ax_brcn  φ v        =>
        simp only [nom_subst_svar]
        exact @ax_brcn (φ[x//i]) v

  lemma dbl_subst_nom {j : NOM} {x : SVAR} (i : NOM) (h : nom_occurs j φ = false) : φ[j//i][x//j] = φ[x//i] := by
    induction φ <;> simp [nom_occurs, nom_subst_nom, nom_subst_svar, -implication_disjunction, *] at *
    . split <;> simp [nom_subst_svar, Ne.symm h]
    repeat simp [h, *] at *

  lemma svar_svar_nom_subst {i j : NOM} {x : SVAR} (h : x ≥ φ.new_var) : φ[x//i][j//x] = φ[j//i] := by
    induction φ <;> simp [nom_subst_svar, nom_subst_nom, subst_nom, -implication_disjunction, *] at *
    . apply Ne.symm; apply diffsvar; assumption
    . split <;> simp [subst_nom]
    . simp [new_var_geq1 h, *] at *
    . simp [Form.new_var] at h
      simp [h, *] at *
    . split
      . exfalso
        have := Ne.symm (diffsvar (new_var_geq2 h).left)
        contradiction
      . simp [new_var_geq2 h, *] at *
  
  lemma nom_subst_self {i : NOM} : φ[i // i] = φ := by
    induction φ <;> simp [nom_subst_nom, -implication_disjunction, *] at * 
    . intro h ; apply Eq.symm; assumption

  lemma eq_new_var {i j : NOM} : φ.new_var = (φ[i // j]).new_var := by
    induction φ <;> simp [Form.new_var, nom_subst_nom, *] at * 
    . split <;> simp [Form.new_var]

  lemma generalize_constants_rev {φ : Form} {x : SVAR} (i : NOM) (h : x ≥ φ.new_var) : ⊢ (all x, φ[x // i]) → ⊢ φ := by
    intro pf
    have l1 := ax_q2_nom (φ[x//i]) x i
    have l2 := mp l1 pf
    rw [@svar_svar_nom_subst φ i i x h, nom_subst_self] at l2
    exact l2

  theorem generalize_constants_iff {φ : Form} {x : SVAR} (i : NOM) (h : x ≥ φ.new_var) : ⊢ φ ↔ ⊢ (all x, φ[x // i]) := by
    apply Iff.intro
    . apply generalize_constants; assumption
    . apply generalize_constants_rev; assumption

  theorem rename_constants (j i : NOM) (h : nom_occurs j φ = false) : ⊢ φ ↔ ⊢ (φ[j // i]) := by
    apply Iff.intro
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

  def double''' : Form → Form := λ φ =>
    loop φ φ.new_nom.letter
  where
    loop : Form → Nat → Form
    | φ, 0   =>  φ
    | φ, n+1 =>  φ[({letter := φ.new_nom.letter + (1-φ.new_nom.letter%2) + 2} : NOM) // ({letter := n} : NOM)]

  theorem pf_double''' : ⊢ φ ↔ ⊢ (double''' φ) := by
    simp [double''']
    cases φ.new_nom.letter with
    | zero =>
        simp [double'''.loop]
    | succ m =>
        simp [double'''.loop]
        have : nom_occurs { letter := φ.new_nom.letter + (1-φ.new_nom.letter%2) + 2 } φ = false := by
          apply ge_new_nom_is_new
          simp [NOM.le]
          exact Nat.le_add_right (Form.new_nom φ).letter ((1 - (Form.new_nom φ).letter % 2) + 2)
        have := rename_constants { letter := φ.new_nom.letter + (1-φ.new_nom.letter%2) + 2 } { letter := m } this
        exact this

  theorem bulk_rename (φ : Form) (new : List NOM) (old : List NOM) (hdup : new.Nodup) (hnocc : ∀ i : NOM, i ∈ new → nom_occurs i φ = false) : ⊢ φ ↔ ⊢ (φ.bulk_subst new old) := by
    induction new generalizing φ old with
    | nil => cases old <;> simp [Form.bulk_subst]
    | cons h₁ t₁ ih =>
        simp at hdup
        cases old with
        | nil => simp [Form.bulk_subst]
        | cons h₂ t₂ =>
          simp [Form.bulk_subst]
          have : ∀ (i : NOM), i ∈ t₁ → nom_occurs i (φ[h₁//h₂]) = false := sorry
          have ih := ih (φ[h₁ // h₂]) t₂ hdup.left this
          have : nom_occurs h₁ φ = false := sorry
          have := rename_constants h₁ h₂ this
          rw [Iff.iff this]
          exact Iff.comm.mp ih

/-
  theorem pf_double'' : ⊢φ ↔ ⊢ φ.double' := by
    rw [Form.double']
    induction φ with
    | bttm => simp [Form.new_nom, Form.double_n]
    | prop _ => simp [Form.new_nom, Form.double_n]
    | svar _ => simp [Form.new_nom, Form.double_n]
    | nom i  => admit
    | impl ψ χ ih1 ih2 =>
        let v := max ψ.new_nom χ.new_nom
        have : max ψ.new_nom χ.new_nom = v := by simp
        simp [Form.new_nom, this]
        cases v.letter
        . simp [Form.double_n]
        . simp [Form.double_n, nom_subst_nom]
          admit
    | bind x ψ ih   =>
        simp [Form.new_nom]
        admit
    | box ψ  ih   =>
        simp [Form.new_nom]
        admit

  theorem pf_double' : ⊢φ ↔ ⊢ φ.double' := by
    rw [Form.double']
    let c := φ.new_nom.letter
    have test : φ.new_nom.letter = c := by simp
    rw [test]
    revert test
    induction c generalizing φ with
    | zero      => intros; rw [Form.double_n]
    | succ n ih =>
        intro test
        cases hocc : nom_occurs ⟨n-1⟩ φ
        . admit
        . let x := φ.new_var
          let ψ := all x, φ[x // ({ letter := n } : NOM)]
          have note : (all x, φ[x // ({ letter := n } : NOM)]) = ψ := by simp
          have cond1 : x ≥ φ.new_var := sorry
          have cond2 : ψ.new_nom.letter = n := sorry
          have l1 := generalize_constants_iff ⟨n⟩ cond1
          have l2 := ih cond2
          rw [note] at l1
          admit
        /-
        have : n+1 = φ.new_nom.letter := by simp [test]
        rw [Form.double_n, this]
        have : nom_occurs ⟨2*φ.new_nom.letter⟩ φ = false := sorry
        have iff1 := rename_constants ⟨2*φ.new_nom.letter⟩ φ.new_nom this
        let ψ := φ[({ letter := 2 * (Form.new_nom φ).letter } : NOM)//Form.new_nom φ]
        have notate : ψ = φ[({ letter := 2 * (Form.new_nom φ).letter } : NOM)//Form.new_nom φ] := by simp
        rw [←notate] at iff1 ⊢
        let x := ψ.new_var
        have : x ≥ ψ.new_var := by admit
        have iff2 := generalize_constants_iff ⟨2*φ.new_nom.letter⟩ this
        let χ := ψ[x // ({ letter := 2 * (Form.new_nom φ).letter } : NOM)]
        have notate2 : χ = ψ[x // ({ letter := 2 * (Form.new_nom φ).letter } : NOM)] := by simp
        rw [←notate2] at iff2
        let y := χ.new_var
        have : x ≥ χ.new_var := by admit
        have iff3 := generalize_constants_iff ⟨φ.new_nom.letter⟩ this

        -- eq_new_var
        -/
/-
  lemma double_theorem : ⊢ φ ↔ ⊢ φ.double := by
    rw [Form.double]
    induction φ.nominals with
    | nil   =>
        simp [Form.double_list]
    | cons h t ih =>
        simp only [Form.double_list]
        conv at ih => rhs; rw [rename_constants (NOM.mk (h.letter*2)) h]
        admit

  lemma double_deduction : Γ ⊢ φ ↔ Γ.double ⊢ φ.double := by
    simp only [SyntacticConsequence]
    admit
  
  lemma double_consistent {Γ : Set Form} : Γ.consistent ↔ Γ.double.consistent := by
    simp only [Set.consistent]
    apply Iff.intro <;> rw [←contraposition] <;> admit
-/
-/
end Nominals

  def Form.double''  : Form → Form   := λ φ =>
    loop φ.new_nom.letter φ
  where
    loop : ℕ → Form → Form
    | 0, φ      => φ
    | n+1, φ    => loop n (nom_subst_nom φ ⟨2*n⟩ ⟨n⟩)
  
  def Form.double'''  : Form → Form   := λ φ =>
    loop φ.new_nom.letter φ
  where
    loop : ℕ → Form → Form
    | 0, φ      => φ
    | n+1, φ    => subst_nom (loop n (nom_subst_svar φ φ.new_var ⟨n⟩)) ⟨2*n⟩ φ.new_var

  #eval Form.double''' (NOM.mk 1 ⋁ NOM.mk 3)


  /-
  ih:
  (loop n (φ[x//n]) ) [2*n//x] =
  (loop n (φ[2*n//n]) )
  -/

  /-
  (loop n (φ [x//n+1] [2*n//n]) ) [2*(n+1)//x] =
   loop n (φ [2*(n+1)//n+1] [2*n//n] )
  -/

  def pf_double_prop : Form → Prop   := λ φ  =>
    loop? φ.new_nom.letter φ
  where
    loop? : ℕ → Form → Prop
    | 0, φ      => (⊢ φ)
    | n+1, φ    => (loop? n φ) → (loop? n (nom_subst_nom φ ⟨2*n⟩ ⟨n⟩))
  

  lemma ge_new_nom_is_new' : ∀ x : NOM, x ≥ φ.new_nom → nom_occurs x φ = false := sorry

  def property (l₁ l₂ : List NOM) : Prop := True

  #check List.take
  #check List.get

  theorem proof_sketch (h : property l₁ l₂) : ⊢ φ ↔ ⊢ (φ.bulk_subst l₁ l₂) := by
    induction l₁ generalizing φ l₂ with
    | nil => cases l₂ <;> simp [Form.bulk_subst]
    | cons h_new t_new ih =>
        cases l₂ with
        | nil => simp [Form.bulk_subst]
        | cons h_old t_old =>
            simp [Form.bulk_subst]
            have : nom_occurs h_new φ = false := by admit
            have := rename_constants h_new h_old this
            rw [this]
            apply ih
            admit

  theorem lasttry : ⊢ φ ↔ ⊢ φ.dbl := by
    simp [Form.dbl]
    apply proof_sketch
    admit