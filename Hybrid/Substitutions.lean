import Hybrid.Form

theorem subst_depth {i : NOM N} {x : SVAR} {φ : Form N} : φ[i // x].depth = φ.depth := by
  induction φ <;> simp [subst_nom, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth' {x y : SVAR} {φ : Form N} : φ[y // x].depth = φ.depth := by
  induction φ <;> simp [subst_svar, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth'' {x : SVAR} {i : NOM N} {φ : Form N} : (φ[i//x]).depth < (ex x, φ).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply ex_depth

theorem iff_subst_svar {y x : SVAR} : (φ ⟷ ψ)[y // x] = (φ[y//x] ⟷ ψ[y//x]) := by
  simp [subst_svar]

section Variables
  lemma svar_eq {ψ χ : SVAR} : ψ = χ ↔ ψ.1 = χ.1 := by
    have l1 : ψ = ⟨ψ.letter⟩ := by simp
    have l2 : χ = ⟨χ.letter⟩ := by simp
    rw [l1, l2]
    simp

  lemma new_var_neg : (∼ψ).new_var = ψ.new_var := by
    simp [Form.new_var, max, -implication_disjunction]
    rw [←svar_eq]
    intro _
    simp [*]
  
  lemma subst_neg : is_substable (∼ψ) y x ↔ is_substable ψ y x := by
    simp [is_substable]

  lemma new_var_gt      : occurs x φ → x < φ.new_var   := by
    induction φ with
    | svar y          =>
        simp [occurs, Form.new_var, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self y.letter
    | impl ψ χ ih1 ih2 =>
        simp only [occurs, Form.new_var, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box ψ ih      =>
        simp only [occurs, Form.new_var]
        assumption
    | bind y ψ ih   =>
        simp only [occurs, Form.new_var, max]
        intro h
        have ih := ih h
        by_cases hc : (y + 1).letter > (Form.new_var ψ).letter
        . simp [hc]
          simp at hc
          exact Nat.lt_trans ih hc
        . simp [hc]
          assumption
    | _ => simp [occurs]

  lemma new_var_is_new  : occurs (φ.new_var) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_var_gt h
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a
  
  lemma ge_new_var_is_new (h : x ≥ φ.new_var) : occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_var_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a
  
  lemma ge_new_var_subst_nom {i : NOM N} {y : SVAR} : φ.new_var ≥ φ[i // y].new_var := by
    induction φ <;> simp [Form.new_var, subst_nom, *] at *
    . split <;> simp [Form.new_var, SVAR.le]
    . simp [max]; split <;> split <;> simp [SVAR.le, *] at *; apply Nat.le_trans <;> assumption; apply Nat.le_of_lt; apply Nat.lt_of_le_of_lt <;> assumption
    . simp [max] at *; split <;> split <;> simp [Form.new_var, SVAR.le, SVAR.add, max] at * <;> split <;> simp [SVAR.le, SVAR.add, *] at *;
                       apply Nat.le_of_lt; apply Nat.lt_of_le_of_lt <;> assumption

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

lemma new_var_geq3 : x ≥ (□ φ).new_var → (x ≥ φ.new_var) := by simp [Form.new_var]

lemma new_var_subst {φ : Form N} {i : NOM N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable (φ[y//i]) x y := by
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

lemma scz {φ : Form N} (i : NOM N) (h : x ≥ φ.new_var) (hy : y ≠ x) : (is_free y φ) ↔ (is_free y (φ[x // i])) := by
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

lemma nom_subst_trans (i : NOM N) (x y : SVAR) (h : y ≥ φ.new_var) : φ[y // i][x // y] = φ[x // i] := by
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

  lemma ge_new_var_subst_helpr {i : NOM N} {x : SVAR} (h : y ≥ Form.new_var (χ⟶ψ)) : y ≥ Form.new_var (χ⟶ψ[i//x]⟶⊥) := by
    simp [Form.new_var, max]
    split <;> split
    . exact (new_var_geq1 h).left
    . apply Nat.le_trans
      apply ge_new_var_subst_nom
      exact (new_var_geq1 h).right
    . exact (new_var_geq1 h).left
    . simp [SVAR.le]

  lemma notfreeset {Γ : Set (Form N)} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ.1 = false) : is_free x (conjunction Γ L) = false := by
    induction L with
    | nil         =>
        simp only [conjunction, is_free]
    | cons h t ih =>
        simp only [is_free, Bool.or_false, Bool.or_eq_false_eq_eq_false_and_eq_false]
        apply And.intro
        . exact hyp h
        . exact ih

  lemma notfree_after_subst {φ : Form N} {x y : SVAR} (h : x ≠ y) : is_free x (φ[y // x]) = false := by
    induction φ with
    | svar z   =>
        by_cases xz : x = z
        . simp [subst_svar, if_pos xz, is_free, h]
        . simp [subst_svar, if_neg xz, is_free, xz]
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, is_free, ih1, ih2]
    | box _ ih    =>
        simp [subst_svar, is_free, ih]
    | bind z _ ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, is_free]
        . simp [subst_svar, if_neg xz, is_free, ih]
    | _        => simp only [is_free]

  lemma notocc_beforeafter_subst {φ : Form N} {x y : SVAR} (h : occurs x φ = false) : occurs x (φ[y // x]) = false := by
    induction φ with
    | svar z   =>
        by_cases xz : x = z
        <;> simp [subst_svar, if_pos xz, xz, occurs, h] at *
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, occurs, not_or, ih1, ih2, -implication_disjunction] at *
        exact ⟨ih1 h.left, ih2 h.right⟩ 
    | box _ ih    =>
        simp [subst_svar, occurs, ih, -implication_disjunction] at *
        exact ih h
    | bind z ψ ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, occurs] at *
          exact h
        . simp [subst_svar, if_neg xz, occurs, ih, xz, h, -implication_disjunction] at *
          exact ih h
    | _        => simp only [occurs]

  lemma notoccursbind : occurs x φ = false → occurs x (all v, φ) = false := by
    simp [occurs]

  lemma notoccurs_notfree : (occurs x φ = false) → (is_free x φ = false) := by
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

  lemma preserve_notfree {φ : Form N} (x v : SVAR) : (is_free x φ = false) → (is_free x (all v, φ) = false) := by
    intro h
    simp only [is_free, h, Bool.and_false]

  lemma subst_notfree_var {φ : Form N} {x y : SVAR} (h : is_free x φ = false) : (φ[y // x] = φ) ∧ (occurs x φ = false → is_substable φ y x) := by
    induction φ with
    | svar z =>
        by_cases heq : x = z
        . simp only [is_free, heq, beq_self_eq_true] at h 
        . simp only [subst_svar, heq, ite_false, occurs, is_substable]
    | impl ψ χ ih1 ih2 =>
        simp only [is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h 
        apply And.intro
        . simp [subst_svar, h, ih1, ih2]
        . intro nocc
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at nocc 
          simp [is_substable, h, nocc, ih1, ih2]
    | box ψ ih  =>
        rw [is_free] at h
        apply And.intro
        . simp [subst_svar, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, ih, nocc, h]
    | bind z ψ ih =>
        apply And.intro
        . by_cases heq : x = z
          . rw [←heq, subst_svar, if_pos (Eq.refl x)]
          . simp only [is_free, bne, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false', beq_iff_eq,
            Ne.symm heq, false_or] at h 
            simp [subst_svar, heq, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, notoccurs_notfree, nocc]
    | _   =>
        simp [subst_svar, is_substable]

    lemma rereplacement (φ : Form N) (x y : SVAR) (h1 : occurs y φ = false) (h2 : is_substable φ y x) : (is_substable (φ[y // x]) x y) ∧ φ[y // x][x // y] = φ := by
      induction φ with
      | svar z =>
          simp [occurs] at h1
          by_cases xz : x = z
          repeat simp [subst_svar, xz, h1, is_substable]
      | impl ψ χ ih1 ih2 =>
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1 
          simp only [is_substable, Bool.and_eq_true] at h2
          simp [subst_svar, ih1, ih2, h1, h2, is_substable]
      | box ψ ih =>
          simp only [occurs] at h1
          simp only [is_substable] at h2
          simp [subst_svar, ih, h1, h2, is_substable]
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
              simp [subst_svar, xz, yz]
              by_cases xfree : is_free x ψ
              . simp [is_substable, xfree, Ne.symm yz, bne] at h2
                simp [ih, h1, h2, is_substable, bne, Ne.symm xz]
              . rw [show (¬is_free x ψ = true ↔ is_free x ψ = false) by simp] at xfree
                simp [subst_notfree_var, xfree, is_substable, (notoccurs_notfree h1)]
      | _     =>
          apply And.intro
          repeat rfl
  
  lemma subst_self_is_self (φ : Form N) (x : SVAR) : φ [x // x] = φ := by
    induction φ with
    | svar y   =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy, xy]
        . rw [subst_svar, if_neg xy]
    | impl φ ψ ih1 ih2 =>
        rw [subst_svar, ih1, ih2]
    | box  φ ih  =>
        rw [subst_svar, ih]
    | bind y φ ih =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy]
        . rw [subst_svar, if_neg xy, ih]
    | _        => rfl

  lemma pos_subst {m : ℕ} {i : NOM N} {v : SVAR} : (iterate_pos m (v⋀φ))[i//v] = iterate_pos m (i⋀φ[i//v]) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop, subst_nom]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop, subst_nom] at ih ⊢
        rw [ih]

  lemma nec_subst {m : ℕ} {i : NOM N} {v : SVAR} : (iterate_nec m (v⟶φ))[i//v] = iterate_nec m (i⟶φ[i//v]) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop, subst_nom]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop, subst_nom] at ih ⊢
        rw [ih]

  theorem Form.new_var_properties (φ : Form N) : ∃ x : SVAR, x ≥ φ.new_var ∧ occurs x φ = false ∧ (∀ y : SVAR, is_substable φ x y) := by
    exists φ.new_var
    simp [SVAR.le, new_var_is_new]
    intro
    apply new_var_subst''
    simp [SVAR.le]
end Variables

section Nominals
  lemma nom_svar_subst_symm {v x y : SVAR} {i : NOM N} (h : y ≠ x) : φ[x//i][v//y] = φ[v//y][x//i] := by
    induction φ <;> simp [subst_svar, nom_subst_svar, *] at *
    . split <;> simp[nom_subst_svar]
    . split <;> simp [subst_svar, h]
    . split <;> simp [nom_subst_svar]

  lemma nom_nom_subst_symm {x y : SVAR} {j i : NOM N} (h1 : j ≠ i) (h2 : y ≠ x) : φ[x//i][j//y] = φ[j//y][x//i] := by
    induction φ <;> simp [nom_subst_svar, subst_nom, *] at *
    . split <;> simp [nom_subst_svar, *]
    . split <;> simp [subst_nom, *]
    . split <;> simp [nom_subst_svar]

  lemma subst_collect_all {x y : SVAR} {i : NOM N} : φ[i//y][x//i] = φ[x//i][x//y] := by
    induction φ <;> simp [subst_svar, subst_nom, nom_subst_svar, *] at *
    . split <;> simp [nom_subst_svar]
    . split <;> simp [subst_svar]
    . split <;> simp [nom_subst_svar, *]

  theorem nom_subst_nocc (h : nom_occurs i χ = false) (y : SVAR) : χ[y // i] = χ := by
    induction χ <;> simp [nom_occurs, nom_subst_svar, *, -implication_disjunction] at *
    . intro; apply h; apply Eq.symm; assumption
    . simp [h] at *
      apply And.intro <;> assumption
    . simp [h] at *; assumption
    . simp [h] at *; assumption

  theorem subst_collect_all_nocc (h : nom_occurs i χ = false) (x y : SVAR) : χ[i // x][y // i] = χ[y // x] := by
    rw [subst_collect_all, nom_subst_nocc h y]

  lemma nom_svar_rereplacement {φ : Form N} {i : NOM N} (h : x ≥ φ.new_var) : φ[x // i][i // x] = φ := by
    induction φ <;> simp [nom_subst_svar, subst_nom] 
    . have := ge_new_var_is_new h
      simp [occurs] at this
      exact this
    . split <;> simp [subst_nom, *]
    . simp [new_var_geq1 h, *]
    . simp [new_var_geq3 h, *]
    . split
      . next h2 =>
          have l1 := (new_var_geq2 h).left
          rw [←h2] at l1
          have l2 := Nat.le_succ x
          have := Nat.le_antisymm l1 l2
          simp [SVAR.add] at this
      . simp [new_var_geq2 h, *]

  lemma pos_subst_nom {m : ℕ} {i : NOM N} {v x : SVAR} : (iterate_pos m (v⋀φ))[x//i] = iterate_pos m (Form.svar v⋀φ[x//i]) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop, nom_subst_svar]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop, nom_subst_svar] at ih ⊢
        rw [ih]

  lemma nec_subst_nom {m : ℕ} {i : NOM N} {v x : SVAR} : (iterate_nec m (v⟶φ))[x//i] = iterate_nec m (Form.svar v⟶φ[x//i]) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop, nom_subst_svar]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop, nom_subst_svar] at ih ⊢
        rw [ih]

  lemma diffsvar {v x : SVAR} (h : x ≥ v+1) : v ≠ x := by
    simp; intro abs; exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self v.letter) h)) (SVAR.mk.inj abs)  

  section New_NOM
  lemma new_nom_gt      : nom_occurs i φ → i.letter < φ.new_nom.letter   := by
    induction φ with
    | nom i          =>
        simp [nom_occurs, Form.new_nom, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self i.letter
    | impl ψ χ ih1 ih2 =>
        simp only [nom_occurs, Form.new_nom, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box      =>
        assumption
    | bind     =>
        assumption
    | _ => simp [nom_occurs]

  lemma new_nom_is_nom  : nom_occurs (φ.new_nom) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_nom_gt h
    have b := Nat.lt_irrefl φ.new_nom.letter
    exact b a
  
  lemma ge_new_nom_is_new (h : x ≥ φ.new_nom) : nom_occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_nom_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_nom.letter
    exact b a
  end New_NOM

-- just remove this definition, it is completely redundant...
  def descending (l : List (NOM N)) : Prop :=
    match l with
    | []        =>    True
    | h :: t    =>    (∀ i ∈ t, h > i) ∧ descending t

  def descending' (l : List (NOM N)) : Prop := l.Chain' GT.gt

  theorem eq_len {φ : Form TotalSet} : φ.list_noms.length = φ.odd_list_noms.length := by simp [Form.odd_list_noms]

  theorem odd_is_odd {φ : Form TotalSet} (h1 : n < φ.list_noms.length) (h2 : n < φ.odd_list_noms.length) : φ.odd_list_noms.get ⟨n, h2⟩ = 2 * φ.list_noms.get ⟨n, h1⟩ + 1 := by
    simp [Form.odd_list_noms, Form.list_noms]

  theorem descending_equiv (l : List (NOM N)) : descending l ↔ descending' l := by
    induction l with
    | nil         =>  simp [descending, descending']
    | cons h t ih =>
        simp [descending, descending', List.Chain', List.chain_iff_pairwise, -implication_disjunction]
        intros
        simp [descending', List.chain'_iff_pairwise] at ih
        exact ih

  theorem descending_property (desc : descending l) (h0 : pos < l.length) (h1 : i ∈ l) (h2 : i > l[pos]) : i ∈ l.take pos := by
    match l with
    | []     => simp at h1
    | h :: t =>
        simp at h0 h1
        cases pos with
        | zero =>
            simp at h2 ⊢
            apply Or.elim h1
            . intro eq
              rw [eq] at h2
              apply Nat.lt_irrefl h.letter
              assumption
            . intro i_mem_t
              apply Nat.lt_asymm h2
              exact (desc.left i i_mem_t)
        | succ pos =>
            apply Or.elim h1
            . intro i_h
              simp [i_h]
            . intro h1_new
              simp
              apply Or.inr
              have desc_new := desc.right
              have h0_new : pos < t.length := by apply Nat.lt_of_succ_lt_succ; assumption
              have h2_new : i > t[pos] := by simp at h2 ⊢; simp [h2]
              exact descending_property desc_new h0_new h1_new h2_new

  theorem descending_ndup (desc : descending l) (h0 : pos < l.length) (h1 : i = l[pos]) : ¬i ∈ l.take pos := by
    match l with
    | []      => simp
    | h :: t  =>
        let fin_pos : Fin (h::t).length := ⟨pos, h0⟩
        simp only [descending_equiv, descending', List.chain'_iff_pairwise, List.pairwise_iff_get] at desc

        intro habs
        have ⟨n, is_i⟩ := List.mem_iff_get.mp habs
        have n_lt := n.2
        simp only [List.length_take, ge_iff_le, lt_min_iff] at n_lt
        rw [List.get_take' (h :: t)] at is_i

        have : ⟨↑n, n_lt.right⟩ < fin_pos := by simp [n_lt.left]
        have := desc ⟨↑n, n_lt.right⟩ fin_pos this
        rw [is_i, h1] at this
        apply Nat.lt_irrefl (h :: t)[pos].letter
        assumption

  theorem descending_list_noms {φ : Form TotalSet} : descending φ.list_noms := by
    rw [descending_equiv, descending']
    exact list_noms_chain'
  
  theorem descending_odd_list_noms {φ : Form TotalSet} : descending φ.odd_list_noms := by
    have dln := @descending_list_noms φ
    have : ∀ a b : NOM TotalSet, (2 * b + 1 < 2 * a + 1) ↔ (b < a) := by simp [NOM.lt, NOM.add, NOM.hmul]
    have := @List.Pairwise.iff (NOM TotalSet) (fun a b => 2 * b + 1 < 2 * a + 1) (fun a b => b < a) this
    simp only [Form.odd_list_noms, descending_equiv, descending', List.chain'_iff_pairwise, List.pairwise_map, GT.gt, this] at dln ⊢
    assumption

  theorem occurs_list_noms : nom_occurs i φ ↔ i ∈ φ.list_noms := by
    induction φ with
    | impl φ ψ ih1 ih2 =>
        simp [Form.list_noms, nom_occurs, ih1, ih2]
        rw [←List.mem_append]
        have is_perm := List.perm_merge GE.ge (Form.list_noms φ) (Form.list_noms ψ)
        simp only [List.Perm.mem_iff is_perm]
    | box _ ih    => exact ih
    | bind _ _ ih => exact ih
    | _        => simp [Form.list_noms, nom_occurs]

  theorem list_noms_subst {old new : NOM N} : i ∈ (φ[new // old]).list_noms → ((i ∈ φ.list_noms ∧ i ≠ old) ∨ i = new) := by
    rw [←occurs_list_noms, ←occurs_list_noms]
    intro h
    induction φ with
    | nom j =>
        simp [nom_subst_nom] at h
        split at h
        . simp [nom_occurs] at h; apply Or.inr; assumption
        . apply Or.inl
          apply And.intro
          . assumption
          . simp [nom_occurs] at h
            rw [h]
            assumption
    | impl ψ χ ih1 ih2 =>
        simp [nom_occurs] at h ⊢
        apply Or.elim h
        . intro hyp
          apply Or.elim (ih1 hyp)
          . intro hl
            simp [hl]
          . intro hr
            simp [hr]
        . intro hyp
          apply Or.elim (ih2 hyp)
          . intro hl
            simp [hl]
          . intro hr
            simp [hr]
    | box ψ ih =>
        simp [nom_occurs] at h
        exact ih h
    | bind _ ψ ih =>
        simp [nom_occurs] at h
        exact ih h
    | _     => simp [nom_occurs] at h

  theorem occ_bulk {l_new l_old : List (NOM N)} {φ : Form N} (eq_len : l_new.length = l_old.length) : nom_occurs i (φ.bulk_subst l_new l_old) → ((i ∈ φ.list_noms ∧ i ∉ l_old) ∨ i ∈ l_new) := by
    intro h
    induction l_new generalizing φ l_old with
    | nil => cases l_old <;> simp [Form.bulk_subst] at *; repeat exact occurs_list_noms.mp h
    | cons h_new t_new ih =>
        cases l_old with
        | nil =>
            simp [Form.bulk_subst] at h ⊢
            apply Or.inl
            exact occurs_list_noms.mp h
        | cons h_old t_old =>
            simp [Form.bulk_subst] at eq_len h ⊢
            have := ih eq_len h
            apply Or.elim this
            . intro hyp
              clear this ih
              cases t_new
              . have := List.length_eq_zero.mp (Eq.symm (Eq.subst eq_len (@List.length_nil (NOM N))))
                simp [this, Form.bulk_subst] at h ⊢
                apply Or.elim (list_noms_subst (occurs_list_noms.mp h))
                . intro c1
                  simp [c1]
                . intro c2
                  exact Or.inr c2
              . cases t_old
                . simp at eq_len
                . simp [Form.bulk_subst] at hyp ⊢
                  have ⟨a, b⟩ := hyp
                  apply Or.elim (list_noms_subst b)
                  . intro c1
                    apply Or.inl
                    simp [c1, a]
                  . intro c2
                    simp [c2]
            . intro hyp
              clear this ih
              apply Or.inr
              apply Or.inr
              assumption

  theorem nocc_bulk {l_new l_old : List (NOM N)} {φ : Form N} (eq_len : l_new.length = l_old.length) : ((i ∉ φ.list_noms ∨ i ∈ l_old) ∧ i ∉ l_new) → nom_occurs i (φ.bulk_subst l_new l_old) = false := by
    rw [contraposition]
    simp [-implication_disjunction]
    intro h1 h2
    apply Or.elim (occ_bulk eq_len h1)
    . simp
    . simp [h2]

  theorem has_nocc_bulk_property : ∀ φ : Form TotalSet, nocc_bulk_property φ.odd_list_noms φ.list_noms φ := by
    unfold nocc_bulk_property
    intro φ n i h
    match n with
    | ⟨pos, lt_pos⟩ =>
        apply And.intro
        . by_cases c : i ∈ φ.list_noms
          . apply Or.inr
            simp only
            -- by h, we know that i > φ.list_noms[pos]
            have lt_pos_2 := (Eq.subst (Eq.symm eq_len) lt_pos)
            have : φ.list_noms[pos].letter < i.letter := by
                simp [odd_is_odd lt_pos_2 lt_pos, h, NOM.lt, NOM.add, NOM.hmul]
                apply Nat.lt_of_le_of_lt
                apply @Nat.le_mul_of_pos_left φ.list_noms[pos].letter 2
                simp
                simp [Nat.mul_comm]
            -- since φ.list_noms is in descending order
            --  and i ∈ φ.list_noms by assumption,
            -- then i ∈ φ.list_noms[:pos]
            apply descending_property
            apply descending_list_noms
            repeat assumption
          . exact Or.inl c
        . simp
          apply descending_ndup
          apply descending_odd_list_noms
          assumption
  
    theorem nocc_bulk_property_induction : nocc_bulk_property (h_new :: t_new) (h_old :: t_old) φ → nocc_bulk_property t_new t_old (φ[h_new//h_old]) := by
      unfold nocc_bulk_property
      intro h n i eq_i
      let m : Fin (List.length (h_new :: t_new)) := ⟨n.val+1, Nat.succ_lt_succ_iff.mpr n.2⟩
      have m_n : m.val = n.val + 1 := by simp
      have : i = (h_new :: t_new)[m] := by simp [eq_i]
      have ⟨l, r⟩ := h this
      apply And.intro
      . simp [m_n, ←or_assoc] at l
        apply Or.elim l
        . intro disj
          apply Or.inl
          apply not_imp_not.mpr (@list_noms_subst TotalSet i φ h_old h_new)
          simp
          apply And.intro
          . intro habs
            have l2 : h_new ∈ List.take (↑m) (h_new :: t_new) := by simp
            rw [←habs] at r l2
            contradiction
          . rw [Or.comm]; exact disj
        . intro
          apply Or.inr
          assumption
      . simp [m_n] at r
        exact r.right

end Nominals

  lemma dbl_subst_nom {j : NOM N} {x : SVAR} (i : NOM N) (h : nom_occurs j φ = false) : φ[j//i][x//j] = φ[x//i] := by
    induction φ <;> simp [nom_occurs, nom_subst_nom, nom_subst_svar, -implication_disjunction, *] at *
    . split <;> simp [nom_subst_svar, Ne.symm h]
    repeat simp [h, *] at *

  lemma svar_svar_nom_subst {i j : NOM N} {x : SVAR} (h : x ≥ φ.new_var) : φ[x//i][j//x] = φ[j//i] := by
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
  
  lemma nom_subst_self {i : NOM N} : φ[i // i] = φ := by
    induction φ <;> simp [nom_subst_nom, -implication_disjunction, *] at * 
    . intro h ; apply Eq.symm; assumption

  lemma eq_new_var {i j : NOM N} : φ.new_var = (φ[i // j]).new_var := by
    induction φ <;> simp [Form.new_var, nom_subst_nom, *] at * 
    . split <;> simp [Form.new_var]



  theorem odd_nom {i : NOM TotalSet} : (Form.nom i).odd_noms = Form.nom (2 * i + 1) := by
    simp [Form.odd_noms, Form.odd_list_noms, Form.list_noms, Form.bulk_subst, nom_subst_nom, NOM_eq, NOM.hmul, NOM.add, Nat.mul_comm]

  theorem bulk_subst_impl {φ ψ : Form TotalSet} : (φ ⟶ ψ).bulk_subst l₁ l₂ = φ.bulk_subst l₁ l₂ ⟶ ψ.bulk_subst l₁ l₂ := by
    admit

  theorem list_noms_impl_r {φ ψ : Form TotalSet} : φ.bulk_subst φ.odd_list_noms φ.list_noms = φ.bulk_subst (φ ⟶ ψ).odd_list_noms (φ ⟶ ψ).list_noms := by
    admit

  theorem list_noms_impl_l {φ ψ : Form TotalSet} : φ.bulk_subst φ.odd_list_noms φ.list_noms = φ.bulk_subst (ψ ⟶ φ).odd_list_noms (ψ ⟶ φ).list_noms := by
    admit

  theorem odd_impl : (φ ⟶ ψ).odd_noms = φ.odd_noms ⟶ ψ.odd_noms := by
    unfold Form.odd_noms
    conv => rhs; rw [@list_noms_impl_r φ ψ, @list_noms_impl_l ψ φ]
    simp [bulk_subst_impl]

  theorem odd_box : (□φ).odd_noms = □(φ.odd_noms) := by admit

  theorem odd_bind : (all x, φ).odd_noms = all x, (φ.odd_noms) := by admit

  def List.to_odd {Γ : Set (Form TotalSet)} {L : List Γ} : List Γ.odd_noms := sorry

  def List.odd_to {Γ : Set (Form TotalSet)} {L : List Γ.odd_noms} : List Γ := sorry

  theorem odd_conj (Γ : Set (Form TotalSet)) (L : List Γ) : (conjunction Γ L).odd_noms = conjunction Γ.odd_noms L.to_odd := by
    admit

  theorem odd_conj_rev (Γ : Set (Form TotalSet)) (L' : List Γ.odd_noms) : (conjunction Γ L'.odd_to).odd_noms = conjunction Γ.odd_noms L' := by
    admit