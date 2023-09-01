import Hybrid.Substitutions
import Hybrid.Proof
import Hybrid.Truth
import Hybrid.Util
open Classical

section Lemmas

  theorem generalize_not_free (h1 : is_free v φ = false) : ⊨ (φ ⟷ (all v, φ)) := by
    intro M s g
    rw [iff_sat]
    apply Iff.intro
    . intro h2
      induction φ generalizing s g with
      | bttm   => exact False.elim h2
      | prop p =>
          simp at h2
          rw [Sat]
          intros
          exact h2
      | svar x =>
          simp only [is_free, beq_eq_false_iff_ne, ne_eq] at h1 
          intro _ var
          exact Eq.trans h2 (Eq.symm (var x h1))
      | nom _ =>
          intro _ _
          exact h2
      | impl ψ χ ih1 ih2 =>
          simp only [Sat, is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1 h2 ⊢
          intros g' var h
          exact ih2 h1.right s g (h2 (ih1 h1.left s g' h g (is_variant_symm.mp var))) g' var
      | box ψ ih    =>
          rw [is_free] at h1
          intros g' var s' is_neigh
          exact ih h1 s' g (h2 s' is_neigh) g' var
      | bind u ψ ih =>
          simp only [is_free, Bool.and_eq_false_eq_eq_false_or_eq_false] at h1  
          apply Or.elim h1
          . intro u_is_v
            simp only [bne, Bool.not_eq_false', beq_iff_eq] at u_is_v 
            rw [u_is_v] at h2 ⊢
            intros g' variant1 g'' variant2
            have variant3 := is_variant_trans variant2 variant1
            exact h2 g'' variant3
          . intro nfree_in_ψ
            rw [bind_comm]
            intros g' variant_u
            exact ih nfree_in_ψ s g' (h2 g' variant_u)
    . intro h
      exact h g (is_variant_refl v)

  theorem svar_substitution {φ : Form N} {g g' : I M.W} (h_subst : is_substable φ y x) (h_var : is_variant g g' x) (h_which_var : g' x = g y) :
  (((M,s,g) ⊨ φ[y // x]) ↔ (M,s,g') ⊨ φ) := by
    induction φ generalizing s g g' with
    | svar z   =>
        by_cases z_x : z = x
        . rw [show z[y//x] = y by rw[z_x, subst_svar, if_pos (Eq.refl x)], Sat, z_x, Sat, h_which_var]
        . rw [show z[y//x] = z by rw[subst_svar, if_neg (Ne.symm (Ne.intro z_x))], Sat, Sat, ←(h_var z (Ne.symm z_x))]
    | impl ψ χ ind_hyp_1 ind_hyp_2 =>
        simp only [is_substable, Bool.and_eq_true] at h_subst 
        have by_ind_hyp_1 := (@ind_hyp_1 s g) h_subst.left h_var h_which_var
        have by_ind_hyp_2 := (@ind_hyp_2 s g) h_subst.right h_var h_which_var
        rw [subst_svar, Sat, Sat, by_ind_hyp_1, by_ind_hyp_2]
    | box  ψ ind_hyp               =>
        apply Iff.intro <;>
        . intro h1 s' s_R_s'
          have by_ind_hyp := (@ind_hyp s' g) h_subst h_var h_which_var
          first | exact by_ind_hyp.mp (h1 s' s_R_s') | exact by_ind_hyp.mpr (h1 s' s_R_s')
    | bind v ψ ind_hyp =>
        cases x_free : is_free x ψ with
        | true =>
            by_cases x_v : x = v
            . -- all x, ψ             and       x is free in ψ
              simp only [subst_svar, x_v, ite_true]
              rw [←x_v]
              have := @generalize_not_free x N (all x, ψ) (by simp [is_free])
              apply Iff.intro
              . intro h
                have := this M s g
                rw [iff_sat] at this
                exact this.mp h g' (is_variant_symm.mp h_var)
              . intro h
                have := this M s g'
                rw [iff_sat] at this
                exact this.mp h g h_var
            . by_cases y_v : y = v
              . -- all y, ψ          and       x is free in ψ
                -- contradiction with h_subst:
                simp only [is_substable, x_free, beq_iff_eq, y_v,
                  bne_self_eq_false, Bool.false_and, ite_false] at h_subst   
              . --  all v, ψ  (v ≠ x and v ≠ y) and x is free in ψ
                simp only [is_substable, x_free, beq_iff_eq, bne, ite_false, Bool.and_eq_true, Bool.not_eq_true',
                  beq_eq_false_iff_ne, ne_eq, Ne.symm y_v, not_false_eq_true, true_and] at h_subst 
                -- proof:
                apply Iff.intro
                . intro h1
                  -- step one: turn
                  --  (M,s,g)⊨(all v, ψ)[y//x] into
                  --  (M,s,g)⊨all v, ψ[y//x]
                  simp only [subst_svar, if_neg x_v] at h1
                  -- step two
                  intro f' f'_var_g'_v
                  -- Here's the fun part. We're going to apply the
                  --  variant mirror property to f' and g', to obtain
                  --  an interpretation f that is a v-variant of g and 
                  --  also an x-variant of f'.
                  -- Since f is a v-variant of g and we have (M,s,g)⊨all v, ψ[y//x],
                  --  we'll obtain (M,s,f)⊨ψ[y//x].
                  -- From there, we'll apply the induction hypothesis to f and f'
                  --  and prove the goal.
                  have exists_mirror := variant_mirror_property g g' f' h_var (is_variant_symm.mp f'_var_g'_v)
                  match exists_mirror with
                  | ⟨f, f_var_g_v, f_var_f'_x⟩ =>
                      have t1 : f' x = f y := by
                        rw [show f y = g y from Eq.symm (f_var_g_v y (Ne.symm (Ne.intro y_v)))]
                        rw [show f' x = g' x from f'_var_g'_v x (Ne.symm (Ne.intro x_v))]
                        assumption
                      have t2 : (M,s,f) ⊨ ψ[y//x] := h1 f (is_variant_symm.mpr f_var_g_v)
                      exact (@ind_hyp s f f' h_subst f_var_f'_x t1).mp t2
                . intro h1
                  -- do the same thing backwards, basically
                  simp only [subst_svar, if_neg x_v]
                  intro f f_var_g_v
                  have exists_mirror := variant_mirror_property f g g' f_var_g_v h_var
                  match exists_mirror with
                  | ⟨f', f_var_f'_x, f'_var_g'_v⟩ =>
                    have t1 : f' x = f y := by
                        rw [show f y = g y from f_var_g_v y (Ne.symm (Ne.intro y_v))]
                        rw [show f' x = g' x from f'_var_g'_v x (Ne.symm (Ne.intro x_v))]
                        assumption
                    have t2 : (M,s,f') ⊨ ψ := h1 f' f'_var_g'_v
                    exact (@ind_hyp s f f' h_subst f_var_f'_x t1).mpr t2
        | false =>
            have x_nfree : is_free x (all v, ψ) = false := preserve_notfree x v x_free
            rw [(subst_notfree_var x_nfree).left]
            apply Iff.intro
            . intro h2 g'' v_variant
              have := generalize_not_free x_nfree M s g
              rw [iff_sat] at this
              exact ((this.mp h2) g' (is_variant_symm.mp h_var)) g'' v_variant
            . intro h2
              have := generalize_not_free x_nfree M s g'
              rw [iff_sat] at this
              exact (this.mp h2) g h_var
    | _        => simp

    theorem nom_substitution {φ : Form N} {x : SVAR} {i : NOM N} {g g' : I M.W}
    (h_var : is_variant g g' x) (h_which_var : g' x = M.Vₙ i) :
    (((M,s,g) ⊨ φ[i // x]) ↔ ((M,s,g') ⊨ φ)) := by
      induction φ generalizing s g g' with
      | svar y =>
          by_cases x_y : x = y
          . apply Iff.intro
            . intro h1
              rw [subst_nom, if_pos x_y] at h1
              rw [Sat, ←x_y, h_which_var]
              exact h1
            . intro h2
              rw [Sat, ←x_y, h_which_var] at h2
              rw [subst_nom, if_pos x_y]
              exact h2
          . apply Iff.intro
            . intro h1
              rw [subst_nom, if_neg x_y] at h1
              rw [Sat, ←(h_var y x_y)]
              exact h1
            . intro h2
              rw [subst_nom, if_neg x_y]
              rw [Sat, ←(h_var y x_y)] at h2
              exact h2
      | impl ψ χ ih_1 ih_2 =>
          have ih_1 := @ih_1 s g g' h_var h_which_var
          have ih_2 := @ih_2 s g g' h_var h_which_var
          apply Iff.intro
          . intro h1 antecedent
            exact ih_2.mp (h1 (ih_1.mpr antecedent))
          . intro h2 antecedent
            exact ih_2.mpr (h2 (ih_1.mp antecedent))
      | box ψ ih =>
          apply Iff.intro
          . intro h1 s' s_R_s'
            have ih := @ih s' g g' h_var h_which_var
            exact ih.mp (h1 s' s_R_s')
          . intro h2 s' s_R_s'
            have ih := @ih s' g g' h_var h_which_var
            exact ih.mpr (h2 s' s_R_s')
      | bind y ψ ih =>
          rw [subst_nom]
          by_cases x_y : x = y
          . rw [if_pos x_y]
            apply Iff.intro
            . intro h1
              intro f f_var_g'_y
              rw [←x_y, is_variant_symm] at f_var_g'_y
              have f_var_g_x := is_variant_trans h_var f_var_g'_y
              rw [x_y] at f_var_g_x
              exact h1 f (is_variant_symm.mp f_var_g_x)
            . intro h2
              intro f f_var_g_y
              rw [←x_y, is_variant_symm] at f_var_g_y
              have f_var_g'_x := is_variant_trans (is_variant_symm.mp f_var_g_y) h_var
              rw [x_y] at f_var_g'_x
              exact h2 f f_var_g'_x
          . rw [if_neg x_y]
            apply Iff.intro
            . intro h1
              intro f' f'_var_g'_y
              have t1 : f' x = Model.Vₙ M i := Eq.trans (f'_var_g'_y x (Ne.symm x_y)) h_which_var
              have exists_mirror := variant_mirror_property g g' f' h_var (is_variant_symm.mp f'_var_g'_y)
              match exists_mirror with
              | ⟨f, g_var_f_y, f_var_f'_x⟩ =>
                  have t2 : (M,s,f) ⊨ ψ[i//x] := h1 f (is_variant_symm.mp g_var_f_y)
                  exact (@ih s f f' f_var_f'_x t1).mp t2
            . intro h2
              intro f f_var_g_y
              have exists_mirror := variant_mirror_property g' g f (is_variant_symm.mp h_var) (is_variant_symm.mp f_var_g_y)
              match exists_mirror with
              | ⟨f', g'_var_f'_y, f'_var_f_x⟩ =>
                  have t1 : f' x = Model.Vₙ M i := by
                    rw [← g'_var_f'_y x (Ne.symm x_y), h_which_var]
                  have t2 : (M,s,f') ⊨ ψ := h2 f' (is_variant_symm.mp g'_var_f'_y)
                  exact (@ih s f f' (is_variant_symm.mp f'_var_f_x) t1).mpr t2
      | _ => simp

  theorem sat_iterated_nec : ((M,s,g) ⊨ iterate_nec n φ) ↔ (∀ s' : M.W, (path M.R s s' n) → (M,s',g) ⊨ φ) := by
    induction n generalizing φ with
    | zero   =>
        rw [iterate_nec, iterate_nec.loop]
        unfold path
        apply Iff.intro
        . intro _ _ s_s'
          rw [←s_s']
          assumption
        . intro h
          exact h s (Eq.refl s)
    | succ m ih =>
        apply Iff.intro
        . intro h1
          rw [iter_nec_succ] at h1
          intro s' ex_path1
          unfold path at ex_path1
          match ex_path1 with
          | ⟨i, i_R_s', ex_path2⟩ =>
              exact ih.mp h1 i ex_path2 s' i_R_s'
        . intro h2
          rw [iter_nec_succ, ih]
          intro i ex_path2 s' i_R_s'
          have ex_path1 : path M.R s s' (Nat.succ m) := ⟨i, i_R_s', ex_path2⟩
          exact h2 s' ex_path1

  theorem sat_iterated_pos : ((M,s,g) ⊨ iterate_pos n φ) ↔ (∃ s' : M.W, (path M.R s s' n) ∧ (M,s',g) ⊨ φ) := by
    induction n generalizing φ with
    | zero   =>
        rw [iterate_pos, iterate_pos.loop]
        unfold path
        apply Iff.intro
        . intro h
          let s' := s
          exists s'
        . intro h
          match h with
          | ⟨s', s_s', s'_sat_φ⟩ => rw [s_s'] ; exact s'_sat_φ
    | succ m ih =>
        apply Iff.intro
        . intro h1
          rw [iter_pos_succ] at h1
          have by_ih := ih.mp h1
          match by_ih with
          | ⟨s', ex_path1, s'_pos_φ⟩ => 
            rw [pos_sat] at s'_pos_φ
            match s'_pos_φ with
              | ⟨s'', s'_R_s'', s''_φ⟩ => 
                exists s''
                exact ⟨⟨s', s'_R_s'', ex_path1⟩, s''_φ⟩
        . intro h2
          rw [iter_pos_succ]
          unfold path at h2
          match h2 with
          | ⟨s', exist, s'_φ⟩ =>
            match exist with
            | ⟨s'', s''_R_s', ex_path2⟩ =>
              have s''_pos_φ : (M,s'',g) ⊨ ◇ φ := by rw [pos_sat] ; exists s'
              have premise : ∃ s'', path M.R s s'' m ∧ (M,s'',g)⊨◇ φ := ⟨s'', ⟨ex_path2, s''_pos_φ⟩⟩
              exact ih.mpr premise

  theorem svar_unique_state {v : SVAR} :
  (((M,s,g) ⊨ Form.svar v) → (∀ r : M.W, ((M,r,g) ⊨ Form.svar v) → r = s)) := by
    intro h1 r h2
    rw [h2, h1]
end Lemmas

section Tautologies
  noncomputable def model_val_func (M : Model N) (s : M.W) (g : I M.W) : Form N → Bool := λ φ => ite ((M,s,g) ⊨ φ) true false

  noncomputable def model_eval (M : Model N) (s : M.W) (g : I M.W) : Eval N :=
      let f := model_val_func M s g
      have p1 : f ⊥ = false := by simp [model_val_func]
      have p2 : ∀ φ ψ : Form N, (f (φ ⟶ ψ) = true) ↔ (¬(f φ) = true ∨ (f ψ) = true) := λ φ ψ : Form N => by simp [model_val_func] 
      ⟨f, p1, p2⟩

  theorem taut_sound : Tautology φ → ⊨ φ := by
    intro h M s g
    have := h (model_eval M s g)
    simp [model_eval, model_val_func] at this
    exact this
end Tautologies

theorem WeakSoundness : (⊢ φ) → (⊨ φ) := by
  intro pf
  induction pf with

  | tautology h => exact taut_sound h

  | ax_k =>
      intro M s g
      unfold Sat
      intro nec_impl nec_phi (s' : M.W) (rel : M.R s s')
      exact (nec_impl s' rel) (nec_phi  s' rel)

  | ax_q1 _ _ p =>
      intro M s g h1 h2 g' variant
      have := generalize_not_free p M s g
      rw [iff_sat] at this
      have := ((this.mp h2) g' variant)
      exact (h1 g' variant) this

  | ax_q2_svar _ x y h_subst =>
      intro M s g
      intro h
      -- let's build an explicit x-variant of g, named g'
      let g' : I M.W := λ v => ite (v ≠ x) (g v) (g y)
      have h_var : is_variant g g' x := by
        intro v x_not_v
        simp [Ne.symm x_not_v]
      have h_which_var : g' x = g y := by simp
      -- this exact g' can be used in the substitution lemma we proved
      rw [svar_substitution h_subst h_var h_which_var]
      -- now the goal becomes immediately provable
      exact h g' (is_variant_symm.mp h_var)
  
  | ax_q2_nom _ x i =>
      intro M s g
      intro h
      let g' : I M.W := λ v => ite (v ≠ x) (g v) (M.Vₙ i)
      have h_var : is_variant g g' x := by
        intro v x_not_v
        simp [Ne.symm x_not_v]
      have h_which_var : g' x = M.Vₙ i := by simp
      rw [nom_substitution h_var h_which_var]
      exact h g' (is_variant_symm.mp h_var)
  
  | ax_name v =>
      intro M s g
      rw [ex_sat]
      let g' : I M.W := λ x => ite (v = x) s (g x)
      apply Exists.intro
      . apply And.intro
        . exact show is_variant g' g v by
            rw [is_variant]
            intro y v_not_y
            simp [v_not_y]
        . simp

  | ax_nom n m =>
      intro _ _ _ _ _ h
      rw [sat_iterated_pos] at h
      rw [sat_iterated_nec]
      intro s'' _ s''_sat_v
      match h with
      | ⟨s', _, s'_sat⟩ =>
          rw [and_sat] at s'_sat
          have s'_sat_v := s'_sat.left
          have s'_sat_φ := s'_sat.right
          have s''_is_s' := svar_unique_state s'_sat_v s'' s''_sat_v
          rw [s''_is_s']
          exact s'_sat_φ
  
  | @ax_brcn φ v =>
      intro M s g (h : (M,s,g) ⊨ all v, □φ) s' sRs' g' g_var_g'_v
      exact (h g' g_var_g'_v) s' sRs'

  | general _ _ ih =>
      intro M s _ g' _
      exact ih M s g'

  | @necess _ _ ih =>
      intro M _ g s' _
      exact ih M s' g

  | mp _ _ ih_maj ih_min =>
      intro M s g
      exact (ih_maj M s g) (ih_min M s g)

theorem Soundness : (Γ ⊢ φ) → (Γ ⊨ φ) := by
  rw [SyntacticConsequence]
  intro h
  apply SetEntailment
  match h with
  | ⟨L, conseq⟩ =>
    exists L
    apply WeakSoundness
    assumption

theorem Consistency : ∀ {N : Set ℕ}, ⊬ (@Form.bttm N) := by
  intro N habs
  have bot_valid := WeakSoundness habs
  let M : Model N := ⟨ℕ, λ _ => λ _ => True, λ _ => ∅,  λ _ => 0⟩
  have g : I (M.W) := λ _ => 0
  have := bot_valid M 0 g
  exact this

theorem npf_negpf : ⊢ (∼φ) → ⊬ φ := by
  intro h habs
  have := Proof.mp h habs
  exact Consistency this

theorem pos_npf_not : ⊢(◇φ) → ⊬(∼φ) := by
  rw [Form.diamond]
  intro h habs
  have := Proof.necess habs
  have := Proof.mp h this
  exact Consistency this