import Hybrid.Form
import Hybrid.Proof
import Hybrid.Truth
import Hybrid.Util
open Classical

section Lemmas
  theorem generalize_bound {φ : Form} {v : SVAR} {M : Model} {s : M.W} {g : I M.W} (h1 : ¬is_free v φ) (h2 : (M,s,g) ⊨ φ) : ((M,s,g) ⊨ all v, φ) :=
    match φ with
    | Form.bttm   => False.elim h2
    | Form.prop p => by
        simp at h2
        rw [Sat]
        intros
        exact h2
    | Form.svar _ =>
        have not_h1 : is_free v (Form.svar _) := trivial
        False.elim (h1 not_h1)
    | Form.nom _ =>
        have not_h1 : is_free v (Form.nom _) := trivial
        False.elim (h1 not_h1)
    | Form.impl ψ χ => by
        rw [Sat]
        rw [is_free, negated_disjunction] at h1
        rw [Sat] at h2
        intros g' variant antecedent
        have sym_variant := is_variant_symm.mp variant
        -- apply the induction hypothesis:
        have by_ind_hyp := generalize_bound h1.left antecedent
        have by_mp_ind  := generalize_bound h1.right (h2 (by_ind_hyp g sym_variant))
        exact by_mp_ind g' variant
    | Form.box ψ    => by
        rw [is_free] at h1
        intros g' variant s' is_neigh
        exact generalize_bound h1 (h2 s' is_neigh) g' variant
    | Form.bind u ψ => by
        -- ugly and convoluted
        -- can you rewrite this?
        rw [is_free] at h1
        have h1_rw : (u = v ∨ ¬is_free v ψ) :=
          byContradiction
          (λ nh1_rw => by
            simp at nh1_rw
            have nh1 : if u = v then False else is_free v ψ :=
              match (instDecidableEqSVAR u v) with
              | isTrue u_is_v => False.elim (nh1_rw.left u_is_v)
              | isFalse _ => nh1_rw.right
            exact False.elim (h1 nh1)
          )
        ---
        apply Or.elim h1_rw
        . intro u_is_v
          rw [u_is_v]
          rw [u_is_v] at h2
          intros g' variant1 g'' variant2
          have variant3 := is_variant_trans variant2 variant1
          exact h2 g'' variant3
        . intro bound_in_ψ
          rw [bind_comm]
          intros g' variant_u
          exact generalize_bound bound_in_ψ (h2 g' variant_u)

  theorem svar_substitution {φ : Form} {x y : SVAR} {M : Model} {s : M.W} {g g' : I M.W} 
  (h_subst : is_substable φ y x) (h_var : is_variant g g' x) (h_which_var : g' x = g y) :
  (((M,s,g) ⊨ φ[y // x]) ↔ (M,s,g') ⊨ φ) := by
    induction φ with
    | svar z   =>
        apply Iff.intro
        . intro h
          by_cases z_x : z = x
          . rw [show z[y//x] = y by rw[z_x, subst_svar, if_pos (Eq.refl x)], Sat] at h
            rw [z_x, Sat, h_which_var]
            exact h
          . rw [show z[y//x] = z by rw[subst_svar, if_neg (Ne.symm (Ne.intro z_x))], Sat] at h
            rw [Sat, ←(h_var z (Ne.symm z_x))]
            exact h
        . intro h
          by_cases z_x : z = x
          . rw [z_x, show x[y//x] = y by rw[subst_svar, if_pos (Eq.refl x)], Sat, ←h_which_var]
            rw [Sat, z_x] at h
            exact h
          . rw [show z[y//x] = z by rw[subst_svar, if_neg (Ne.symm (Ne.intro z_x))], Sat]
            rw [Sat, ←(h_var z (Ne.symm z_x))] at h
            exact h
    | impl ψ χ ind_hyp_1 ind_hyp_2 =>
        have by_ind_hyp_1 := ind_hyp_1 h_subst.left
        have by_ind_hyp_2 := ind_hyp_2 h_subst.right
        apply Iff.intro
        . simp [-implication_disjunction]
          intro h1 h2
          exact by_ind_hyp_2.mp (h1 (by_ind_hyp_1.mpr h2))
        . intro h1 h2
          exact by_ind_hyp_2.mpr (h1 (by_ind_hyp_1.mp h2))
    | box  ψ _                    =>
        apply Iff.intro
        . intro h1 s' s_R_s'
          have by_ind_hyp := @svar_substitution ψ x y M s' g g' h_subst h_var h_which_var
          exact by_ind_hyp.mp (h1 s' s_R_s')
        . intro h1 s' s_R_s'
          have by_ind_hyp := @svar_substitution ψ x y M s' g g' h_subst h_var h_which_var
          exact by_ind_hyp.mpr (h1 s' s_R_s')
    | bind v ψ ind_hyp =>
        by_cases x_free : is_free x ψ
        . by_cases x_v : x = v
          . -- all x, ψ             and       x is free in ψ
            have x_bound : ¬is_free x (all v, ψ) :=
              by conv => rhs rhs lhs rw [←x_v] ; exact not_bound_when_quantified
            apply Iff.intro
            . intro h1
              conv at h1 => rhs ; rw [subst_bound_var x_bound]
              exact (generalize_bound x_bound h1) g' (is_variant_symm.mp h_var)
            . intro h1
              conv => rhs ; rw [subst_bound_var x_bound, ←x_v]
              rw [←x_v] at h1
              rw [←x_v] at x_bound
              exact (generalize_bound x_bound h1) g h_var
          . -- all v, ψ   (v ≠ x)   and       x is free in ψ
            by_cases y_v : y = v
            . unfold is_substable at h_subst
              rw [if_neg (double_negation.mpr x_free), if_neg (double_negation.mpr y_v)] at h_subst
              exact False.elim h_subst
            . -- simplify h_subst to is_substable ψ y x
              unfold is_substable at h_subst
              rw [if_neg (double_negation.mpr x_free), if_pos y_v] at h_subst
              apply Iff.intro
              . intro h1
                -- step one: turn
                --  (M,s,g)⊨(all v, ψ)[y//x] into
                --  (M,s,g)⊨all v, ψ[y//x]
                unfold subst_svar at h1
                rw [if_neg x_v] at h1
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
                    exact (@svar_substitution ψ x y M s f f' h_subst f_var_f'_x t1).mp t2
              . intro h1
                -- do the same thing backwards, basically
                unfold subst_svar
                rw [if_neg x_v]
                intro f f_var_g_v
                have exists_mirror := variant_mirror_property f g g' f_var_g_v h_var
                match exists_mirror with
                | ⟨f', f_var_f'_x, f'_var_g'_v⟩ =>
                  have t1 : f' x = f y := by
                      rw [show f y = g y from f_var_g_v y (Ne.symm (Ne.intro y_v))]
                      rw [show f' x = g' x from f'_var_g'_v x (Ne.symm (Ne.intro x_v))]
                      assumption
                  have t2 : (M,s,f') ⊨ ψ := h1 f' f'_var_g'_v
                  exact (@svar_substitution ψ x y M s f f' h_subst f_var_f'_x t1).mpr t2
        . have x_bound : ¬is_free x (all v, ψ) := preserve_boundness x_free
          apply Iff.intro
          . intro h2 g'' v_variant
            conv at h2 => rhs ; rw [subst_bound_var x_bound]
            exact ((generalize_bound x_bound h2) g' (is_variant_symm.mp h_var)) g'' v_variant
          . intro h2
            conv => rhs ; rw [subst_bound_var x_bound]
            exact (generalize_bound x_bound h2) g h_var
    | _        => simp
    termination_by svar_substitution φ _ _ _ _ _ _ _ _ _ => φ
    decreasing_by sorry

end Lemmas

theorem Soundness {Γ : set Form} {φ : Form} : (Γ ⊢ φ) → (Γ ⊨ φ)
  | Proof.premise hp => by
      rw [Entails]
      intro (M : Model) (M_sat_Γ : M⊨Γ) (s : M.W) (g : I M.W)
      rw [Models_Set] at M_sat_Γ
      exact M_sat_Γ s g φ hp

  | Proof.general t => by
      admit

  | Proof.necess pf => by
     admit

  | Proof.ax_k => by
      rw [Entails]
      intro (M : Model) (M_sat_Γ : M ⊨ Γ) (s : M.W) (g : I M.W)
      unfold Sat
      intro nec_impl nec_phi (s' : M.W) (rel : M.R s s')
      exact (nec_impl s' rel) (nec_phi  s' rel)

  | @Proof.ax_q1 _ _ _ _ p => by
      intro _ _ _ g h1 h2 g' variant
      exact (h1 g' variant) ((generalize_bound p h2) g' variant)

  | @Proof.ax_q2_svar _ φ x y h_subst => by
      intro (M : Model) (M_sat_Γ : M ⊨ Γ) (s : M.W) (g : I M.W)
      intro h
      -- let's build an explicit x-variant of g, named g'
      let g' : I M.W := λ v => ite (v ≠ x) (g v) (g y)
      have h_var : is_variant g g' x := by
        intro v x_not_v
        simp [Ne.symm x_not_v]
      have h_which_var : g' x = g y := by simp
      -- this exact g' can be used in the substitution lemma we proved
      rw [@svar_substitution φ x y M s g g' h_subst h_var h_which_var]
      -- now the goal becomes immediately provable
      exact h g' (is_variant_symm.mp h_var)

  | _ => sorry