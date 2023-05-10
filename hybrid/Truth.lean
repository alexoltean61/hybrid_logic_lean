import Hybrid.Form
import Hybrid.Util

section Definitions

  structure Model where
    W : Type
    R : W → W → Prop
    Vₚ: PROP → set W
    Vₙ: NOM  → W

  -- interpretation function
  -- from any state variable, to exactly ONE world
  def I (W : Type) := SVAR → W

  -- let's define what it means to have a path between two elements
  -- under a relation R
  -- we will need this in proofs
  def path {α : Type} (R : α → α → Prop) (a b : α) (n : Nat) : Prop :=
    match n with
    | Nat.zero   => a = b
    | Nat.succ m => ∃ i : α, (R i b) ∧ (path R a i m)

  @[simp]
  def is_variant (g₁ : I W) (g₂ : I W) (x : SVAR) := ∀ y : SVAR, ((x ≠ y) → (g₁ y = g₂ y))

  @[simp]
  def Sat (M : Model) (s : M.W) (g : I M.W) : (φ : Form) → Prop
    | Form.bttm     => False
    | Form.prop p   => s ∈ (M.Vₚ p)
    | Form.nom  i   => s = (M.Vₙ i)
    | Form.svar x   => s = (g x)
    | Form.impl ψ χ => (Sat M s g ψ) → (Sat M s g χ)
    | Form.box  ψ   => ∀ s' : M.W, (M.R s s' → (Sat M s' g ψ))
    | Form.bind x ψ => ∀ g' : I M.W, ((is_variant g' g x) → Sat M s g' ψ)

  notation "(" M "," s "," g ")" "⊨" φ => Sat M s g φ
  notation "(" M "," s "," g ")" "⊭" φ => ¬ Sat M s g φ

  @[simp]
  def Models (M : Model) (φ : Form) := ∀ (s : M.W) (g : I M.W), ((M, s, g) ⊨ φ)

  infix:1000 "⊨" => Models
  infix:1000 "⊭" => ¬ Models

  @[simp]
  def Valid (φ : Form) := ∀ (M : Model), (M ⊨ φ)

  prefix:1000 "⊨" => Valid
  prefix:1000 "⊭" => ¬ Valid

  @[simp]
  def Sat_Set (M : Model) (s : M.W) (g : I M.W) (Γ : List Form) := ∀ (φ : Form), (List.elem φ Γ) → ((M, s, g) ⊨ φ)

  notation "(" M "," s "," g ")" "⊨" Γ => Sat_Set M s g Γ
  notation "(" M "," s "," g ")" "⊭" Γ => ¬ Sat_Set M s g Γ

  @[simp]
  def Entails (Γ : List Form) (φ : Form) := ∀ (M : Model) (s : M.W) (g : I M.W), ((M,s,g) ⊨ Γ) → ((M,s,g) ⊨ φ) 
  --def Entails (Γ : set Form) (φ : Form) := ∀ M : Model, (M ⊨ Γ) → (M ⊨ φ) 

  infix:1000 "⊨" => Entails
  infix:1000 "⊭" => ¬ Entails

end Definitions

section Theorems

  section Variants
    @[simp]
    theorem is_variant_refl {g : I W} (x : SVAR) : is_variant g g x := by simp

    @[simp]
    theorem is_variant_symm {g₁ : I W} {g₂ : I W} {x : SVAR} : is_variant g₁ g₂ x ↔ is_variant g₂ g₁ x := by
      -- bit annoying that it simplified the implication
      -- maybe prove again using simp [-implication_disjunction]
      simp
      apply Iff.intro
      . intro h1 hy
        apply Or.elim (h1 hy)
        . intro x_eq_y
          exact Or.inl x_eq_y
        . intro g1_eq_g2
          exact Or.inr (Eq.symm g1_eq_g2)
      . intro h2 hy
        apply Or.elim (h2 hy)
        . intro x_eq_y
          exact Or.inl x_eq_y
        . intro g2_eq_g1
          exact Or.inr (Eq.symm g2_eq_g1)

    theorem is_variant_trans {g₁ g₂ g₃ : I W} {x : SVAR} : is_variant g₁ g₂ x → is_variant g₂ g₃ x → is_variant g₁ g₃ x := by
      rw [is_variant, is_variant, is_variant]
      intros a b y x_not_y
      have g1_is_g2 := a y x_not_y
      have g2_is_g3 := b y x_not_y
      exact Eq.trans g1_is_g2 g2_is_g3

    theorem two_step_variant {g₁ g₂ g₃ : I W} {x y : SVAR} (g₁₂x : is_variant g₁ g₂ x) (g₂₃y : is_variant g₂ g₃ y) : ∀ v : SVAR, (v ≠ x ∧ v ≠ y) → g₁ v = g₃ v := by
      intro v ⟨v_not_x, v_not_y⟩ 
      have one_eq_two   := g₁₂x v (Ne.symm v_not_x)
      have two_eq_three := g₂₃y v (Ne.symm v_not_y)
      exact Eq.trans one_eq_two two_eq_three

    theorem two_step_variant_rev (g₁ g₃ : I W) {x y : SVAR} (two_step : ∀ v : SVAR, (v ≠ x ∧ v ≠ y) → g₁ v = g₃ v) : ∃ g₂ : I W, (is_variant g₁ g₂ x ∧ is_variant g₂ g₃ y) := by
      let g₂ : I W := (λ v : SVAR => if (v = x) then (g₃ v) else if (v = y) then (g₁ v) else (g₃ v))
      exists g₂
      apply And.intro
      . rw [is_variant]
        intro v v_not_x
        have v_not_x := Ne.symm v_not_x
        simp
        unfold ite
        cases (instDecidableEqSVAR v x) with
        | isTrue  v_is_x =>
            exact False.elim (v_not_x v_is_x)
        | isFalse _      =>
            cases (instDecidableEqSVAR v y) with
            | isTrue  _       => rfl
            | isFalse v_not_y => rw [show (g₁ v = g₃ v) from two_step v (And.intro v_not_x v_not_y)]
      . rw [is_variant]
        intro v v_not_y
        have v_not_y := Ne.symm v_not_y
        simp
        unfold ite
        cases (instDecidableEqSVAR v x) with
        | isTrue  _ => rfl
        | isFalse _ =>
          cases (instDecidableEqSVAR v y) with
          | isTrue v_is_y => exact False.elim (v_not_y v_is_y)
          | isFalse _     => rfl

    theorem variant_mirror_property (g₁ g₂ g₃ : I W) {x y : SVAR} (g₁₂x : is_variant g₁ g₂ x) (g₂₃y : is_variant g₂ g₃ y) : 
      ∃ g₂_mirror : I W, (is_variant g₁ g₂_mirror y ∧ is_variant g₂_mirror g₃ x) := by
      have two_step := two_step_variant g₁₂x g₂₃y
      conv at two_step =>
        intro v
        conv => lhs ; rw [conj_comm]
      exact two_step_variant_rev g₁ g₃ two_step 

  end Variants

  section Satisfaction

    theorem bind_comm {M : Model} {s : M.W} {g : I M.W} {φ : Form} {x y : SVAR} : ((M,s,g) ⊨ all x, (all y, φ)) ↔ ((M,s,g) ⊨ all y, (all x, φ)) := by
      apply Iff.intro
      . intro h1
        intros h var_h_g i var_i_h
        have two_step : ∀ (v : SVAR), v ≠ x ∧ v ≠ y → g v = i v := (λ a => λ b => Eq.symm ((two_step_variant var_i_h var_h_g) a b))
        have exist_mid_g := two_step_variant_rev g i two_step
        match exist_mid_g with
        | ⟨mid_g, mid_g_var_g, mid_g_var_i⟩ =>
          have mid_g_sat := h1 mid_g (is_variant_symm.mp mid_g_var_g)
          exact mid_g_sat i (is_variant_symm.mp mid_g_var_i)
      . intro h2
        intros h var_h_g i var_i_h
        have two_step : ∀ (v : SVAR), v ≠ y ∧ v ≠ x → g v = i v := (λ a => λ b => Eq.symm ((two_step_variant var_i_h var_h_g) a b))
        have exist_mid_g := two_step_variant_rev g i two_step
        match exist_mid_g with
        | ⟨mid_g, mid_g_var_g, mid_g_var_i⟩ =>
          have mid_g_sat := h2 mid_g (is_variant_symm.mp mid_g_var_g)
          exact mid_g_sat i (is_variant_symm.mp mid_g_var_i)
  
    theorem neg_sat {φ : Form} {M : Model} {s : M.W} {g : I M.W} : ((M,s,g) ⊨ ∼φ) ↔ ((M,s,g) ⊭ φ) := by
      simp
    theorem and_sat {φ ψ : Form} {M : Model} {s : M.W} {g : I M.W} : ((M,s,g) ⊨ φ ⋀ ψ) ↔ (((M,s,g) ⊨ φ) ∧ (M,s,g) ⊨ ψ) := by
      simp
    theorem or_sat  {φ ψ : Form} {M : Model} {s : M.W} {g : I M.W} : ((M,s,g) ⊨ φ ⋁ ψ) ↔ (((M,s,g) ⊨ φ) ∨ (M,s,g) ⊨ ψ) := by
      simp
    theorem pos_sat {φ : Form} {M : Model} {s : M.W} {g : I M.W} : (((M,s,g) ⊨ ◇φ) ↔ (∃ s' : M.W, (M.R s s' ∧ (M,s',g) ⊨ φ))) := by
      simp
    theorem ex_sat  {x : SVAR} {φ : Form} {M : Model} {s : M.W} {g : I M.W} : ((M,s,g) ⊨ ex x, φ) ↔ (∃ g' : I M.W, (is_variant g' g x) ∧ ((M,s,g') ⊨ φ)) := by
      simp [-is_variant]

    theorem sat_nested_impl : ((M,s,g) ⊨ φ ⟶ ψ ⟶ χ) ↔ ((M,s,g) ⊨ (φ ⋀ ψ) ⟶ χ) := by
      apply Iff.intro
      . intro h1 h2
        rw [and_sat] at h2
        exact h1 (h2.left) (h2.right)
      . intro h1 h2 h3
        exact h1 (and_sat.mpr ⟨h2, h3⟩)

    theorem sat_truth : ((M,s,g) ⊨ ⊥ ⟶ ⊥) := by
      intro _
      assumption

    theorem sat_empty_set : ∀ (M : Model) (s : M.W) (g : I M.W), ((M,s,g) ⊨ []) := by
      intro _ _ _ _ _
      contradiction

    theorem sat_singleton_set : ((M,s,g) ⊨ [φ]) ↔ ((M,s,g) ⊨ φ) := by
      unfold Sat_Set
      apply Iff.intro
      . intro h
        apply h
        rw [List.elem, beq_self_eq_true φ]
      . intro h
        intro ψ elem_ψ
        rw [List.elem, List.elem] at elem_ψ
        cases t : ψ == φ
        . rw [t] at elem_ψ
          contradiction
        . rw [eq_of_beq t]
          exact h

    theorem sat_cons {Γ : List Form} : (((M,s,g) ⊨ Γ) ∧ ((M,s,g) ⊨ [φ])) ↔ ((M,s,g) ⊨ φ :: Γ) := by
      rw [sat_singleton_set]
      apply Iff.intro
      . intro h ψ
        by_cases c : ψ = φ
        . rw [List.elem, c]
          intro _
          exact h.right
        . rw [List.elem, beq_false_of_ne c]
          intro h2
          exact h.left ψ h2
      . intro h
        apply And.intro
        . intro ψ ψ_in_Γ
          have : List.elem ψ (φ :: Γ) = true := by
            by_cases c : ψ = φ
            . rw [List.elem, c, beq_self_eq_true]
            . rw [List.elem, beq_false_of_ne c, ψ_in_Γ]
          exact h ψ this
        . apply h φ
          rw [List.elem, beq_self_eq_true]

    theorem sat_prec : ((M,s,g) ⊨ h :: t) → ((M,s,g) ⊨ t) := by
      intro hyp ψ ψ_in_t
      have : List.elem ψ (h :: t) = true := by
        by_cases c : ψ = h
        . rw [List.elem, c, beq_self_eq_true]
        . rw [List.elem, beq_false_of_ne c, ψ_in_t]
      exact hyp ψ this

    theorem Deduction (Γ : List Form) (φ : Form) : ((ψ :: Γ) ⊨ φ) ↔ (Γ ⊨ (ψ ⟶ φ)) := by
      apply Iff.intro
      . intro hyp
        intro M s g sat_Γ sat_ψ
        apply hyp M s g
        rw [←sat_singleton_set] at sat_ψ
        exact (@sat_cons M s g ψ Γ).mp ⟨sat_Γ, sat_ψ⟩
      . intro hyp
        intro M s g sat_ψ_Γ 
        have sat_h_t := (@sat_prec M s g ψ Γ) sat_ψ_Γ 
        have sat_ψ := sat_ψ_Γ ψ
        rw [List.elem, beq_self_eq_true] at sat_ψ
        have sat_ψ := sat_ψ (Eq.refl true)
        exact hyp M s g sat_h_t sat_ψ

    theorem SemanticConsequence (Γ : List Form) (φ : Form) : (Γ ⊨ φ) ↔ (⊨ (conjunction Γ ⟶ φ)) := by
      induction Γ generalizing φ with
      | nil     =>
          unfold conjunction
          apply Iff.intro
          . intro h
            intro M s g _
            exact (h M s g) (sat_empty_set M s g)
          . intro h
            intro M s g _
            exact (h M s g) sat_truth
      | cons h t ih =>
          rw [Deduction, ih (h ⟶ φ)]
          apply Iff.intro
          . intro hyp
            intro M s g sat_conj
            have := sat_nested_impl.mp (hyp M s g)
            have : (M,s,g)⊨h⋀conjunction t⟶φ := by
              intro p
              rw [and_sat] at p
              exact this (and_sat.mpr ⟨p.right, p.left⟩)
            rw [on_conj] at this
            exact this sat_conj
          . intro hyp
            intro M s g sat_conj
            conv at hyp => rhs lhs rw [←on_conj]
            have : (M,s,g)⊨(conjunction t⋀h)⟶φ := by
              intro p
              rw [and_sat] at p
              exact (hyp M s g) (and_sat.mpr ⟨p.right, p.left⟩)
            exact (sat_nested_impl.mpr this) sat_conj

    end Satisfaction

end Theorems