import Hybrid.Form
import Hybrid.Util

structure Model where
  W : Type
  R : W → W → Prop
  Vₚ: PROP → set W
  Vₙ: NOM  → W

-- interpretation function
-- from any state variable, to exactly ONE world
def I (W : Type) := SVAR → W

@[simp]
def is_variant (g₁ : I W) (g₂ : I W) (x : SVAR) := ∀ y : SVAR, ((x ≠ y) → (g₁ y = g₂ y))

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

@[simp]
def Models (M : Model) (φ : Form) := ∀ (s : M.W) (g : I M.W), ((M, s, g) ⊨ φ)

infix:1000 "⊨" => Models
infix:1000 "⊭" => ¬ Models

@[simp]
def Valid (φ : Form) := ∀ (M : Model), (M ⊨ φ)

prefix:1000 "⊨" => Valid
prefix:1000 "⊭" => ¬ Valid

@[simp]
def Models_Set (M : Model) (Γ : set Form) := ∀ (s : M.W) (g : I M.W) (φ : Form), (φ ∈ Γ) → ((M, s, g) ⊨ φ)

infix:1000 "⊨" => Models_Set
infix:1000 "⊭" => ¬ Models_Set

@[simp]
def Entails (Γ : set Form) (φ : Form) := ∀ M : Model, (M ⊨ Γ) → (M ⊨ φ) 

infix:1000 "⊨" => Entails
infix:1000 "⊭" => ¬ Entails

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