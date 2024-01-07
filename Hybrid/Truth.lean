import Hybrid.Form
import Hybrid.Util
import Hybrid.Substitutions

section Definitions

  structure Model (N : Set ℕ) where
    W : Type
    R : W → W → Prop
    Vₚ: PROP → Set W
    Vₙ: NOM N  → W

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
  def is_variant (g₁ g₂ : I W) (x : SVAR) := ∀ y : SVAR, ((x ≠ y) → (g₁ y = g₂ y))

  @[simp]
  def Sat (M : Model N) (s : M.W) (g : I M.W) : (φ : Form N) → Prop
    | Form.bttm     => False
    | Form.prop p   => s ∈ (M.Vₚ p)
    | Form.nom  i   => s = (M.Vₙ i)
    | Form.svar x   => s = (g x)
    | Form.impl ψ χ => (Sat M s g ψ) → (Sat M s g χ)
    | Form.box  ψ   => ∀ s' : M.W, (M.R s s' → (Sat M s' g ψ))
    | Form.bind x ψ => ∀ g' : I M.W, ((is_variant g' g x) → Sat M s g' ψ)

  notation "(" M "," s "," g ")" "⊨" φ => Sat M s g φ
  notation "(" M "," s "," g ")" "⊭" φ => ¬ Sat M s g φ

  theorem neg_sat : ((M,s,g) ⊨ ∼φ) ↔ ((M,s,g) ⊭ φ) := by
    simp only [Sat, or_false]
  theorem and_sat : ((M,s,g) ⊨ φ ⋀ ψ) ↔ (((M,s,g) ⊨ φ) ∧ (M,s,g) ⊨ ψ) := by
    simp
  theorem or_sat  : ((M,s,g) ⊨ φ ⋁ ψ) ↔ (((M,s,g) ⊨ φ) ∨ (M,s,g) ⊨ ψ) := by
    simp
  theorem pos_sat : (((M,s,g) ⊨ ◇φ) ↔ (∃ s' : M.W, (M.R s s' ∧ (M,s',g) ⊨ φ))) := by
    simp
  theorem ex_sat  : ((M,s,g) ⊨ ex x, φ) ↔ (∃ g' : I M.W, (is_variant g' g x) ∧ ((M,s,g') ⊨ φ)) := by
    simp [-is_variant]
  theorem iff_sat : ((M,s,g) ⊨ (φ ⟷ ψ)) ↔ (((M,s,g) ⊨ φ) ↔ (M,s,g) ⊨ ψ) := by
    rw [Form.iff, and_sat, Sat, Sat]
    apply Iff.intro
    . intro ⟨h1, h2⟩
      apply Iff.intro <;> assumption
    . intro h1
      apply And.intro <;> simp [h1]

  @[simp]
  def Valid (φ : Form N) := ∀ (M : Model N) (s : M.W) (g : I M.W), ((M, s, g) ⊨ φ)

  prefix:1000 "⊨" => Valid
  prefix:1000 "⊭" => ¬ Valid

  @[simp]
  def Sat_Set (M : Model N) (s : M.W) (g : I M.W) (Γ : Set (Form N)) := ∀ (φ : Form N), (φ ∈ Γ) → ((M, s, g) ⊨ φ)

  notation "(" M "," s "," g ")" "⊨" Γ => Sat_Set M s g Γ
  notation "(" M "," s "," g ")" "⊭" Γ => ¬ Sat_Set M s g Γ

  --def Entails (Γ : set Form) (φ : Form) := ∀ M : Model, (M ⊨ Γ) → (M ⊨ φ)
  @[simp]
  def Entails (Γ : Set (Form N)) (φ : Form N) := ∀ (M : Model N) (s : M.W) (g : I M.W), ((M,s,g) ⊨ Γ) → ((M,s,g) ⊨ φ)


  infix:1000 "⊨" => Entails
  notation Γ "⊭" φ => ¬ (Entails Γ φ)

  @[simp]
  def satisfiable (Γ : Set (Form N)) := ∃ (M : Model N) (s : M.W) (g : I M.W), (M,s,g) ⊨ Γ

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
        intro v v_x
        have v_x := Ne.symm v_x
        simp only [v_x, ite_false, Ne.symm]
        by_cases v_y : v = y
        . simp only [v_y, ite_true]
        . simp only [show (g₁ v = g₃ v) from
                          two_step v (And.intro v_x v_y),
                     ite_self]
      . rw [is_variant]
        intro v v_y
        have v_y := Ne.symm v_y
        by_cases v_x : v = x
        . simp only [v_x, ite_true]
        . simp only [v_x, v_y, ite_false, ite_self]

    theorem variant_mirror_property (g₁ g₂ g₃ : I W) {x y : SVAR} (g₁₂x : is_variant g₁ g₂ x) (g₂₃y : is_variant g₂ g₃ y) :
      ∃ g₂_mirror : I W, (is_variant g₁ g₂_mirror y ∧ is_variant g₂_mirror g₃ x) := by
      have two_step := two_step_variant g₁₂x g₂₃y
      conv at two_step =>
        intro v
        conv => lhs ; rw [conj_comm]
      exact two_step_variant_rev g₁ g₃ two_step

  end Variants

  section Satisfaction

    theorem bind_comm {M : Model N} {s : M.W} {g : I M.W} {φ : Form N} {x y : SVAR} : ((M,s,g) ⊨ all x, (all y, φ)) ↔ ((M,s,g) ⊨ all y, (all x, φ)) := by
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

    theorem SatConjunction (Γ : Set (Form N)) (L : List Γ) : Γ ⊨ conjunction Γ L := by
      intro M s g M_sat_Γ
      induction L with
      | nil =>
          simp only [conjunction, Sat]
      | cons h t ih =>
          simp only [conjunction, and_sat, ih, and_true]
          exact M_sat_Γ h h.prop

    theorem SetEntailment (Γ : Set (Form N)) : (∃ L, ⊨ (conjunction Γ L ⟶ ψ)) → Γ ⊨ ψ := by
      intro h
      intro M s g M_sat_Γ
      match h with
      | ⟨L, hw⟩ =>
          have l1 := hw M s g
          have l2 := SatConjunction Γ L M s g M_sat_Γ
          rw [Sat] at l1
          exact l1 l2

    end Satisfaction

  theorem D_help {Γ : Set (Form N)} : ((M,s,g)⊨Γ ∪ {φ}) ↔ (((M,s,g)⊨Γ) ∧ (M,s,g) ⊨ {φ}) := by
    apply Iff.intro
    . intro h
      rw [Sat_Set] at h
      apply And.intro
      . intro χ mem; apply h; simp [mem]
      . intro χ mem; apply h; simp at mem; simp [mem]
    . intro ⟨hl, hr⟩
      intro χ mem; simp at mem
      apply Or.elim mem <;> {
        intros; first | {apply hl; assumption} | {apply hr; assumption}
      }

  theorem SemanticDeduction {Γ : Set (Form N)} : (Γ ⊨ (φ ⟶ ψ)) ↔ ((Γ ∪ {φ}) ⊨ ψ) := by
    apply Iff.intro <;> {
      intro h M s g sat_set
      try (intro sat_φ;
            have sat_φ : (M,s,g) ⊨ {φ} := by simp only [Sat_Set, Set.mem_singleton_iff, forall_eq,
              sat_φ])
      try (have := h M s g (D_help.mpr ⟨sat_set, sat_φ⟩))
      try (have ⟨sat_l, sat_r⟩ := D_help.mp sat_set;
            simp only [Sat_Set, Set.mem_singleton_iff, forall_eq] at sat_r ;
            have := (h M s g sat_l) sat_r)
      assumption
    }

end Theorems

def Model.odd_noms (M : Model TotalSet) : Model TotalSet where
  W := M.W
  R := M.R
  Vₚ:= M.Vₚ
  Vₙ:= λ i => M.Vₙ ((i-1)/2)

def Model.odd_noms_inv (M : Model TotalSet) : Model TotalSet where
  W := M.W
  R := M.R
  Vₚ:= M.Vₚ
  Vₙ:= λ i => M.Vₙ (i*2+1)

theorem sat_odd_noms {φ : Form TotalSet} : ((M,s,g) ⊨ φ) ↔ ((M.odd_noms,s,g) ⊨ φ.odd_noms) := by
  induction φ generalizing s g with
  | nom i =>
      simp [odd_nom, Model.odd_noms]
  | impl φ ψ ih1 ih2 =>
      rw [odd_impl, Sat, Sat, ih1, ih2]
  | box φ ih =>
      rw [odd_box, Sat, Sat]
      apply Iff.intro
      . intro h1 s' h2
        rw [←@ih s' g]
        exact h1 s' h2
      . intro h1 s' h2
        rw [@ih s' g]
        exact h1 s' h2
  | bind x φ ih =>
      rw [odd_bind, Sat, Sat]
      apply Iff.intro
      . intro h1 g' h2
        rw [←@ih s g']
        exact h1 g' h2
      . intro h1 g' h2
        rw [@ih s g']
        exact h1 g' h2
  | _ => simp [Form.odd_noms, Model.odd_noms]

theorem sat_odd_noms' {φ : Form TotalSet} : ((M,s,g) ⊨ φ.odd_noms) ↔ ((M.odd_noms_inv,s,g) ⊨ φ) := by
--  conv => rhs; rw [sat_odd_noms]
  induction φ generalizing s g with
  | nom i =>
      simp [odd_nom, Model.odd_noms, Model.odd_noms_inv]
  | impl φ ψ ih1 ih2 =>
      rw [odd_impl, Sat, Sat, ih1, ih2]
  | box φ ih =>
      rw [odd_box, Sat, Sat]
      apply Iff.intro
      . intro h1 s' h2
        rw [←@ih s' g]
        exact h1 s' h2
      . intro h1 s' h2
        rw [@ih s' g]
        exact h1 s' h2
  | bind x φ ih =>
      rw [odd_bind, Sat, Sat]
      apply Iff.intro
      . intro h1 g' h2
        rw [←@ih s g']
        exact h1 g' h2
      . intro h1 g' h2
        rw [@ih s g']
        exact h1 g' h2
  | _ => simp [Form.odd_noms, Model.odd_noms, Model.odd_noms_inv]

/-
theorem testtt {Γ : Set Form} : ((M,s,g) ⊨ Γ) ↔ ((M.odd_noms,s,g) ⊨ Γ.odd_noms) := by
  apply Iff.intro
  . intro h φ_odd φ_odd_prop
    have ⟨φ, mem, is_odd⟩ := φ_odd_prop
    rw [←is_odd, ←sat_odd_noms]
    exact h φ mem
  . intro h φ mem
    rw [sat_odd_noms]
    have φ_odd_mem : φ.odd_noms ∈ Γ.odd_noms := by exists φ
    exact h φ.odd_noms φ_odd_mem

theorem testtt' {Γ : Set Form} : ((M,s,g) ⊨ Γ.odd_noms) ↔ ((M.odd_noms_inv,s,g) ⊨ Γ) := by
  apply Iff.intro
  . intro h φ mem
    rw [←sat_odd_noms']
    have φ_odd_mem : φ.odd_noms ∈ Γ.odd_noms := by exists φ
    exact h φ.odd_noms φ_odd_mem
  . intro h φ_odd φ_odd_prop
    have ⟨φ, mem, is_odd⟩ := φ_odd_prop
    rw [←is_odd, sat_odd_noms']
    exact h φ mem

theorem plang : Γ ⊨ φ ↔ Γ.odd_noms ⊨ φ.odd_noms := by
  apply Iff.intro
  . intro h M s g sat_odd_set
    rw [testtt'] at sat_odd_set
    have := h M.odd_noms_inv s g sat_odd_set
    rw [sat_odd_noms']
    exact this
  . intro h M s g sat_set
    rw [testtt] at sat_set
    have := h M.odd_noms s g sat_set
    rw [sat_odd_noms]
    exact this

#print axioms plang
-/
