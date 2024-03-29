import Hybrid.Lindenbaum
import Hybrid.ProofUtils

open Proof

def conjunction' (L : List (Form N)) : Form N :=
  match L with
    | []     => ⊥ ⟶ ⊥
    | [h]    => h
    | h :: t => h ⋀ conjunction' t

def has_wit_conj (Γ : Set (Form N)) : Form N → Form N → Prop
  | (ex x, ψ), φ => ∃ i : NOM N, ◇(((ex x, ψ) ⟶ ψ[i//x]) ⋀ φ) ∈ Γ
  | _, _         => True

lemma l313 {τ χ : Form N} (h1 : is_substable χ y x) (h2 : occurs y τ = false) (h3 : occurs y χ = false) :
  ⊢ (◇ τ ⟶ ex y, ◇(((ex x, χ) ⟶ χ[y//x]) ⋀ τ)) := by
  have l1 := Γ_empty.mpr (rename_bound_ex h3 h1)
  have l2 := Γ_empty.mp (Γ_conj_elim_l l1)
  have l3 := @b361 N y (χ[y//x]) (ex x, χ)
  have l4 := mp l3 l2
  have l5 := tautology (@ax_1 N ((ex y, (ex x, χ)⟶χ[y//x])) τ)
  have l6 := mp l5 l4
  have l7 := tautology (@imp_refl N τ)
  have l8 := tautology (@conj_intro_hs N τ ((ex y, (ex x, χ)⟶χ[y//x])) τ)
  have l9 := mp (mp l8 l6) l7
  have l10 := @b362' N y ((ex x, χ)⟶χ[y//x]) τ (notoccurs_notfree h2)
  have l11 := hs l9 l10
  have l12 := diw_impl l11
  have l13 := hs l12 ax_brcn_contrap
  exact l13

lemma l313' {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : ∀ ψ : Form N, has_wit_conj Δ ψ φ := by
  intro ψ
  unfold has_wit_conj
  split
  . next _ _ x ψ =>
      have ⟨y, geq, nocc, subst⟩ := (φ ⟶ ψ ⟶ all x, ⊥).new_var_properties
      have y_ne_x : y ≠ x := by
        intro habs
        have := habs ▸ (new_var_geq2 (new_var_geq1 (new_var_geq1 geq).2).2).1
        simp [SVAR.le, SVAR.add] at this
      have subst := subst x
      simp [occurs, is_substable, is_free] at nocc subst
      have := Γ_theorem (l313 subst.2 nocc.1 nocc.2) Δ
      have mem' := MCS_pf mcs (Γ_mp this (Γ_premise mem))
      have has_wit := wit mem'
      simp [subst_nom, y_ne_x] at has_wit ⊢
      admit
  . trivial

-- ◇ (((ex x, ψ)⟶ψ[y//x])⋀φ)
-- ◇ ((ex x, ψ⟶ψ[i//x])⋀φ)

def witness_conditionals (enum : ℕ → Form N) (n : ℕ) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : ∃ (l : List (Form N)), l ≠ [] ∧ ◇conjunction' l ∈ Δ :=
  match n with
  | 0   => by exists [φ]; simp only [ne_eq, not_false_eq_true, conjunction', true_and, mem]
  | n+1 => by
           let ⟨prev_l, prev_nnil, prev_mem⟩ := witness_conditionals enum n mcs wit mem
           let ψ_n := enum n
           have := l313' mcs wit prev_mem ψ_n
           match ψ_n with
           | ex x, ψ_n  =>
              let ⟨i_n, curr_mem⟩ := this
              exact ⟨((ex x, ψ_n) ⟶ ψ_n[i_n//x]) :: prev_l, by simp, by rw [conjunction']; exact curr_mem; exact prev_nnil⟩
           | _        => exact ⟨prev_l, prev_nnil, prev_mem⟩

def succesor_set' (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : Set (Form N) :=
  {ψ | □ψ ∈ Δ} ∪ {φ | ∃ n : ℕ, φ ∈ (witness_conditionals enum n mcs wit mem).choose}



/-
def Set.has_wit_of (Γ : Set (Form N)) : Form → Prop
  | ex x, φ => ∃ (i : NOM), (ex x, φ ⟶ φ[i//x]) ∈ Γ
  | _       => True

def Set.list_wit {Γ : Set (Form N)} (enum : ℕ → Form N) (n : ℕ) (h : ∀ i : ℕ, i < n → Γ.has_wit_of (enum i)) : List (Form N) :=
  match n with
  | 0   =>    []
  | n+1 =>    sorry

theorem set_family (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : Δ.MCS) (wit : Δ.witnessed) (mem : ◇φ ∈ Δ) :
  (n : ℕ) → (∃ Γ : Set (Form N), Canonical.R Δ Γ ∧ φ ∈ Γ ∧ ∀ i : ℕ, i < n → Γ.has_wit_of (enum i))
  | 0     => by
      let Γ₀ := {φ} ∪ {ψ | □ψ ∈ Δ}
      have : Γ₀.consistent := by admit
      have ⟨Γ₀', incl, l_mcs⟩ := RegularLindenbaumLemma Γ₀ this
      exists Γ₀'
      apply And.intro
      . simp only [Canonical, restrict_by, mcs, l_mcs, true_and]
        intro φ mem
        apply incl; apply Or.inr; simp
        exact mem
      . simp; apply incl; simp
  | n+1   => by
      have ⟨Γ_ih, ⟨R_ih, ⟨mem_ih, wit_ih⟩⟩⟩ := set_family enum mcs wit mem n
      admit

def succesor_set (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : Δ.MCS) (wit : Δ.witnessed) (mem : ◇φ ∈ Δ) : Set (Form N) :=
  {φ | ∃ n : ℕ, φ ∈ (set_family enum mcs wit mem n).choose}
-/
