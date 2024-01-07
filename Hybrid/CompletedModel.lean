import Hybrid.ProofUtils
import Hybrid.Truth
import Hybrid.Soundness
-- Interface for proofs to be filled
-- about renaming bound vars:
import Hybrid.RenameBound

open Classical

def restrict_by : (Set (Form N) → Prop) → (Set (Form N) → Set (Form N) → Prop) → (Set (Form N) → Set (Form N) → Prop) :=
  λ restriction => λ R => λ Γ => λ Δ => restriction Γ ∧ restriction Δ ∧ R Γ Δ

theorem path_conj {R : α → Prop} : path (λ a b => R a ∧ R b) a b n → (R a → R b) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro ⟨_, h⟩ _
      exact h.1.2

theorem path_restr : path (restrict_by R₁ R₂) Γ Δ n → path R₂ Γ Δ n := by
  simp only [restrict_by]
  induction n generalizing Δ with
  | zero => simp only [path, imp_self]
  | succ n ih =>
      simp only [path]
      intro ⟨Θ, ⟨⟨_, _, h1⟩, h2⟩⟩
      exists Θ
      apply And.intro
      assumption
      apply ih
      assumption

theorem path_restr' : path (restrict_by R₁ R₂) Γ Δ n → (R₁ Γ → R₁ Δ) := by
  simp only [restrict_by]
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro ⟨_, h⟩ _
      exact h.1.2.1

structure GeneralModel (N : Set ℕ) where
  W : Type
  R : W → W  → Prop
  Vₚ: PROP   → Set W
  Vₙ: NOM N  → Set W

def GeneralI (W : Type) := SVAR → Set W

def Canonical : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := restrict_by MCS (λ Γ => λ Δ => (∀ {φ : Form TotalSet}, □φ ∈ Γ → φ ∈ Δ))
--  R := λ Γ => λ Δ => Γ.MCS ∧ Δ.MCS ∧ (∀ φ : Form, □φ ∈ Γ → φ ∈ Δ)
  Vₚ:= λ p => {Γ | MCS Γ ∧ ↑p ∈ Γ}
  Vₙ:= λ i => {Γ | MCS Γ ∧ ↑i ∈ Γ}

def CanonicalI : SVAR → Set (Set (Form TotalSet)) := λ x => {Γ | MCS Γ ∧ ↑x ∈ Γ}

instance : Membership (Form TotalSet) Canonical.W := ⟨Set.Mem⟩

theorem R_nec : □φ ∈ Γ → Canonical.R Γ Δ → φ ∈ Δ := by
  intro h1 h2
  simp only [Canonical, restrict_by] at h2
  apply h2.right.right
  assumption

theorem R_pos : Canonical.R Γ Δ ↔ (MCS Γ ∧ MCS Δ ∧ ∀ {φ}, (φ ∈ Δ → ◇φ ∈ Γ)) := by
  simp only [Canonical, restrict_by]
  apply Iff.intro
  . intro ⟨h1, h2, h3⟩
    simp only [*, true_and]
    intro φ φ_mem
    rw [←(@not_not (◇φ ∈ Γ))]
    intro habs
    have ⟨habs, _⟩ := not_forall.mp (h1.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [←Form.neg, Form.diamond] at habs
    have habs : ∼φ ∈ Δ := by
      apply h3
      apply Proof.MCS_pf h1
      apply Proof.Γ_mp
      apply Proof.Γ_theorem
      apply Proof.tautology
      apply dne
      assumption
    unfold MCS consistent at h1 h2
    apply h2.left
    apply Proof.Γ_mp
    repeat (apply Proof.Γ_premise; assumption)
  . intro ⟨h1, h2, h3⟩
    simp only [*, true_and]
    intro φ φ_mem
    rw [←(@not_not (φ ∈ Δ))]
    intro habs
    have ⟨habs, _⟩ := not_forall.mp (h2.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [←Form.neg] at habs
    have habs : ◇∼φ ∈ Γ := by
      apply h3
      apply Proof.MCS_pf h2
      assumption
    unfold MCS consistent at h1 h2
    apply h1.left
    apply Proof.Γ_mp
    apply Proof.Γ_premise
    assumption
    apply Proof.Γ_mp
    apply Proof.Γ_theorem
    apply Proof.mp
    apply Proof.tautology
    apply iff_elim_l
    apply Proof.dn_nec
    apply Proof.Γ_premise
    assumption

theorem R_iter_nec (n : ℕ) : (iterate_nec n φ) ∈ Γ → path Canonical.R Γ Δ n → φ ∈ Δ := by
  intro h1 h2
  induction n generalizing φ Δ with
  | zero =>
      simp only [iterate_nec, iterate_nec.loop, path] at h1 h2
      rw [←h2]
      assumption
  | succ n ih =>
      simp only [path, iter_nec_succ] at ih h1 h2
      have ⟨Κ, hk1, hk2⟩ := h2
      apply R_nec
      exact (ih h1 hk2)
      assumption

theorem R_iter_pos (n : ℕ) : path Canonical.R Γ Δ n → ∀ {φ}, (φ ∈ Δ → (iterate_pos n φ) ∈ Γ) := by
  intro h1 φ h2
  induction n generalizing φ Δ with
  | zero =>
      simp [path, iterate_pos, iterate_pos.loop] at h1 ⊢
      rw [h1]
      assumption
  | succ n ih =>
      simp only [path, iter_pos_succ] at ih h1 ⊢
      have ⟨Κ, hk1, hk2⟩ := h1
      rw [R_pos] at hk1
      apply ih hk2
      exact hk1.right.right h2

theorem restrict_R_iter_nec {n : ℕ} : (iterate_nec n φ) ∈ Γ → path (restrict_by R Canonical.R) Γ Δ n → φ ∈ Δ := by
  intro h1 h2
  apply R_iter_nec
  assumption
  apply path_restr
  assumption

theorem restrict_R_iter_pos {n : ℕ} : path (restrict_by R Canonical.R) Γ Δ n → ∀ {φ}, (φ ∈ Δ → (iterate_pos n φ) ∈ Γ) := by
  intro h1 φ h2
  apply R_iter_pos
  apply path_restr
  repeat assumption

-- implicitly we mean generated submodels *of the canonical model*
def Set.GeneratedSubmodel (Θ : Set (Form TotalSet)) (restriction : Set (Form TotalSet) → Prop) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := λ Γ => λ Δ =>
    (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧
    (∃ m, path (restrict_by restriction Canonical.R) Θ Δ m) ∧
    Canonical.R Γ Δ
  Vₚ:= λ p => {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₚ p}
  Vₙ:= λ i => {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₙ i}

def Set.GeneratedSubI (Θ : Set (Form TotalSet)) (restriction : Set (Form TotalSet) → Prop) : GeneralI (Set (Form TotalSet)) := λ x =>
  {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ CanonicalI x}

theorem submodel_canonical_path (Θ : Set (Form TotalSet)) (r : Set (Form TotalSet) → Prop) (rt : r Θ) : path (Θ.GeneratedSubmodel r).R Γ Δ n → path (restrict_by r Canonical.R) Γ Δ n := by
  intro h
  induction n generalizing Γ Δ with
  | zero =>
      simp [path] at h ⊢
      exact h
  | succ n ih =>
      have ⟨Η, ⟨h1, h2⟩⟩ := h
      have := ih h2
      clear h h2
      exists Η
      apply And.intro
      . simp [Set.GeneratedSubmodel] at h1
        have ⟨⟨n, l1⟩, ⟨⟨m, l2⟩, l3⟩⟩ := h1
        simp [restrict_by, l3]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption
      . exact this

theorem path_root (Θ : Set (Form TotalSet)) (r : Set (Form TotalSet) → Prop) : path (restrict_by r Canonical.R) Θ Γ n → path (Θ.GeneratedSubmodel r).R Θ Γ n := by
  induction n generalizing Θ Γ with
  | zero => simp [path]
  | succ n ih =>
      simp only [path]
      intro ⟨Δ, ⟨h1, h2⟩⟩
      exists Δ
      apply And.intro
      . simp [Set.GeneratedSubmodel]
        apply And.intro
        . exists n
        . apply And.intro
          . exists (n+1)
            simp [path]
            exists Δ
          . exact h1.2.2
      . apply ih
        exact h2

def WitnessedModel {Θ : Set (Form TotalSet)} (_ : MCS Θ) (_ : witnessed Θ) : GeneralModel TotalSet := Θ.GeneratedSubmodel witnessed
def WitnessedI {Θ : Set (Form TotalSet)} (_ : MCS Θ) (_ : witnessed Θ) : GeneralI (Set (Form TotalSet)) := Θ.GeneratedSubI witnessed

def CompletedModel {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := λ Γ => λ Δ => ((WitnessedModel mcs wit).R Γ Δ) ∨ (Γ = {Form.bttm} ∧ Δ = Θ)
  Vₚ:= λ p => (WitnessedModel mcs wit).Vₚ p
  Vₙ:= λ i => if (WitnessedModel mcs wit).Vₙ i ≠ ∅
              then  (WitnessedModel mcs wit).Vₙ i
              else { {Form.bttm} }
def CompletedI {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : GeneralI (Set (Form TotalSet)) := λ x =>
  if (WitnessedI mcs wit) x ≠ ∅
              then  (WitnessedI mcs wit) x
              else { {Form.bttm} }

-- Lemma 3.11, Blackburn 1998, pg. 637
lemma subsingleton_valuation : ∀ {Θ : Set (Form TotalSet)} {R : Set (Form TotalSet) → Prop} (i : NOM TotalSet), MCS Θ → ((Θ.GeneratedSubmodel R).Vₙ i).Subsingleton := by
  -- the hypothesis MCS Θ is not necessary
  --  but to prove the theorem without it would complicate
  --  the code, and anyway, we'll only ever use MCS-generated submodels
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Θ restr i Θ_MCS Γ ⟨⟨n, h1⟩, ⟨Γ_MCS, Γ_i⟩⟩  Δ ⟨⟨m, h2⟩, ⟨Δ_MCS, Δ_i⟩⟩
  simp only [Set.GeneratedSubmodel] at Γ Δ ⊢
  rw [←(@not_not (Γ = Δ))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro ⟨φ, h⟩
  apply Or.elim h
  . clear h
    intro ⟨h3, h4⟩
    apply h4
    have := restrict_R_iter_pos h1 ((Proof.MCS_conj Γ_MCS i φ).mp ⟨Γ_i, h3⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance i n m)) this
    have := restrict_R_iter_nec this h2
    apply Proof.MCS_mp
    repeat assumption
  . clear h
    intro ⟨h3, h4⟩
    apply h3
    have := restrict_R_iter_pos h2 ((Proof.MCS_conj Δ_MCS i φ).mp ⟨Δ_i, h4⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance i m n)) this
    have := restrict_R_iter_nec this h1
    apply Proof.MCS_mp
    repeat assumption

lemma subsingleton_i : ∀ {Θ : Set (Form TotalSet)} {R : Set (Form TotalSet) → Prop} (x : SVAR), MCS Θ → ((Θ.GeneratedSubI R) x).Subsingleton := by
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Θ restr x Θ_MCS Γ ⟨⟨n, h1⟩, ⟨Γ_MCS, Γ_i⟩⟩  Δ ⟨⟨m, h2⟩, ⟨Δ_MCS, Δ_i⟩⟩
  rw [←(@not_not (Γ = Δ))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro ⟨φ, h⟩
  apply Or.elim h
  . clear h
    intro ⟨h3, h4⟩
    apply h4
    have := restrict_R_iter_pos h1 ((Proof.MCS_conj Γ_MCS x φ).mp ⟨Γ_i, h3⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance' x n m)) this
    have := restrict_R_iter_nec this h2
    apply Proof.MCS_mp
    repeat assumption
  . clear h
    intro ⟨h3, h4⟩
    apply h3
    have := restrict_R_iter_pos h2 ((Proof.MCS_conj Δ_MCS x φ).mp ⟨Δ_i, h4⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance' x m n)) this
    have := restrict_R_iter_nec this h1
    apply Proof.MCS_mp
    repeat assumption

lemma wit_subsingleton_valuation {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (i : NOM TotalSet) : ((WitnessedModel mcs wit).Vₙ i).Subsingleton := by
  rw [WitnessedModel]
  apply subsingleton_valuation
  assumption

lemma wit_subsingleton_i {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (x : SVAR) : ((WitnessedI mcs wit) x).Subsingleton := by
  rw [WitnessedI]
  apply subsingleton_i
  assumption

lemma completed_singleton_valuation {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (i : NOM TotalSet) : ∃ Γ : Set (Form TotalSet), (CompletedModel mcs wit).Vₙ i = {Γ} := by
  simp [CompletedModel]
  split
  . simp
  . next h =>
      rw [←ne_eq, ←Set.nonempty_iff_ne_empty, Set.nonempty_def] at h
      match h with
      | ⟨Γ, h⟩ =>
          exists Γ
          apply (Set.subsingleton_iff_singleton h).mp
          apply wit_subsingleton_valuation

lemma completed_singleton_i {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (x : SVAR) : ∃ Γ : Set (Form TotalSet), (CompletedI mcs wit) x = {Γ} := by
  simp [CompletedI]
  split
  . simp
  . next h =>
      rw [←ne_eq, ←Set.nonempty_iff_ne_empty, Set.nonempty_def] at h
      match h with
      | ⟨Γ, h⟩ =>
          exists Γ
          apply (Set.subsingleton_iff_singleton h).mp
          apply wit_subsingleton_i

def Set.MCS_in (Γ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Prop := ∃ n, path (WitnessedModel mcs wit).R Θ Γ n

theorem mcs_in_prop {Γ Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Γ.MCS_in mcs wit → (MCS Γ ∧ witnessed Γ) := by
  intro ⟨n, h⟩
  cases n with
  | zero =>
      simp [path] at h
      simp [←h, mcs, wit]
  | succ n =>
      have ⟨Δ, h1, h2⟩ := h
      clear h2
      simp [WitnessedModel, Set.GeneratedSubmodel, Canonical] at h1
      have ⟨h3, ⟨m, h4⟩, h5⟩ := h1
      clear h1 h3
      simp [h5.2.1]
      apply path_restr' h4
      exact wit

theorem mcs_in_wit {Γ Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Γ.MCS_in mcs wit → (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) := by
  intro ⟨n, h⟩
  exists n
  cases n with
  | zero =>
      simp [path] at h ⊢
      exact h
  | succ n =>
      simp [path]
      have ⟨Δ, h1, h2⟩ := h
      exists Δ
      apply And.intro
      . apply submodel_canonical_path
        repeat assumption
      . have ⟨⟨_, l⟩, ⟨⟨_, r1⟩, r2⟩⟩ := h1
        simp [restrict_by, r2]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption

def needs_dummy {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := (∃ i, ((CompletedModel mcs wit).Vₙ i) = { (Set.singleton Form.bttm) }) ∨
                                                                                 (∃ x, ((CompletedI mcs wit) x) = { (Set.singleton Form.bttm) })

def Set.is_dummy (Γ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := needs_dummy mcs wit ∧ Γ = {Form.bttm}


theorem choose_subtype {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)  : ((completed_singleton_valuation mcs wit i).choose.MCS_in mcs wit) ∨ (completed_singleton_valuation mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (λ Γ => (Set.MCS_in Γ mcs wit) ∨ (Set.is_dummy Γ mcs wit))
  intro Γ h
  simp [CompletedModel, WitnessedModel, Set.GeneratedSubmodel] at h
  split at h
  . next c =>
      apply Or.inr
      apply And.intro
      . apply Or.inl
        exists i
        simp [CompletedModel, WitnessedModel, Set.GeneratedSubmodel, c]
        apply Eq.refl
      . apply Eq.symm
        simp at h
        exact h
  . apply Or.inl
    have Γ_mem : Γ ∈ {Γ | (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) ∧ Γ ∈ GeneralModel.Vₙ Canonical i} := by simp [h]
    simp at Γ_mem
    have ⟨⟨n, pth⟩, _⟩ := Γ_mem
    simp [Set.MCS_in, WitnessedModel]
    exists n
    apply path_root
    exact pth

theorem choose_subtype' {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : ((completed_singleton_i mcs wit i).choose.MCS_in mcs wit) ∨ (completed_singleton_i mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (λ Γ => (Set.MCS_in Γ mcs wit) ∨ (Set.is_dummy Γ mcs wit))
  intro Γ h
  simp [CompletedI, WitnessedI, Set.GeneratedSubI] at h
  split at h
  . next c =>
      apply Or.inr
      apply And.intro
      . apply Or.inr
        exists i
        simp [CompletedI, WitnessedI, Set.GeneratedSubI, c]
        apply Eq.refl
      . apply Eq.symm
        simp at h
        exact h
  . apply Or.inl
    have Γ_mem : Γ ∈ {Γ | (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) ∧ Γ ∈ CanonicalI i} := by simp [h]
    simp at Γ_mem
    have ⟨⟨n, pth⟩, _⟩ := Γ_mem
    simp [Set.MCS_in, WitnessedModel]
    exists n
    apply path_root
    exact pth


-- pg. 638: "we only glue on a dummy state when we are forced to"
--    we define the set of states as Γ.MCS_in ∨ Γ.is_dummy
--    where is_dummy contains the assumption that we are *forced*
--    to glue a dummy
noncomputable def StandardCompletedModel {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Model TotalSet :=
    ⟨{Γ : Set (Form TotalSet) // Γ.MCS_in mcs wit ∨ Γ.is_dummy mcs wit},
      λ Γ => λ Δ => (CompletedModel mcs wit).R Γ.1 Δ.1,
      λ p => {Γ | Γ.1 ∈ ((CompletedModel mcs wit).Vₚ p)},
      λ i => ⟨(completed_singleton_valuation mcs wit i).choose, choose_subtype mcs wit⟩⟩

noncomputable def StandardCompletedI {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : I (StandardCompletedModel mcs wit).W :=
    λ x => ⟨(completed_singleton_i mcs wit x).choose, choose_subtype' mcs wit⟩

theorem sat_dual_all_ex : ((M,s,g) ⊨ (all x, φ)) ↔ (M,s,g) ⊨ ∼(ex x, ∼φ) := by
  apply Iff.intro
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    simp only [Form.bind_dual, neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    have := h g' var
    simp only [Form.bind_dual, neg_sat, not_not] at this
    exact this

theorem sat_dual_nec_pos : ((M,s,g) ⊨ (□ φ)) ↔ (M,s,g) ⊨ ∼(◇ ∼φ) := by
  apply Iff.intro
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro _ _
    simp only [neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro s' r
    have := h s' r
    simp only [neg_sat, not_not] at this
    exact this

@[simp]
def coe (Δ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (h : Δ.MCS_in mcs wit) : (StandardCompletedModel mcs wit).W := ⟨Δ, Or.inl h⟩

def statement (φ : Form TotalSet) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := ∀ {Δ : Set (Form TotalSet)}, (h : Δ.MCS_in mcs wit) → φ ∈ Δ ↔ (StandardCompletedModel mcs wit, coe Δ mcs wit h, StandardCompletedI mcs wit) ⊨ φ


lemma truth_bttm : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement ⊥ mcs wit) := by
  intro _ mcs' wit' Δ h
  have := (mcs_in_prop mcs' wit' h).1
  apply Iff.intro
  . intro h
    exact this.1 (Proof.Γ_premise h)
  . simp

lemma truth_prop : ∀ {Θ : Set (Form TotalSet)} {p : PROP}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement p mcs wit) := by
  intro Θ  _ mcs wit Δ h
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h)
  apply Iff.intro
  . intro hl
    apply And.intro
    . apply mcs_in_wit
      exact h
    . simp [Canonical, hl, D_mcs]
  . simp [StandardCompletedModel, CompletedModel, WitnessedModel, Set.GeneratedSubmodel, restrict_by, Canonical, -implication_disjunction]
    intros
    assumption

lemma truth_nom_help : ∀ {Θ : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Θ) → (wit : witnessed Θ) → ∀ {Δ : Set (Form TotalSet)}, Δ.MCS_in mcs wit → (↑i ∈ Δ ↔ ((StandardCompletedModel mcs wit).Vₙ ↑i).1 = Δ) := by
  intro Θ i mcs wit Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedModel, CompletedModel, WitnessedModel]
  apply Iff.intro
  . intro h
    apply choice_intro (λ Γ : Set (Form TotalSet) => Γ = Δ)
    intro Η eta_eq
    have delta_mem : Δ ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by
      simp [Set.GeneratedSubmodel, WitnessedModel] at h_in ⊢
      apply And.intro
      . have ⟨n, h_in⟩ := h_in
        exists n
        exact submodel_canonical_path Θ witnessed wit h_in
      . simp [Canonical, h, D_mcs]
    split at eta_eq
    . next fls =>
        exfalso
        rw [←@not_not (((Θ.GeneratedSubmodel witnessed).Vₙ i) = ∅), ←Ne,
          ←Set.nonempty_iff_ne_empty, Set.nonempty_def, not_exists] at fls
        apply fls Δ
        exact delta_mem
    . have eta_mem : Η ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by simp [eta_eq]
      apply subsingleton_valuation i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [←h] at h_in D_mcs ⊢
    clear h
    apply choice_intro (λ Γ : Set (Form TotalSet) => ↑i ∈ Γ)
    intro Η eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (λ Γ => Γ ⊢ ⊥)
        intro _ a
        simp [fls, Set.eq_singleton_iff_unique_mem] at a
        apply Proof.Γ_premise
        exact a.left.left
    . have eta_mem : Η ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by simp [eta_eq]
      simp [Set.GeneratedSubmodel, Canonical] at eta_mem
      exact eta_mem.left.right

lemma truth_svar_help : ∀ {Θ : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Θ) → (wit : witnessed Θ) → ∀ {Δ : Set (Form TotalSet)}, Δ.MCS_in mcs wit → (↑i ∈ Δ ↔ (StandardCompletedI mcs wit ↑i).1 = Δ) := by
  intro Θ i mcs wit Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedI, CompletedI, WitnessedI]
  apply Iff.intro
  . intro h
    apply choice_intro (λ Γ : Set (Form TotalSet) => Γ = Δ)
    intro Η eta_eq
    have delta_mem : Δ ∈ Θ.GeneratedSubI witnessed i := by
      simp [Set.GeneratedSubI, WitnessedI] at h_in ⊢
      apply And.intro
      . have ⟨n, h_in⟩ := h_in
        exists n
        exact submodel_canonical_path Θ witnessed wit h_in
      . simp [CanonicalI, h, D_mcs]
    split at eta_eq
    . next fls =>
        exfalso
        rw [←@not_not ((Θ.GeneratedSubI witnessed i) = ∅), ←Ne,
          ←Set.nonempty_iff_ne_empty, Set.nonempty_def, not_exists] at fls
        apply fls Δ
        exact delta_mem
    . have eta_mem : Η ∈ Θ.GeneratedSubI witnessed i := by simp [eta_eq]
      apply subsingleton_i i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [←h] at h_in D_mcs ⊢
    clear h
    apply choice_intro (λ Γ : Set (Form TotalSet) => ↑i ∈ Γ)
    intro Η eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (λ Γ => Γ ⊢ ⊥)
        intro _ a
        simp [fls, Set.eq_singleton_iff_unique_mem] at a
        apply Proof.Γ_premise
        exact a.left.left
    . have eta_mem : Η ∈ Θ.GeneratedSubI witnessed i := by simp [eta_eq]
      simp [Set.GeneratedSubI, CanonicalI] at eta_mem
      exact eta_mem.right.right

lemma truth_nom : ∀ {Θ : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement i mcs wit) := by
  intro Θ i mcs wit Δ h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_nom_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_nom_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_svar : ∀ {Θ : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement i mcs wit) := by
  intro Θ i mcs wit Δ h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_svar_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_svar_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_impl : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement φ mcs wit) → (statement ψ mcs wit) → statement (φ ⟶ ψ) mcs wit := by
  intro Θ mcs wit ih_φ ih_ψ Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  apply Iff.intro
  . intro h1 h2
    apply (ih_ψ h_in).mp
    apply Proof.MCS_mp
    repeat assumption
    exact (ih_φ h_in).mpr h2
  . intro sat_φ_ψ
    unfold statement at ih_φ ih_ψ
    rw [Sat, ←ih_φ, ←ih_ψ, Proof.MCS_impl] at sat_φ_ψ
    repeat assumption

lemma has_state_symbol (s : (StandardCompletedModel mcs wit).W) : (∃ i, (StandardCompletedModel mcs wit).Vₙ i = s) ∨ (∃ x, StandardCompletedI mcs wit x = s) := by
  apply Or.elim s.2
  . intro s_in
    apply Or.inl
    have ⟨s_mcs, s_wit⟩ := (mcs_in_prop mcs wit s_in)
    have ⟨i, sat_i⟩ := Proof.MCS_rich s_mcs s_wit
    simp [truth_nom mcs wit s_in] at sat_i
    exists i
    apply Eq.symm
    exact sat_i
  -- absolutely unnecesarily ugly, but at least it works
  . intro ⟨needs_dummy, s_is_dummy⟩
    have : s.1 = Set.singleton Form.bttm := by simp [s_is_dummy]; apply Eq.refl
    rw [needs_dummy, ←this] at needs_dummy
    clear this
    apply Or.elim needs_dummy
    . intro ⟨i, h⟩
      apply Or.inl
      exists i
      simp [StandardCompletedModel]
      apply Subtype.eq
      apply choice_intro (λ Γ => Γ = s.1)
      rw [h,]
      intro s' eq
      rw [←Set.singleton_eq_singleton_iff]
      apply Eq.symm
      exact eq
    . intro ⟨i, h⟩
      apply Or.inr
      exists i
      simp [StandardCompletedI]
      apply Subtype.eq
      apply choice_intro (λ Γ => Γ = s.1)
      rw [h]
      intro s' eq
      rw [←Set.singleton_eq_singleton_iff]
      apply Eq.symm
      exact eq

lemma truth_ex : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (∀ {χ : Form TotalSet}, χ.depth < (ex x, ψ).depth → statement χ mcs wit) → statement (ex x, ψ) mcs wit := by
  intro Θ mcs wit ih
  intro Δ Δ_in
  have ⟨Δ_mcs, Δ_wit⟩ := (mcs_in_prop mcs wit Δ_in)
  apply Iff.intro
  . intro h
    have ⟨i, mem⟩ := Δ_wit h
    have ih_s := @ih (ψ[i//x]) subst_depth''
    rw [ih_s Δ_in] at mem
    apply WeakSoundness Proof.ax_q2_contrap
    exact mem
  . simp only [ex_sat]
    intro ⟨g', g'_var, g'_ψ⟩
    let s := g' x
    apply Or.elim (has_state_symbol s)
    . intro ⟨i, sat_i⟩
      have ih_s := @ih (ψ[i//x]) subst_depth''
      simp at sat_i
      rw [←nom_substitution (is_variant_symm.mp g'_var) (Eq.symm sat_i), ←ih_s] at g'_ψ
      have g'_ψ := Proof.Γ_premise g'_ψ
      clear g'_var sat_i
      apply Proof.MCS_pf Δ_mcs
      apply Proof.Γ_mp
      . apply Proof.Γ_theorem
        apply Proof.ax_q2_contrap
        exact i
      . exact g'_ψ
    . intro ⟨y, sat_y⟩
      simp at sat_y
      have := rename_all_bound ψ y (StandardCompletedModel mcs wit) (coe Δ mcs wit Δ_in) g'
      rw [iff_sat] at this
      rw [this] at g'_ψ
      clear this
      rw [←svar_substitution (substable_after_replace ψ) (is_variant_symm.mp g'_var) (Eq.symm sat_y)] at g'_ψ
      have r_ih := @ih ((ψ.replace_bound y)[y//x]) replace_bound_depth'
      rw [←r_ih] at g'_ψ
      have := Proof.MCS_with_svar_witness (substable_after_replace ψ) Δ_mcs g'_ψ
      apply Proof.MCS_mp Δ_mcs; apply Proof.MCS_thm Δ_mcs
    --  exact @exists_replace x ψ y
      apply exists_replace; exact y; exact this
