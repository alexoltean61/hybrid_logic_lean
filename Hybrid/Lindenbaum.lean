import Hybrid.Substitutions
import Hybrid.ProofUtils
import Hybrid.FormCountable

open Classical

-- First, we define how to obtain Γᵢ₊₁ from Γᵢ, given a formula φ:
def lindenbaum_next (Γ : Set (Form N)) (φ : Form N) : Set (Form N) :=
  if consistent (Γ ∪ {φ}) then
    match φ with
    | ex x, ψ =>
        if c : ∃ i : NOM N, all_nocc i (Γ ∪ {φ}) then
          Γ ∪ {φ} ∪ {ψ[c.choose // x]}
        else
          Γ ∪ {φ}
    | _       =>  Γ ∪ {φ}
  else
    Γ

-- Now we define the whole indexed family Γᵢ.
-- Usually, the enumeration of formulas starts from 1 (φ₁, φ₂, ...), and
--    Γ₀ = Γ .
-- However, in Lean it's much tidier to enumerate from 0 (φ₀, φ₁, ...), so
--    Γ₀ = Γ ∪ {φ₀} if it is consistent and Γ₀ = Γ otherwise.
def lindenbaum_family (enum : Nat → Form N) (Γ : Set (Form N)) : Nat → Set (Form N)
| .zero   => lindenbaum_next Γ (enum 0)
| .succ n =>
    let prev_set := lindenbaum_family enum Γ n
    lindenbaum_next prev_set (enum (n+1))

notation Γ "(" i "," e ")" => lindenbaum_family e Γ i

def LindenbaumMCS (enum : Nat → Form N) (Γ : Set (Form N)) (_ : consistent Γ) : Set (Form N) :=
    {φ | ∃ i : Nat, φ ∈ Γ (i, enum)}

-- Lemma: All Γᵢ belong to LindenbaumMCS Γ
lemma all_sets_in_family{enum : ℕ → Form N} {Γ : Set (Form N)} {c : consistent Γ} : ∀ n, Γ (n, enum) ⊆ LindenbaumMCS enum Γ c := by
  intro i φ h
  exists i

lemma all_sets_in_family_tollens {enum : ℕ → Form N} {Γ : Set (Form N)} {c : consistent Γ} : φ ∉ (LindenbaumMCS enum Γ c) → ∀ n, φ ∉ Γ (n, enum) := by
  rw [contraposition, not_not, not_forall]
  intro h
  let ⟨i, hi⟩ := h
  rw [not_not] at hi
  exact all_sets_in_family i hi

-- Lemma: If Γ is consistent, then for all φ, lindenbaum_next Γ φ is consistent
lemma consistent_lindenbaum_next (Γ : Set (Form N)) (hc : consistent Γ) (φ : Form N) : consistent (lindenbaum_next Γ φ) := by
  rw [lindenbaum_next]
  split
  . split
    . next x ψ h =>
      split
      . next hnom =>
        let i := Exists.choose hnom
        have not1 : i = Exists.choose hnom := by simp
        have i_sat := Exists.choose_spec hnom
        have not2 : (ex x, ψ) = ((all x, ψ⟶⊥)⟶⊥) := by simp
        rw [←not1, ←not2, consistent]
        intro hyp
        have ⟨L, habs⟩ := Proof.Deduction.mpr hyp
        let χ := conjunction (Γ ∪ {ex x, ψ}) L
        have not3 : χ = conjunction (Γ ∪ {ex x, ψ}) L := by simp
        rw [←not3] at habs
        let y := (χ⟶ψ).new_var
        have y_ge : y ≥ (χ⟶ψ).new_var := by simp [SVAR.le]
        have : y ≥ (χ⟶(ψ[i//x])⟶⊥).new_var := ge_new_var_subst_helpr y_ge
        have habs := (Proof.generalize_constants i this) habs
        rw [nom_subst_svar, nom_subst_svar] at habs
        have nocc0 : occurs y χ = false := by apply ge_new_var_is_new; exact (new_var_geq1 y_ge).left
        have nocc1 : nom_occurs i χ = false := all_noc_conj i_sat L
        conv at i_sat =>
          rw [←not1, ←not2, all_nocc, Set.union_singleton]
          intro φ; rw [Set.mem_insert_iff]
        have nocc2 : nom_occurs i (ex x, ψ) = false := by apply (i_sat (ex x, ψ)); simp
        simp only [nom_occurs, or_false, Bool.or_false, ←not1] at nocc2
        rw [nom_subst_nocc nocc1, subst_collect_all_nocc nocc2] at habs
        have := Proof.ax_q1 χ (ψ[y//x]⟶⊥) (notoccurs_notfree nocc0)
        have habs := Proof.mp this habs
        have habs : Σ L, ⊢(conjunction (Γ ∪ {ex x, ψ}) L⟶all y, ψ[y//x]⟶⊥) := ⟨L, habs⟩
        rw [←SyntacticConsequence, ←Form.neg] at habs
        have : ⊢((all y, ∼(ψ[y//x])) ⟶ (all x, ∼ψ)) := by
          apply Proof.iff_mpr
          apply Proof.rename_bound
          apply ge_new_var_is_new
          rw [new_var_neg]
          exact (new_var_geq1 y_ge).right
          rw [subst_neg]
          apply new_var_subst'' (new_var_geq1 y_ge).right
        have := Proof.Γ_theorem this (Γ ∪ {ex x, ψ})
        have habs := Proof.Γ_mp this habs
        have : (Γ ∪ {ex x, ψ}) ⊢ (ex x, ψ) := by apply Proof.Γ_premise; simp
        have := Proof.Γ_mp this habs
        exact h this
      . assumption
    . assumption
  . assumption


-- Lemma: If you can consistently extend (lindenbaum_next Γ φ) with φ, then
--    φ already belongs to (lindenbaum_next Γ φ)
lemma maximal_lindenbaum_next {Γ : Set (Form N)} (hc : consistent ((lindenbaum_next Γ φ) ∪ {φ})) : φ ∈ lindenbaum_next Γ φ := by
  revert hc
  rw [lindenbaum_next]
  split
  . split
    . split <;> simp
    . intro; simp
  . intro; contradiction

--
-- Now apply the previous lemmas to the family as a whole.
--

-- Lemma: If Γ is consistent, then all Γᵢ are consistent.
lemma consistent_family {Γ : Set (Form N)} (e : ℕ → Form N) (c : consistent Γ) : ∀ n, consistent (Γ (n, e)) := by
  intro n
  induction n <;> (
      simp only [lindenbaum_family]
      apply consistent_lindenbaum_next
      assumption
  )

-- Lemma: If φ doesn't belong to the set in the family corresponding to its place in the enumeration,
--     (i.e., φ ∉ Γᵢ, where i = f φ),
--    then Γᵢ ∪ {φ} must be inconsistent.
lemma maximal_family {Γ : Set (Form N)} {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun) :
    ¬φ ∈ Γ (f φ, e) → ¬consistent (Γ (f φ, e) ∪ {φ}) := by
    rw [contraposition, not_not, not_not]
    unfold lindenbaum_family
    cases heq : f φ with
    | zero =>
        simp only
        have by_inv : e (f φ) = φ := by simp [f.leftInverse_invFun f_inj φ, e_inv]
        rw [show 0 = f φ by simp [heq], by_inv]
        intro h
        rw [lindenbaum_next]
        apply maximal_lindenbaum_next
        exact h
    | succ n =>
        simp only
        have by_inv : e (f φ) = φ := by simp [f.leftInverse_invFun f_inj φ, e_inv]
        simp only [show (n+1) = f φ by simp [heq], by_inv]
        intro h
        rw [lindenbaum_next]
        apply maximal_lindenbaum_next
        exact h

-- todo: Include here that Γ ⊆ Γᵢ for all i
lemma increasing_family : i ≤ j → Γ (i, e) ⊆ Γ (j, e) := by
  intro h
  induction h with
  | refl => simp [subset_of_eq]
  | @step m _ ih =>
      simp only [lindenbaum_family, lindenbaum_next]
      split
      . intro _ φ_member
        have incl : Γ(m, e) ⊆ (Γ(m, e) ∪ {e (m + 1)}) := by simp
        split ; split
        . rw [Set.union_singleton]
          apply Set.subset_insert
          exact incl (ih φ_member)
        . exact incl (ih φ_member)
        . exact incl (ih φ_member)
      . assumption

lemma Γ_in_family : Γ ⊆ Γ (i, e) := by
  induction i with
  | zero =>
      simp only [lindenbaum_family, lindenbaum_next]
      split ; split ; split
      . apply subset_trans
        have : Γ ⊆ Γ ∪ {e 0} := by simp
        exact this
        simp
      . simp
      . simp
      . apply subset_of_eq
        simp
  | succ n ih =>
      apply subset_trans
      apply ih
      apply increasing_family
      apply Nat.le_succ

-- Now we want to show that Γ' = LindenbaumMCS e Γ is consistent.
--
-- (f is an injection Form → ℕ  ; e is its (left) inverse ℕ → Form N)
--
-- Assume Γ' is inconsistent.
--  That means that there is list of elements L of that set
--  such that their conjunction proves a contradiction.
--
-- L : List (LindenbaumMCS e Γ)
--   there is a "maximum formula" in L, (Prove!)
--   i.e. a formula φ s.t. for all ψ ≠ φ in L f(φ) > f(ψ)
-- Clearly, φ ∈ lindenbaum_family e Γ f(φ). (lemma in_set)
-- Now, we know that for all formulas ψ, if f(ψ) <= n, then
--    ψ ∈ lindenbaum_family e Γ n. (Prove!)
-- So since φ is the greatest element in L, then all elements in L
--    are elements in lindenbaum_family e Γ f(φ).
-- So in fact L only contains elements from lindenbaum_family e Γ f(φ),
--    not from the whole MCS.
--
-- We know that if Γ is consistent, then for all n, lindenbaum_family e Γ n
--    is consistent. (lemma consistent_family).
-- So lindenbaum_family e Γ f(φ) is consistent.
-- So no conjunction of elements in L can prove a contradiction.
--
--    This completes our reductio proof.
--    We conclude LindenbaumMCS e Γ is consistent after all.

-- Needed, but unrelated.
lemma incl_insert {A B : Set α} (h1 : A ⊆ B) (h2 : x ∈ B) : (A ∪ {x}) ⊆ B := by
  intro a h
  simp at h
  apply Or.elim h
  . intro ax
    rw [ax]
    assumption
  . apply h1

-- If φ is a formula that belongs to the infinite union Γ' = LindenbaumMCS e Γ,
--    then φ must belong to some Γᵢ from Γ'.
-- More specifically, i = f φ; i.e. the place of φ in the enumeration.
lemma at_finite_step {Γ : Set (Form N)} (c : consistent Γ) (f : Form N → ℕ) (f_inj : f.Injective) (e : ℕ → Form N) (e_inv : e = f.invFun) :
    φ ∈ LindenbaumMCS e Γ c → φ ∈ Γ (f φ, e) := by
  rw [contraposition]
  simp only [LindenbaumMCS, Set.mem_setOf_eq, not_exists, not_not]
  intro h n habs
  by_cases order : n ≤ (f φ)
  . have incl := increasing_family order habs
    contradiction
  . simp only [not_le] at order
    have order := Nat.le_of_lt order
    have incl := incl_insert ((@increasing_family (f φ)) order) habs
    have n_consistent := consistent_family e c n
    have ⟨phi_inconsistent, _⟩ := not_forall.mp (maximal_family f_inj e_inv h)
    clear h
    have n_inconsistent := Proof.increasing_consequence phi_inconsistent incl
    exact n_consistent n_inconsistent

-- Given a finite list of elements in (LindenbaumMCS e Γ c), all elements of that list
--    occur in some Γᵢ that makes up the infinite union.
lemma list_at_finite_step {Γ : Set (Form N)} {c : consistent Γ} (f : Form N → ℕ) (f_inj : f.Injective) (e : ℕ → Form N) (e_inv : e = f.invFun) (L : List (LindenbaumMCS e Γ c)) :
    {↑φ | φ ∈ L} ⊆ (Γ (L.max_form f, e)) := by
    intro φ_val hmem
    simp only [Set.mem_setOf_eq] at hmem
    let ⟨φ, φ_property, φ_is_val⟩ := hmem
    rw [←φ_is_val]
    clear hmem φ_val φ_is_val
    have φ_in_MCS : ↑φ ∈ LindenbaumMCS e Γ c := by simp
    have φ_in_own_set := at_finite_step c f f_inj e e_inv φ_in_MCS
    have := L.max_is_max f φ φ_property
    exact increasing_family this φ_in_own_set

lemma LindenbaumConsistent {Γ : Set (Form N)} (c : consistent Γ) {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun) :
  consistent (LindenbaumMCS e Γ c) := by
  rw [←@not_not (consistent (LindenbaumMCS e Γ c))]
  intro habs
  let ⟨⟨L, L_incons⟩, _⟩ := not_forall.mp habs
  clear habs
  let ⟨L', conj_L'⟩ := conj_incl_linden L (list_at_finite_step f f_inj e e_inv L)
  rw [conj_L'] at L_incons
  clear conj_L'
  have : ((⊢(conjunction (Γ(L.max_form f, e)) L'⟶⊥) → (Γ(L.max_form f, e)) ⊢ ⊥)) := by intro h; simp [SyntacticConsequence]; exists L'
  exact consistent_family e c (L.max_form f) (this L_incons)

lemma LindenbaumMaximal {Γ : Set (Form N)} (c : consistent Γ) {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun) :
  ∀ φ, φ ∉ (LindenbaumMCS e Γ c) → ¬consistent ((LindenbaumMCS e Γ c) ∪ {φ}) := by
  intro φ not_mem
  have := all_sets_in_family_tollens not_mem (f φ)
  have ⟨pf_bot, _⟩ := not_forall.mp (maximal_family f_inj e_inv this)
  intro habs
  apply habs
  apply Proof.Deduction.mp
  apply Proof.increasing_consequence
  exact Proof.Deduction.mpr pf_bot
  apply all_sets_in_family

theorem RegularLindenbaumLemma : ∀ Γ : Set (Form N), consistent Γ → ∃ Γ' : Set (Form N), Γ ⊆ Γ' ∧ MCS Γ' := by
  intro Γ cons
  let ⟨f, f_inj⟩ := exists_injective_nat (Form N)
  let enum       := f.invFun
  let Γ' := LindenbaumMCS enum Γ cons
  have enum_inv : enum = f.invFun := rfl
  exists Γ'
  apply And.intro
  . -- Γ is included in Γ'
    let Γ₀ := Γ (0, enum)
    have Γ_in_Γ₀ : Γ ⊆ Γ₀ := Γ_in_family
    have Γ₀_in_family := @all_sets_in_family N enum Γ cons 0
    rw [show LindenbaumMCS enum Γ cons = Γ' by simp, show Γ (0, enum) = Γ₀ by simp] at Γ₀_in_family
    intro _ φ_in_Γ
    exact Γ₀_in_family (Γ_in_Γ₀ φ_in_Γ)
  . rw [MCS]
    apply And.intro
    . exact LindenbaumConsistent cons f_inj enum_inv
    . intro φ
      exact LindenbaumMaximal cons f_inj enum_inv φ

def enough_noms (Γ : Set (Form N)) := (∃ i, all_nocc i Γ) ∧ ∀ (e : ℕ → Form N) (n : ℕ), ∃ i, all_nocc i (Γ (n, e))

lemma LindenbaumWitnessed {Γ : Set (Form N)} (c : consistent Γ) {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun)
    (h : enough_noms Γ) : witnessed (LindenbaumMCS e Γ c) := by
    intro φ φ_mem
    split
    . next φ x ψ =>
        have φ_mem := at_finite_step c f f_inj e e_inv φ_mem
        let n := f ((all x, ψ⟶⊥)⟶⊥)
        have not₁ : n = f ((all x, ψ⟶⊥)⟶⊥) := by simp
        have not₂ : (ex x, ψ) = ((all x, ψ⟶⊥)⟶⊥) := by simp
        rw [←not₁, ←not₂] at φ_mem

        have ⟨i, nocc⟩ := h.right e n
        exists i
        apply all_sets_in_family (n)
        revert not₁
        cases n with
        | zero =>
            intro not₁
            have : e (Nat.zero) = ((all x, ψ⟶⊥)⟶⊥) := by rw [not₁, e_inv, Function.leftInverse_invFun f_inj]
            rw [lindenbaum_family, this, lindenbaum_next]
            admit
        | succ n =>
            intro not₁
            simp [lindenbaum_family]
            admit

    . assumption

theorem ExtendedLindenbaumLemma : ∀ Γ : Set (Form TotalSet), consistent Γ → ∃ Γ' : Set (Form TotalSet), Γ.odd_noms ⊆ Γ' ∧ MCS Γ' ∧ witnessed Γ' := by admit
