import Hybrid.ProofUtils
import Hybrid.FormCountable

open Classical

section Lindenbaum

  -- First, we define how to obtain Γᵢ₊₁ from Γᵢ, given a formula φ: 
  def lindenbaum_next (Γ : Set Form) (φ : Form) : Set Form :=
    if (Γ ∪ {φ}).consistent then
      Γ ∪ {φ}
    else
      Γ
  
  -- Now we define the whole indexed family Γᵢ.
  -- Usually, the enumeration of formulas starts from 1 (φ₁, φ₂, ...), and
  --    Γ₀ = Γ .
  -- However, in Lean it's much tidier to enumerate from 0 (φ₀, φ₁, ...), so
  --    Γ₀ = Γ ∪ {φ₀} if it is consistent and Γ₀ = Γ otherwise.
  def lindenbaum_family (enum : Nat → Form) (Γ : Set Form) : Nat → Set Form 
  | .zero   => lindenbaum_next Γ (enum 0)
  | .succ n =>
      let prev_set := lindenbaum_family enum Γ n
      lindenbaum_next prev_set (enum (n+1))
  
  notation Γ "(" i "," e ")" => lindenbaum_family e Γ i    

  def LindenbaumMCS (enum : Nat → Form) (Γ : Set Form) (_ : Γ.consistent) : Set Form :=
      {φ | ∃ i : Nat, φ ∈ Γ (i, enum)}

  -- Lemma: All Γᵢ belong to LindenbaumMCS Γ
  lemma all_sets_in_family{enum : ℕ → Form} {Γ : Set Form} {c : Γ.consistent} : ∀ n, Γ (n, enum) ⊆ LindenbaumMCS enum Γ c := by
    intro i φ h
    exists i
  
  lemma all_sets_in_family_tollens {enum : ℕ → Form} {Γ : Set Form} {c : Γ.consistent} : φ ∉ (LindenbaumMCS enum Γ c) → ∀ n, φ ∉ Γ (n, enum) := by
    rw [contraposition, not_not, not_forall]
    intro h
    let ⟨i, hi⟩ := h
    rw [not_not] at hi
    exact all_sets_in_family i hi 

  -- Lemma: If Γ is consistent, then for all φ, lindenbaum_next Γ φ is consistent
  lemma consistent_lindenbaum_next (Γ : Set Form) (hc : Γ.consistent) (φ : Form) : (lindenbaum_next Γ φ).consistent := by
    rw [lindenbaum_next]
    split <;> assumption
  
  -- Lemma: If you can consistently extend (lindenbaum_next Γ φ) with φ, then
  --    φ already belongs to (lindenbaum_next Γ φ)
  lemma maximal_lindenbaum_next {Γ : Set Form} (hc : ((lindenbaum_next Γ φ) ∪ {φ}).consistent) : φ ∈ lindenbaum_next Γ φ := by
    rw [lindenbaum_next] at hc
    by_cases h : (Γ ∪ {φ}).consistent
    . clear hc
      simp only [lindenbaum_next, h, ite_true]
      simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
    . simp only [h, ite_false] at hc
      -- ^ contradiction

  --
  -- Now apply the previous lemmas to the family as a whole.
  --

  -- Lemma: If Γ is consistent, then all Γᵢ are consistent.
  lemma consistent_family {Γ : Set Form} (e : ℕ → Form) (c : Γ.consistent) : ∀ n, (Γ (n, e)).consistent := by
    intro n
    induction n with
    | zero =>
        simp only [lindenbaum_family, lindenbaum_next]
        split <;> assumption
    | succ n ih =>
        simp only [lindenbaum_family]
        apply consistent_lindenbaum_next
        assumption

  -- Lemma: If φ doesn't belong to the set in the family corresponding to its place in the enumeration,
  --     (i.e., φ ∉ Γᵢ, where i = f φ),
  --    then Γᵢ ∪ {φ} must be inconsistent.
  lemma maximal_family {Γ : Set Form} {f : Form → ℕ} (f_inj : f.Injective) {e : ℕ → Form} (e_inv : e = f.invFun) :
      ¬φ ∈ Γ (f φ, e) → ¬(Γ (f φ, e) ∪ {φ}).consistent := by
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
          exact incl (ih φ_member)
        . assumption
  
  -- Now we want to show that Γ' = LindenbaumMCS e Γ is consistent.
  --
  -- (f is an injection Form → ℕ  ; e is its (left) inverse ℕ → Form)
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
  lemma at_finite_step {Γ : Set Form} (c : Γ.consistent) (f : Form → ℕ) (f_inj : f.Injective) (e : ℕ → Form) (e_inv : e = f.invFun) :
      φ ∈ LindenbaumMCS e Γ c → φ ∈ Γ (f φ, e) := by
    rw [contraposition]
    simp only [LindenbaumMCS, Set.mem_setOf_eq, not_exists, not_not]
    intro h n habs
    by_cases order : n ≤ (f φ)
    . have incl := increasing_family order habs
      contradiction
    . simp only [not_le] at order
      have order := Nat.le_of_lt order
      have incl := incl_insert (@increasing_family (f φ) n e Γ order) habs
      have n_consistent := consistent_family e c n
      have phi_inconsistent := maximal_family f_inj e_inv h
      clear h
      simp only [Set.consistent, not_not] at n_consistent phi_inconsistent
      have n_inconsistent := Proof.increasing_consequence phi_inconsistent incl
      exact n_consistent n_inconsistent

  -- Given a finite list of elements in (LindenbaumMCS e Γ c), all elements of that list
  --    occur in some Γᵢ that makes up the infinite union.
  lemma list_at_finite_step {Γ : Set Form} {c : Γ.consistent} (f : Form → ℕ) (f_inj : f.Injective) (e : ℕ → Form) (e_inv : e = f.invFun) (L : List (LindenbaumMCS e Γ c)) :
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

  lemma LindenbaumConsistent {Γ : Set Form} (c : Γ.consistent) {f : Form → ℕ} (f_inj : f.Injective) {e : ℕ → Form} (e_inv : e = f.invFun) :
    (LindenbaumMCS e Γ c).consistent := by
    rw [←@not_not (Set.consistent (LindenbaumMCS e Γ c))]
    intro habs
    rw [Set.consistent, not_not, SyntacticConsequence] at habs
    let ⟨L, L_incons⟩ := habs
    clear habs
    let ⟨L', conj_L'⟩ := conj_incl_linden L (list_at_finite_step f f_inj e e_inv L)
    rw [conj_L'] at L_incons
    clear conj_L'
    have : ((⊢(conjunction (Γ(L.max_form f, e)) L'⟶⊥) → (Γ(L.max_form f, e)) ⊢ ⊥)) := by intro h; simp [SyntacticConsequence]; exists L'
    have := this L_incons
    have := consistent_family e c (L.max_form f)
    contradiction

  lemma LindenbaumMaximal {Γ : Set Form} (c : Γ.consistent) {f : Form → ℕ} (f_inj : f.Injective) {e : ℕ → Form} (e_inv : e = f.invFun) :
    ∀ φ, φ ∉ (LindenbaumMCS e Γ c) → ((LindenbaumMCS e Γ c) ∪ {φ}) ⊢ ⊥ := by
    intro φ not_mem
    have := all_sets_in_family_tollens not_mem (f φ)
    have := maximal_family f_inj e_inv this
    simp only [Set.consistent, not_not, ←Proof.Deduction] at this ⊢
    apply Proof.increasing_consequence this
    apply all_sets_in_family

  theorem LindenbaumLemma : ∀ Γ : Set Form, Γ.consistent → ∃ Γ' : Set Form, Γ ⊆ Γ' ∧ Γ'.MCS := by
    intro Γ cons
    let ⟨f, f_inj⟩ := exists_injective_nat Form
    let enum       := f.invFun
    let Γ' := LindenbaumMCS enum Γ cons
    have enum_inv : enum = f.invFun := by simp
    exists Γ'
    apply And.intro 
    . -- Γ is included in Γ'
      let Γ₀ := Γ (0, enum)
      have Γ_in_Γ₀ : Γ ⊆ Γ₀ := by
          simp [show Γ₀ = Γ (0, enum) by simp, lindenbaum_family, lindenbaum_next]
          split <;> simp [subset_of_eq]
      have Γ₀_in_family := @all_sets_in_family enum Γ cons 0
      rw [show LindenbaumMCS enum Γ cons = Γ' by simp, show Γ (0, enum) = Γ₀ by simp] at Γ₀_in_family
      intro _ φ_in_Γ
      exact Γ₀_in_family (Γ_in_Γ₀ φ_in_Γ)
    . rw [Set.MCS]
      apply And.intro
      . exact LindenbaumConsistent cons f_inj enum_inv
      . exact LindenbaumMaximal cons f_inj enum_inv

end Lindenbaum

/-
theorem ExtendedLindenbaumLemma : ∀ Γ : Set Form, Γ.consistent → ∃ Γ' : Set Form, Γ.double ⊆ Γ' ∧ Γ'.witnessed ∧ Γ'.MCS := by
  intro Γ cons
  admit
-/