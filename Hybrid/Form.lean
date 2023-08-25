import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin
import Hybrid.Util

section Basics
  structure PROP where
    letter : Nat
  deriving DecidableEq, Repr

  structure SVAR where
    letter : Nat
  deriving DecidableEq, Repr

  structure NOM where
    letter : Nat
  deriving DecidableEq, Repr

  instance : Max PROP where
    max := λ p => λ q => ite (p.letter > q.letter) p q
  instance svarmax : Max SVAR where
    max := λ x => λ y => ite (x.letter > y.letter) x y
  instance : Max NOM where
    max := λ i => λ j => ite (i.letter > j.letter) i j

  theorem NOM_eq {i j : NOM} : (i = j) ↔ (i.letter = j.letter) := by
    cases i
    cases j
    simp
  theorem NOM_eq' {i j : NOM} : (i = j) ↔ (j.letter = i.letter) := by
    cases i
    cases j
    simp
    apply Iff.intro <;> {intro; simp [*]}

--  instance ofNatSVAR : OfNat SVAR n    where
--    ofNat := SVAR.mk n
  instance : OfNat NOM n     where
    ofNat := NOM.mk  n
  instance : Coe SVAR Nat  := ⟨SVAR.letter⟩
--  instance : Coe NOM Nat   := ⟨NOM.letter⟩
  instance : Coe Nat SVAR  := ⟨SVAR.mk⟩   
--  instance : Coe Nat NOM   := ⟨NOM.mk⟩   
  instance SVAR.le : LE SVAR         where
    le    := λ x => λ y =>  x.letter ≤ y.letter
  instance SVAR.lt : LT SVAR         where
    lt    := λ x => λ y =>  x.letter < y.letter
  instance NOM.le : LE NOM         where
    le    := λ x => λ y =>  x.letter ≤ y.letter
  instance NOM.lt : LT NOM         where
    lt    := λ x => λ y =>  x.letter < y.letter
  instance SVAR.add : HAdd SVAR Nat SVAR where
    hAdd  := λ x => λ n => SVAR.mk (x.letter + n)
  instance NOM.add : HAdd NOM Nat NOM where
    hAdd  := λ x => λ n => NOM.mk (x.letter + n)
  instance : HMul NOM Nat NOM where
    hMul  := λ x => λ n => NOM.mk (x.letter * n)
  instance NOM.hmul : HMul Nat NOM NOM where
    hMul  := λ n => λ x => NOM.mk (x.letter * n)
  instance : HMul NOM ℕ ℕ where
    hMul  := λ x => λ n => x.letter * n

  instance : IsTrans NOM GT.gt where
    trans := λ _ _ _ h1 h2 => Nat.lt_trans h2 h1

  instance : IsTotal NOM GE.ge where
    total := by simp [NOM.le, Nat.le_total]

  instance : IsTrans NOM GE.ge where
    trans := λ _ _ _ h1 h2 => Nat.le_trans h2 h1

  theorem NOM.gt_iff_ge_and_ne {a b : NOM} : a > b ↔ (a ≥ b ∧ a ≠ b) := by
    simp only [GT.gt, GE.ge, NOM.lt, NOM.le, NOM.mk, Nat.lt_iff_le_and_ne, ne_eq, NOM_eq']

  inductive Form where
    -- atomic formulas:
    | bttm : Form
    | prop : PROP → Form
    | svar : SVAR → Form
    | nom  :  NOM → Form
    -- connectives:
    | impl : Form → Form → Form
    -- modal:
    | box  : Form → Form
    -- hybrid:
    | bind : SVAR → Form → Form
  deriving DecidableEq, Repr

  def Form.depth : Form → ℕ
    | .impl φ ψ =>  1 + Form.depth φ + Form.depth ψ
    | .box  φ   =>  1 + Form.depth φ
    | .bind _ φ =>  2 + Form.depth φ
    | _       =>    0

  @[simp]
  def Form.neg      : Form → Form := λ φ => Form.impl φ Form.bttm
  @[simp]
  def Form.conj     : Form → Form → Form := λ φ => λ ψ => Form.neg (Form.impl φ (Form.neg ψ))
  @[simp]
  def Form.iff      : Form → Form → Form := λ φ => λ ψ => Form.conj (Form.impl φ ψ) (Form.impl ψ φ) 
  @[simp]
  def Form.disj     : Form → Form → Form := λ φ => λ ψ => Form.impl (Form.neg φ) ψ
  @[simp]
  def Form.diamond  : Form → Form := λ φ => Form.neg (Form.box (Form.neg φ))
  @[simp,match_pattern]
  def Form.bind_dual: SVAR → Form → Form := λ x => λ φ => Form.neg (Form.bind x (Form.neg φ))

  instance : Coe PROP Form  := ⟨Form.prop⟩
  instance : Coe SVAR Form  := ⟨Form.svar⟩
  instance : Coe NOM  Form  := ⟨Form.nom⟩

  infixr:60 "⟶" => Form.impl
  infixl:65 "⋀" => Form.conj
  infixl:65 "⋁" => Form.disj
  prefix:100 "□" => Form.box
  prefix:100 "◇ " => Form.diamond
  notation:120 "all " x ", " φ => Form.bind x φ
  notation:120 "ex " x ", " φ => Form.bind_dual x φ
  prefix:170 "∼" => Form.neg
  infixr:60 "⟷" => Form.iff
  notation "⊥"  => Form.bttm

  def conjunction (Γ : Set Form) (L : List Γ) : Form :=
  match L with
    | []     => ⊥ ⟶ ⊥
    | h :: t => h.val ⋀ conjunction Γ t

  def Form.new_var  : Form → SVAR
  | .svar x   => x+1
  | .impl ψ χ => max (ψ.new_var) (χ.new_var)
  | .box  ψ   => ψ.new_var
  | .bind x ψ => max (x+1) (ψ.new_var)
  | _         => ⟨0⟩

  def Form.new_nom  : Form → NOM
  | .nom  i   => i+1
  | .impl ψ χ => max (ψ.new_nom) (χ.new_nom)
  | .box  ψ   => ψ.new_nom
  | .bind _ ψ => ψ.new_nom
  | _         => ⟨0⟩ 

end Basics

section Substitutions
  def occurs (x : SVAR) (φ : Form) : Bool :=
    match φ with
    | Form.bttm     => false
    | Form.prop _   => false
    | Form.svar y   => x = y
    | Form.nom  _   => false
    | Form.impl φ ψ => (occurs x φ) || (occurs x ψ)
    | Form.box  φ   => occurs x φ
    | Form.bind _ φ => occurs x φ

  def is_free (x : SVAR) (φ : Form) : Bool :=
    match φ with
    | Form.bttm     => false
    | Form.prop _   => false
    | Form.svar y   => x == y
    | Form.nom  _   => false
    | Form.impl φ ψ => (is_free x φ) || (is_free x ψ)
    | Form.box  φ   => is_free x φ
    | Form.bind y φ => (y != x) && (is_free x φ)

  def is_bound (x : SVAR) (φ : Form) := (occurs x φ) && !(is_free x φ)
  
  -- conventions for substitutions can get confusing
  -- "φ[s // x], the formula obtained by substituting s for all *free* occurrences of x in φ"
  -- for reference: Blackburn 1998, pg. 628
  def subst_svar (φ : Form) (s : SVAR) (x : SVAR) : Form :=
    match φ with
    | Form.bttm     => φ
    | Form.prop _   => φ
    | Form.svar y   => ite (x = y) s y
    | Form.nom  _   => φ
    | Form.impl φ ψ => (subst_svar φ s x) ⟶ (subst_svar ψ s x)
    | Form.box  φ   => □ (subst_svar φ s x)
    | Form.bind y φ => ite (x = y) (Form.bind y φ) (Form.bind y (subst_svar φ s x))

  def subst_nom (φ : Form) (s : NOM) (x : SVAR) : Form :=
    match φ with
    | Form.bttm     => φ
    | Form.prop _   => φ
    | Form.svar y   => ite (x = y) s y
    | Form.nom  _   => φ
    | Form.impl φ ψ => (subst_nom φ s x) ⟶ (subst_nom ψ s x)
    | Form.box  φ   => □ (subst_nom φ s x)
    | Form.bind y φ => ite (x = y) (Form.bind y φ) (Form.bind y (subst_nom φ s x))

  def is_substable (φ : Form) (y : SVAR) (x : SVAR) : Bool :=
    match φ with
    | Form.bttm     => true
    | Form.prop _   => true
    | Form.svar _   => true
    | Form.nom  _   => true
    | Form.impl φ ψ => (is_substable φ y x) && (is_substable ψ y x)
    | Form.box  φ   => is_substable φ y x
    | Form.bind z φ =>
        if (is_free x φ == false) then true
        else z != y && is_substable φ y x
    -- all s, s ⟶ (all x, x)  : safe,   substitution won't do anything
    -- all x, x                : safe,   substitution won't do anything
    -- all y, y ⟶ x           : safe,   result will be   all y, y ⟶ s
    -- all s, y ⟶ x           : UNSAFE, substitution would make x bound
    --                                      where it was previously free
    --
    -- Takeaway: s is substable for all free occurences of x only as long
    --         as x *does not occur free in the scope of an s-quantifier*

  notation:150 φ "[" s "//" x "]" => subst_svar φ s x
  notation:150 φ "[" s "//" x "]" => subst_nom  φ s x

end Substitutions

section NominalSubstitution 

  def Form.nominals : Form → List NOM
  | .nom a      => [a]
  | .impl φ ψ   => φ.nominals ++ ψ.nominals
  | .box φ      => φ.nominals
  | .bind _ φ   => φ.nominals
  | _           => []

  def nom_subst_nom : Form → NOM → NOM → Form
  | .nom a, i, j     => if a = j then i else a
  | .impl φ ψ, i, j  => nom_subst_nom φ i j ⟶ nom_subst_nom ψ i j
  | .box φ, i, j     => □ nom_subst_nom φ i j
  | .bind y φ, i, j  => all y, nom_subst_nom φ i j
  | φ, _, _          => φ

  def nom_subst_svar : Form → SVAR → NOM → Form
  | .nom a, i, j     => if a = j then i else a
  | .impl φ ψ, i, j  => nom_subst_svar φ i j ⟶ nom_subst_svar ψ i j
  | .box φ, i, j     => □ nom_subst_svar φ i j
  | .bind y φ, i, j  => all y, nom_subst_svar φ i j
  | φ, _, _          => φ

  notation:150 φ "[" i "//" a "]" => nom_subst_nom φ i a
  notation:150 φ "[" i "//" a "]" => nom_subst_svar φ i a

  def nom_occurs : NOM → Form → Bool
  | i, .nom j    => i = j
  | i, .impl ψ χ => (nom_occurs i ψ) || (nom_occurs i χ)
  | i, .box ψ    => nom_occurs i ψ
  | i, .bind _ ψ => nom_occurs i ψ
  | _, _         => false

  def all_nocc (i : NOM) (Γ : Set Form) := ∀ (φ : Form), φ ∈ Γ → nom_occurs i φ = false

  theorem all_noc_conj (h : all_nocc i Γ) (L : List Γ) : nom_occurs i (conjunction Γ L) = false := by
    induction L with
    | nil => simp [conjunction, nom_occurs]
    | cons head tail ih =>
        simp [conjunction, nom_occurs, ih, -Form.conj]
        exact h head head.2

  def Form.bulk_subst : Form → List NOM → List NOM → Form
  | φ, h₁ :: t₁, h₂ :: t₂ => bulk_subst (φ[h₁ // h₂]) t₁ t₂
  | φ, _, []    =>  φ
  | φ, [], _    =>  φ

  def Form.list_noms : Form → List NOM
  | nom  i   => [i]
  | impl φ ψ => (List.merge GE.ge φ.list_noms ψ.list_noms).dedup
  | box φ    => φ.list_noms
  | bind _ φ => φ.list_noms
  | _        => []

  def Form.odd_list_noms : Form → List NOM := λ φ => φ.list_noms.map (λ i => 2*i+1)

  def Form.odd_noms : Form → Form := λ φ => φ.bulk_subst φ.odd_list_noms φ.list_noms

  def Set.odd_noms : Set Form → Set Form := λ Γ => {Form.odd_noms φ | φ ∈ Γ} 

  def nocc_bulk_property (l1 l2 : List NOM) (φ : Form) := ∀ {n : Fin l1.length} {i : NOM}, (i = l1[n]) → (i ∉ φ.list_noms ∨ i ∈ l2.take n) ∧ i ∉ l1.take n

  theorem list_noms_sorted_ge {φ : Form} : φ.list_noms.Sorted GE.ge := by
    induction φ with
    | nom  i   => simp [Form.list_noms]
    | impl φ ψ ih1 ih2 =>
        exact List.Pairwise.sublist ((List.merge GE.ge φ.list_noms ψ.list_noms).dedup_sublist) (List.Sorted.merge ih1 ih2)
    | box _ ih    => exact ih
    | bind _ _ ih => exact ih
    | _        => simp [Form.list_noms]
  
  theorem list_noms_nodup {φ : Form} : φ.list_noms.Nodup := by
    induction φ <;> simp [Form.list_noms, List.nodup_dedup, *]

  theorem list_noms_sorted_gt {φ : Form} : φ.list_noms.Sorted GT.gt := by
    simp [List.Sorted, List.Pairwise, GT.gt, NOM.gt_iff_ge_and_ne]
    apply List.Pairwise.and
    apply list_noms_nodup
    apply list_noms_sorted_ge

  theorem list_noms_chain' {φ : Form} : φ.list_noms.Chain' GT.gt := by
    rw [List.chain'_iff_pairwise]
    exact list_noms_sorted_gt

end NominalSubstitution

section IteratedModalities

  -- Axiom utils. Since we won't be assuming a transitive frame,
  -- it will make sense to be able to construct formulas with
  -- iterated modal operators at their beginning (ex., for axiom nom)
  def iterate_nec (n : Nat) (φ : Form) : Form :=
    let rec loop : Nat → Form → Form
      | 0, φ   => φ
      | n+1, φ => □ (loop n φ)
    loop n φ

  theorem iter_nec_one : □ φ = iterate_nec 1 φ := by
    rw [iterate_nec, iterate_nec.loop, iterate_nec.loop]

  theorem iter_nec_one_m_comm : iterate_nec 1 (iterate_nec m φ) = iterate_nec m (iterate_nec 1 φ) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop]
        exact ih

  theorem iter_nec_compose : iterate_nec (m + 1) φ = iterate_nec m (iterate_nec 1 φ) := by
    rw [iterate_nec, iterate_nec.loop, iter_nec_one, ←iterate_nec, iter_nec_one_m_comm]

  theorem iter_nec_succ : iterate_nec (m + 1) φ = iterate_nec m (□ φ) := by
    rw [iter_nec_one, iter_nec_compose]



  def iterate_pos (n : Nat) (φ : Form) : Form :=
    let rec loop : Nat → Form → Form
      | 0, φ   => φ
      | n+1, φ => ◇ (loop n φ)
    loop n φ

  theorem iter_pos_one : ◇ φ = iterate_pos 1 φ := by
    rw [iterate_pos, iterate_pos.loop, iterate_pos.loop]

  theorem iter_pos_one_m_comm : iterate_pos 1 (iterate_pos m φ) = iterate_pos m (iterate_pos 1 φ) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop]
        exact ih

  theorem iter_pos_compose : iterate_pos (m + 1) φ = iterate_pos m (iterate_pos 1 φ) := by
    rw [iterate_pos, iterate_pos.loop, iter_pos_one, ←iterate_pos, iter_pos_one_m_comm]

  theorem iter_pos_succ : iterate_pos (m + 1) φ = iterate_pos m (◇ φ) := by
    rw [iter_pos_one, iter_pos_compose]


end IteratedModalities

  theorem ex_depth {x : SVAR} : Form.depth φ < Form.depth (ex x, φ) := by
    simp [Form.depth]
    rw [←Nat.add_assoc, ←Nat.add_assoc, Nat.add_comm]
    apply Nat.lt_add_of_pos_right
    simp