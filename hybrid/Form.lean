import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Parity
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


  instance : OfNat SVAR n    where
    ofNat := SVAR.mk n
  instance : OfNat NOM n     where
    ofNat := NOM.mk  n
  instance : Coe SVAR Nat  := ⟨SVAR.letter⟩
--  instance : Coe NOM Nat   := ⟨NOM.letter⟩
  instance : Coe Nat SVAR  := ⟨SVAR.mk⟩   
--  instance : Coe Nat NOM   := ⟨NOM.mk⟩   
  instance SVAR.le : LE SVAR         where
    le    := λ x => λ y =>  x.letter ≤ y.letter
  instance : LT SVAR         where
    lt    := λ x => λ y =>  x.letter < y.letter
  instance NOM.le : LE NOM         where
    le    := λ x => λ y =>  x.letter ≤ y.letter
  instance  : HAdd SVAR Nat SVAR where
    hAdd  := λ x => λ n => SVAR.mk (x.letter + n)
  instance : HAdd NOM Nat NOM where
    hAdd  := λ x => λ n => NOM.mk (x.letter + n)
  instance : HMul NOM Nat NOM where
    hMul  := λ x => λ n => NOM.mk (x.letter * n)
  instance : HMul Nat NOM NOM where
    hMul  := λ n => λ x => NOM.mk (x.letter * n)
  instance : HMul NOM ℕ ℕ where
    hMul  := λ x => λ n => x.letter * n

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
  | _         => 0

  def Form.new_nom  : Form → NOM
  | .nom  i   => i+1
  | .impl ψ χ => max (ψ.new_nom) (χ.new_nom)
  | .box  ψ   => ψ.new_nom
  | .bind _ ψ => ψ.new_nom
  | _         => 0

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

  #eval is_free (SVAR.mk 0) ⊥
  #eval is_free (SVAR.mk 0) (all SVAR.mk 0, ⊥)

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

  #eval is_substable (all SVAR.mk 0, all SVAR.mk 1, SVAR.mk 0) (SVAR.mk 1) (SVAR.mk 0)  
  #eval subst_svar (all SVAR.mk 0, all SVAR.mk 1, SVAR.mk 0) (SVAR.mk 1) (SVAR.mk 0)
  #eval occurs 1 (all 0, all 1, SVAR.mk 0)

  lemma new_var_gt      : occurs x φ → x < φ.new_var   := by
    induction φ with
    | svar y          =>
        simp [occurs, Form.new_var, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self y.letter
    | impl ψ χ ih1 ih2 =>
        simp only [occurs, Form.new_var, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box ψ ih      =>
        simp only [occurs, Form.new_var]
        assumption
    | bind y ψ ih   =>
        simp only [occurs, Form.new_var, max]
        intro h
        have ih := ih h
        by_cases hc : (y + 1).letter > (Form.new_var ψ).letter
        . simp [hc]
          simp at hc
          exact Nat.lt_trans ih hc
        . simp [hc]
          assumption
    | _ => simp [occurs]

  lemma new_var_is_new  : occurs (φ.new_var) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_var_gt h
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a
  
  lemma ge_new_var_is_new (h : x ≥ φ.new_var) : occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_var_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a
  
  lemma notfreeset {Γ : Set Form} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ = false) : is_free x (conjunction Γ L) = false := by
    induction L with
    | nil         =>
        simp only [conjunction, is_free]
    | cons h t ih =>
        simp only [is_free, Bool.or_false, Bool.or_eq_false_eq_eq_false_and_eq_false]
        apply And.intro
        . exact hyp h
        . exact ih

  lemma notfree_after_subst {φ : Form} {x y : SVAR} (h : x ≠ y) : is_free x (φ[y // x]) = false := by
    induction φ with
    | svar z   =>
        by_cases xz : x = z
        . simp [subst_svar, if_pos xz, is_free, h]
        . simp [subst_svar, if_neg xz, is_free, xz]
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, is_free, ih1, ih2]
    | box _ ih    =>
        simp [subst_svar, is_free, ih]
    | bind z _ ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, is_free]
        . simp [subst_svar, if_neg xz, is_free, ih]
    | _        => simp only [is_free]

  lemma notocc_beforeafter_subst {φ : Form} {x y : SVAR} (h : occurs x φ = false) : occurs x (φ[y // x]) = false := by
    induction φ with
    | svar z   =>
        by_cases xz : x = z
        <;> simp [subst_svar, if_pos xz, xz, occurs, h] at *
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, occurs, not_or, ih1, ih2, -implication_disjunction] at *
        exact ⟨ih1 h.left, ih2 h.right⟩ 
    | box _ ih    =>
        simp [subst_svar, occurs, ih, -implication_disjunction] at *
        exact ih h
    | bind z ψ ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, occurs] at *
          exact h
        . simp [subst_svar, if_neg xz, occurs, ih, xz, h, -implication_disjunction] at *
          exact ih h
    | _        => simp only [occurs]

  lemma notoccursbind : occurs x φ = false → occurs x (all v, φ) = false := by
    simp [occurs]

  lemma notoccurs_notfree : (occurs x φ = false) → (is_free x φ = false) := by
    induction φ with
    | svar _ => simp [occurs, is_free]
    | impl _ _ ih1 ih2 =>
        intro h
        simp [occurs] at h
        simp [is_free, ih1, ih2, h]
    | box _ ih        =>
        intro h
        rw [occurs] at h
        simp [is_free, ih, h]
    | bind _ _ ih     =>
        intro h
        rw [occurs] at h
        simp [is_free, ih, h]
    | _ => 
        intro h
        rfl

  lemma preserve_notfree {φ : Form} (x v : SVAR) : (is_free x φ = false) → (is_free x (all v, φ) = false) := by
    intro h
    simp only [is_free, h, Bool.and_false]

  -- φ = all x, all y, x
  -- φ[y // x] = φ:                 (x is bound in φ)
  #eval (all SVAR.mk 0, all SVAR.mk 1, SVAR.mk 0)[SVAR.mk 1 // SVAR.mk 0]
  --  but is_subst φ y x = false:   (x occurs free in the scope of y)
  #eval is_substable (all SVAR.mk 0, all SVAR.mk 1, SVAR.mk 0) (SVAR.mk 1) (SVAR.mk 0)
  lemma subst_notfree_var {φ : Form} {x y : SVAR} (h : is_free x φ = false) : (φ[y // x] = φ) ∧ (occurs x φ = false → is_substable φ y x) := by
    induction φ with
    | svar z =>
        by_cases heq : x = z
        . simp only [is_free, heq, beq_self_eq_true] at h 
        . simp only [subst_svar, heq, ite_false, occurs, is_substable]
    | impl ψ χ ih1 ih2 =>
        simp only [is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h 
        apply And.intro
        . simp [subst_svar, h, ih1, ih2]
        . intro nocc
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at nocc 
          simp [is_substable, h, nocc, ih1, ih2]
    | box ψ ih  =>
        rw [is_free] at h
        apply And.intro
        . simp [subst_svar, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, ih, nocc, h]
    | bind z ψ ih =>
        apply And.intro
        . by_cases heq : x = z
          . rw [←heq, subst_svar, if_pos (Eq.refl x)]
          . simp only [is_free, bne, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false', beq_iff_eq,
            Ne.symm heq, false_or] at h 
            simp [subst_svar, heq, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, notoccurs_notfree, nocc]
    | _   =>
        simp [subst_svar, is_substable]

    lemma rereplacement (φ : Form) (x y : SVAR) (h1 : occurs y φ = false) (h2 : is_substable φ y x) : (is_substable (φ[y // x]) x y) ∧ φ[y // x][x // y] = φ := by
      induction φ with
      | svar z =>
          simp [occurs] at h1
          by_cases xz : x = z
          repeat simp [subst_svar, xz, h1, is_substable]
      | impl ψ χ ih1 ih2 =>
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1 
          simp only [is_substable, Bool.and_eq_true] at h2
          simp [subst_svar, ih1, ih2, h1, h2, is_substable]
      | box ψ ih =>
          simp only [occurs] at h1
          simp only [is_substable] at h2
          simp [subst_svar, ih, h1, h2, is_substable]
      | bind z ψ ih =>
          by_cases yz : y = z
          . rw [←yz]
            rw [←yz] at h1

            simp only [is_substable, beq_iff_eq, ←yz, bne_self_eq_false, Bool.false_and, ite_eq_left_iff,
              Bool.not_eq_false, implication_disjunction, Bool.not_eq_true, or_false] at h2 
            have h2 := @preserve_notfree ψ x y h2
            simp [subst_notfree_var, h2]

            have := @subst_notfree_var (all y, ψ) y x (notoccurs_notfree h1)
            simp [@subst_notfree_var (all y, ψ) y x, notoccurs_notfree, h1]
          . by_cases xz : x = z
            . have : is_free x (all x, ψ) = false := by simp [is_free]
              rw [←xz] at h1
              simp [←xz, subst_notfree_var, this, notoccurs_notfree, h1]
            . simp only [occurs] at h1
              simp [subst_svar, xz, yz]
              by_cases xfree : is_free x ψ
              . simp [is_substable, xfree, Ne.symm yz, bne] at h2
                simp [ih, h1, h2, is_substable, bne, Ne.symm xz]
              . rw [show (¬is_free x ψ = true ↔ is_free x ψ = false) by simp] at xfree
                simp [subst_notfree_var, xfree, is_substable, (notoccurs_notfree h1)]
      | _     =>
          apply And.intro
          repeat rfl
  
  lemma subst_self_is_self (φ : Form) (x : SVAR) : φ [x // x] = φ := by
    induction φ with
    | svar y   =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy, xy]
        . rw [subst_svar, if_neg xy]
    | impl φ ψ ih1 ih2 =>
        rw [subst_svar, ih1, ih2]
    | box  φ ih  =>
        rw [subst_svar, ih]
    | bind y φ ih =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy]
        . rw [subst_svar, if_neg xy, ih]
    | _        => rfl

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

  def Form.list_noms : Form → List NOM := λ φ =>
    loop φ.new_nom.letter φ
  where
    loop : Nat → Form → List NOM
    | 0, _     =>      []
    | n+1, φ   => ite (nom_occurs ⟨n⟩ φ) (⟨n⟩ :: loop n φ) (loop n φ)

  def Form.dbl_list_noms : Form → List NOM := λ φ =>
    loop φ.new_nom.letter φ
  where
    loop : Nat → Form → List NOM
    | 0, _     =>      []
    | n+1, φ   =>      ite (nom_occurs ⟨n⟩ φ) (⟨2*n⟩ :: loop n φ) (loop n φ)
  
  #eval (NOM.mk 2 ⋁ NOM.mk 3 ⋁ NOM.mk 4).list_noms
  #eval List.take 9 (NOM.mk 2 ⋁ NOM.mk 3 ⋁ NOM.mk 4).dbl_list_noms

--  theorem dream {φ : Form} (h1 : (h₁ :: t₁) = φ.double_list_noms) (h2 : (h₂ :: t₂) = φ.list_noms)

  def Form.bulk_subst : Form → List NOM → List NOM → Form
  | φ, h₁ :: t₁, h₂ :: t₂ => bulk_subst (φ[h₁ // h₂]) t₁ t₂
  | φ, _, []    =>  φ
  | φ, [], _    =>  φ

  def Form.dbl : Form → Form := λ φ => φ.bulk_subst φ.dbl_list_noms φ.list_noms

  #eval (NOM.mk 2 ⟶ NOM.mk 3 ⟶ NOM.mk 4).dbl

  lemma new_nom_gt      : nom_occurs i φ → i.letter < φ.new_nom.letter   := by
    induction φ with
    | nom i          =>
        simp [nom_occurs, Form.new_nom, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self i.letter
    | impl ψ χ ih1 ih2 =>
        simp only [nom_occurs, Form.new_nom, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box      =>
        assumption
    | bind     =>
        assumption
    | _ => simp [nom_occurs]

  lemma new_nom_is_nom  : nom_occurs (φ.new_nom) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_nom_gt h
    have b := Nat.lt_irrefl φ.new_nom.letter
    exact b a
  
  lemma ge_new_nom_is_new (h : x ≥ φ.new_nom) : nom_occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_nom_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_nom.letter
    exact b a

/-
  theorem all_lt_list_noms {φ : Form} : ∀ n, n < φ.new_nom.letter → ⟨n⟩ ∈ φ.list_noms := by
    rw [Form.list_noms]
    induction φ.new_nom.letter with
    | zero => simp
    | succ n ih =>
        intro i i_lt
        simp [Form.list_noms.loop] at ih ⊢
        apply Or.elim (ih i)
        . intro n_le
          apply Or.inl
          apply Nat.le_antisymm
          apply Nat.lt_add_one_iff.mp
          assumption
          assumption
        . clear i_lt ih
          intro hmem
          apply Or.inr
          assumption

  theorem all_lt_list_noms' {φ : Form} : ∀ n, ⟨n⟩ ∈ φ.list_noms ↔ n < φ.new_nom.letter := by
    intro n
    apply Iff.intro
    . rw [Form.list_noms]
      induction φ.new_nom.letter with
      | zero    => simp only [Form.list_noms.loop]; intro; contradiction
      | succ m ih =>
          simp [Form.list_noms.loop, -implication_disjunction]
          intro disj
          apply Or.elim disj
          . intro
            simp [*]
          . intro
            simp [*, Nat.lt_succ_of_lt] at *
    . exact all_lt_list_noms n
-/

  -- bit ugly but it works
  theorem occurs_list_noms : nom_occurs i φ ↔ i ∈ φ.list_noms := by
    rw [Form.list_noms]
    apply Iff.intro
    . intro h
      have := new_nom_gt h
      revert this
      induction φ.new_nom.letter with
      | zero => simp
      | succ n ih =>
          intro h2
          rw [Form.list_noms.loop]
          split
          . simp
            by_cases heq : i.letter = n
            . apply Or.inl
              rw [NOM.mk.injEq]
              assumption
            . simp [Nat.lt_succ_iff_lt_or_eq, heq] at h2
              apply Or.inr; apply ih; assumption
          . apply ih
            have : ¬i.letter = n := by
                intro habs
                have : i = {letter := n} := by rw [NOM.mk.injEq, habs]
                simp [*] at *
            simp [Nat.lt_succ_iff_lt_or_eq, this] at h2
            assumption
    . induction φ.new_nom.letter with
      | zero => simp [Form.list_noms.loop]
      | succ n ih =>
          intro h
          simp [Form.list_noms.loop] at h
          split at h
          . simp at h
            apply Or.elim h
            . intro; simp [*]
            . exact ih
          . apply ih; assumption

  theorem list_noms_subst {old new : NOM} : i ∈ (φ[new // old]).list_noms → ((i ∈ φ.list_noms ∧ i ≠ old) ∨ i = new) := by
    --rw [all_lt_list_noms', all_lt_list_noms']
    rw [←occurs_list_noms, ←occurs_list_noms]
    intro h
    induction φ with
    | nom j =>
        simp [nom_subst_nom] at h
        split at h
        . simp [nom_occurs] at h; apply Or.inr; assumption
        . apply Or.inl
          apply And.intro
          . assumption
          . simp [nom_occurs] at h
            rw [h]
            assumption
    | impl ψ χ ih1 ih2 =>
        simp [nom_occurs] at h ⊢
        apply Or.elim h
        . intro hyp
          apply Or.elim (ih1 hyp)
          . intro hl
            simp [hl]
          . intro hr
            simp [hr]
        . intro hyp
          apply Or.elim (ih2 hyp)
          . intro hl
            simp [hl]
          . intro hr
            simp [hr]
    | box ψ ih =>
        simp [nom_occurs] at h
        exact ih h
    | bind _ ψ ih =>
        simp [nom_occurs] at h
        exact ih h
    | _     => simp [nom_occurs] at h

  theorem occ_bulk {l_new l_old : List NOM} {φ : Form} (eq_len : l_new.length = l_old.length) : nom_occurs i (φ.bulk_subst l_new l_old) → ((i ∈ φ.list_noms ∧ i ∉ l_old) ∨ i ∈ l_new) := by
    intro h
    induction l_new generalizing φ l_old with
    | nil => cases l_old <;> simp [Form.bulk_subst] at *; repeat exact occurs_list_noms.mp h
    | cons h_new t_new ih =>
        cases l_old with
        | nil =>
            simp [Form.bulk_subst] at h ⊢
            apply Or.inl
            exact occurs_list_noms.mp h
        | cons h_old t_old =>
            simp [Form.bulk_subst] at eq_len h ⊢
            have := ih eq_len h
            apply Or.elim this
            . intro hyp
              clear this ih
              cases t_new
              . have := List.length_eq_zero.mp (Eq.symm (Eq.subst eq_len (@List.length_nil NOM)))
                simp [this, Form.bulk_subst] at h ⊢
                apply Or.elim (list_noms_subst (occurs_list_noms.mp h))
                . intro c1
                  simp [c1]
                . intro c2
                  exact Or.inr c2
              . cases t_old
                . simp at eq_len
                . simp [Form.bulk_subst] at hyp ⊢
                  have ⟨a, b⟩ := hyp
                  apply Or.elim (list_noms_subst b)
                  . intro c1
                    apply Or.inl
                    simp [c1, a]
                  . intro c2
                    simp [c2]
            . intro hyp
              clear this ih
              apply Or.inr
              apply Or.inr
              assumption

  -- FORM.DBL_LIST_NOMS DOESN'T HAVE THIS PROPERTY
  theorem nocc_bulk {l_new l_old : List NOM} {φ : Form} (eq_len : l_new.length = l_old.length) : ((i ∉ φ.list_noms ∨ i ∈ l_old) ∧ i ∉ l_new) → nom_occurs i (φ.bulk_subst l_new l_old) = false := by
    rw [contraposition]
    simp [-implication_disjunction]
    intro h1 h2
    apply Or.elim (occ_bulk eq_len h1)
    . simp
    . simp [h2]

  def map_odd : ℕ → NOM → NOM := λ off => λ h => ⟨h.letter*2 + off + (1 - off % 2)⟩ 
  def map_odd_inv : ℕ → NOM → NOM := λ off => λ h => ⟨(h.letter - (1 - off % 2) - off)/2⟩

  theorem map_odd_inv_is_inv : map_odd_inv off (map_odd off i) = i := by
    simp [map_odd_inv, map_odd]

  theorem map_odd_ge  : map_odd off i ≥ ⟨off⟩ := by
    simp [map_odd, NOM.le, Nat.add_comm, Nat.add_assoc]

  def Form.mapping1 : Form → Form := λ φ => φ.bulk_subst (φ.list_noms.map (map_odd φ.new_nom.letter)) φ.list_noms
  def Form.mapping2 : Form → Form := λ φ =>
    φ.mapping1.bulk_subst (φ.mapping1.list_noms.map (map_odd_inv φ.new_nom.letter)) φ.mapping1.list_noms

  theorem mapping_inv {φ : Form} : φ.mapping1.mapping2 = φ := by
    unfold Form.mapping1 Form.mapping2
    admit 

  theorem mapping1nocc : ∀ i : NOM, i ∈ (φ.list_noms.map (map_odd φ.new_nom.letter)) → nom_occurs i φ = false := by
    intro i hmem
    apply ge_new_nom_is_new
    simp at hmem
    have ⟨a, p1, _⟩ := hmem
    have := @map_odd_ge φ.new_nom.letter a
    rw [p1] at this
    exact this

  def all_nocc : List NOM → Form → Prop := λ l => λ φ =>  ∀ i, i ∈ l → nom_occurs i φ = false

/-
  theorem nom_nom_nom_subst {i j a : NOM} (h : nom_occurs i φ = false ∧ nom_occurs j φ = false) : φ[j // a] = φ[i // a][j // i] := by
    induction φ <;> simp [nom_subst_nom, nom_occurs, *, -implication_disjunction] at *
    . split <;> simp [nom_subst_nom, Ne.symm, h]
    . simp [h] at *
      apply And.intro
      repeat assumption
    repeat { simp [h.left, h.right] at *; assumption  }

  -- ((φ[a // b]).bulk_subst l1 l2)

  theorem remember {φ : Form} {h_new : NOM} : (φ.bulk_subst (h_old :: t) t_orig)[h_new // h_old] = φ.bulk_subst (h_new :: t) t_orig := sorry

  theorem triangle_subst {φ : Form} (l₁ l₂ : List NOM) (h1: all_nocc l₁ φ ∧ all_nocc l₂ φ) (h2 : l₁ ≠ [] ∧ l₂ ≠ []) :
      φ.bulk_subst l₁ φ.list_noms = (φ.bulk_subst l₂ φ.list_noms).bulk_subst l₁ l₂ := by
      induction φ.list_noms generalizing φ l₁ l₂ with
      | nil => simp [Form.bulk_subst]; admit
      | cons h_orig t_orig ih =>
          cases l₁ with
          | nil => simp at h2
          | cons head₁ tail₁ =>
              cases l₂ with
              | nil => simp at h2
              | cons head₂ tail₂ =>
                  rw [Form.bulk_subst, Form.bulk_subst, remember, Form.bulk_subst]
                  have nih := @ih (φ[head₁ // h_orig])
                  clear ih

                  --conv at ih => rhs; rw [Form.bulk_subst, remember]
                  
                  --simp only [Form.bulk_subst] at ih ⊢
                  admit
      /-
      cases l₁ with
      | nil => simp at h5
      | cons h₁ t₁ =>
          cases l₂ with
          | nil => simp at h5
          | cons h₂ t₂ =>
              simp [all_nocc, -implication_disjunction] at h1 h2
              clear h5
              revert h3 h4
              cases φ.list_noms
              . simp [Form.bulk_subst, -implication_disjunction]
                intro h3 h4
                rw [h3, h4]
                admit
              . simp [Form.bulk_subst, -implication_disjunction]
                intro h3 h4
                rw [h4]
                admit
        -/
-/
/-
  def Form.map_odd_list : Form → List NOM → ℕ → Form 
  | φ, [], _            => φ
  | φ, h :: t, offset   => 
      φ[map_odd_n offset h // h].map_odd_list t offset

  def Form.map_odd      : Form → Form := λ φ => φ.map_odd_list φ.nominals φ.new_nom.letter

  theorem eddie (φ : Form) : φ.map_odd.nominals = φ.nominals.map (map_odd_n φ.new_nom.letter) := by
    induction φ with
    | impl ψ χ ih1 ih2 =>
        simp [Form.map_odd]        
        admit
    | _ => admit 

  theorem helper {φ : Form} : ∀ i : NOM, nom_occurs i φ.map_odd → i ≥ φ.new_nom := by
    intro i
    rw [Form.map_odd]
    have h : φ.nominals = [] ↔ ∀ i : NOM, nom_occurs i φ = false := hmm φ
    revert h
    induction φ.nominals generalizing φ with
    | nil =>
        simp only [true_iff, Form.map_odd_list, ge_iff_le]
        intro a b
        exfalso
        have := Eq.mpr (Bool.eq_false_eq_not_eq_true (nom_occurs i φ)) (a i)
        contradiction
    | cons h t ih =>
        let ψ : Form := sorry
        have : t = ψ.nominals := sorry
        rw [this] at ih
        have new_ih := ih (hmm ψ)
        clear ih
        simp only [Form.map_odd_list]
        intro c hocc
        clear c
        admit

  def Form.double_list : Form → List NOM → Form
  | φ, []       => φ
  | φ, h :: t   => φ [NOM.mk (h.letter * 2) // h].double_list t

  def Form.half_list : Form → List NOM → Form
  | φ, []       => φ
  | φ, h :: t   => φ [NOM.mk (h.letter / 2) // h].double_list t

  def Form.double  : Form → Form   :=   λ φ => φ.double_list (φ.nominals)
  def Form.half    : Form → Form   :=   λ φ => φ.half_list (φ.nominals)

--  notation:150 φ "*2" => Form.double φ
--  notation:150 φ "/2" => Form.half φ

  def Set.double : Set Form → Set Form := λ Γ => {Form.double φ | φ ∈ Γ}
  def Set.half   : Set Form → Set Form := λ Γ => {Form.half φ | φ ∈ Γ}

  def Form.double_n : Form → ℕ → Form
  | φ, 0         => φ
  | φ, n+1       => (nom_subst_nom φ ⟨2*(n+1)⟩ ⟨n+1⟩).double_n n

  def Form.double'  : Form → Form   := λ φ => φ.double_n φ.new_nom.letter

  def Form.double''  : Form → Form   := λ φ =>
    loop φ φ.new_nom.letter
  where
    loop : Form → ℕ → Form
    | φ, 0      => φ
    | φ, n+1    => loop (nom_subst_nom φ ⟨2*n⟩ ⟨n⟩) n


  #eval (NOM.mk 3 ⋁ NOM.mk 6).double''
--  notation:150 Γ "*2" => Set.double Γ 
--  notation:150 Γ "/2" => Set.half Γ 
-/
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
