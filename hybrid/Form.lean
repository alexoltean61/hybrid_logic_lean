import Hybrid.Util

def set (α : Type u) := α → Prop
def member {α : Type u} (A : set α) (a : α) := A a
notation a "∈" A => member A a

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
  deriving Repr

  @[simp]
  def Form.neg      : Form → Form := λ φ => Form.impl φ Form.bttm
  @[simp]
  def Form.conj     : Form → Form → Form := λ φ => λ ψ => Form.neg (Form.impl φ (Form.neg ψ))
  @[simp]
  def Form.disj     : Form → Form → Form := λ φ => λ ψ => Form.impl (Form.neg φ) ψ
  @[simp]
  def Form.diamond  : Form → Form := λ φ => Form.neg (Form.box (Form.neg φ))
  @[simp]
  def Form.bind_dual: SVAR → Form → Form := λ x => λ φ => Form.neg (Form.bind x (Form.neg φ))

  instance : Coe PROP Form  := ⟨Form.prop⟩
  instance : Coe SVAR Form  := ⟨Form.svar⟩
  instance : Coe NOM  Form  := ⟨Form.nom⟩

  infixr:60 "⟶" => Form.impl
  infixl:65 "⋀" => Form.conj
  infixl:65 "⋁" => Form.disj
  prefix:70 "∼" => Form.neg
  prefix:100 "□" => Form.box
  prefix:100 "◇ " => Form.diamond
  notation:120 "all " x ", " φ => Form.bind x φ
  notation:120 "ex " x ", " φ => Form.bind_dual x φ
  notation "⊥"  => Form.bttm
end Basics

section Variables
  instance : LT SVAR where
    lt := λ x y => x.letter < y.letter  
  instance : HAdd SVAR Nat SVAR where
    hAdd := λ v n => { letter := v.letter + n }
  instance : HAdd Nat SVAR SVAR where
    hAdd := λ n v => { letter := v.letter + n }
  instance (x y : SVAR) : Decidable (x < y) :=
      dite (x.letter < y.letter) (λ tr => isTrue tr) (λ fls => isFalse fls)

  def max_svar (l : List SVAR) : SVAR :=
    match l with
      | []     => {letter := (default : Nat)}
      | h :: t => max h (max_svar t)
  
  def list_vars (φ : Form) : List SVAR :=
    match φ with
    | Form.svar x   => [x]
    | Form.impl φ ψ => (list_vars φ) ++ (list_vars ψ)
    | Form.box φ    => list_vars φ
    | Form.bind _ φ => list_vars φ
    | _             => []

  def occurs (x : SVAR) (φ : Form) : Bool := (list_vars φ).contains x

  def get_fresh_var (φ : Form) : SVAR := {letter := (max_svar (list_vars φ)).letter + 1}
end Variables

section Substitutions
  def is_free (x : SVAR) (φ : Form) : Prop :=
    match φ with
    | Form.bttm     => True
    | Form.prop _   => True
    | Form.svar _   => True
    | Form.nom  _   => True
    | Form.impl φ ψ => (is_free x φ) ∨ (is_free x ψ)
    | Form.box  φ   => is_free x φ
    | Form.bind y φ => ite (y = x) False (is_free x φ)

  instance DecidableIsFree : Decidable (is_free x φ) := by
    match φ with
    | Form.bttm     => exact isTrue trivial
    | Form.prop _   => exact isTrue trivial
    | Form.svar _   => exact isTrue trivial
    | Form.nom  _   => exact isTrue trivial
    | Form.box  φ   => exact (@DecidableIsFree x φ)
    | Form.impl φ ψ =>
        have ih_1 := @DecidableIsFree x φ
        have ih_2 := @DecidableIsFree x ψ
        match ih_1 with
        | isTrue p  => exact isTrue (Or.inl p)
        | isFalse p =>
            match ih_2 with
            | isTrue  q => exact isTrue (Or.inr q)
            | isFalse q => exact isFalse (negated_disjunction.mpr ⟨p, q⟩)
    | Form.bind y φ =>
        have ih := @DecidableIsFree x φ
        match ih with
        | isTrue p =>
            exact dite (y = x) (λ eq =>
                    isFalse (show ¬is_free x (all y, φ) by
                      intro t
                      unfold is_free at t
                      rw [if_pos eq] at t
                      exact t)
                    )
                  (λ neq =>
                    isTrue (show is_free x (all y, φ) by
                      unfold is_free
                      rw [if_neg neq]
                      assumption)
                    )
        | isFalse p =>
            exact dite (y = x) (λ eq =>
                    isFalse (show ¬is_free x (all y, φ) by
                      intro t
                      unfold is_free at t
                      rw [if_pos eq] at t
                      exact t)
                    )
                  (λ neq =>
                    isFalse (show ¬is_free x (all y, φ) by
                      unfold is_free
                      rw [if_neg neq]
                      assumption)
                    )

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

  def is_substable (φ : Form) (s : SVAR) (x : SVAR) : Prop :=
    match φ with
    | Form.bttm     => True
    | Form.prop _   => True
    | Form.svar _   => True
    | Form.nom  _   => True
    | Form.impl φ ψ => (is_substable φ s x) ∧ (is_substable ψ s x)
    | Form.box  φ   => is_substable φ s x
    | Form.bind y φ => ite (¬is_free x φ) True (ite (s ≠ y) (is_substable φ s x) False)
    -- all s, s ⟶ (all x, x)  : safe,   substitution won't do anything
    -- all x, x                : safe,   substitution won't do anything
    -- all y, y ⟶ x           : safe,   result will be   all y, y ⟶ s
    -- all s, y ⟶ x           : UNSAFE, substitution would make x bound
    --                                      where it was previously free
    --
    -- Takeaway: s is substable for all free occurences of x only as long
    --         as x *does not occur free in the scope of an s-quantifier*


--  class Subst (α : Type) where
--    subst : Form → α → SVAR → Form
  
--  instance : Subst SVAR where
--    subst := subst_svar
--  instance : Subst NOM where
--    subst := subst_nom

--  def substitute [Subst α] (φ : Form) (s : α) (x : SVAR) : Form :=
--    Subst.subst φ s x

  notation:150 φ "[" s "//" x "]" => subst_svar φ s x
  notation:150 φ "[" s "//" x "]" => subst_nom  φ s x

  theorem preserve_boundness {φ : Form} {x v : SVAR} : ¬is_free x φ → (¬ is_free x (all v, φ)) := by
    intro h1 h2
    simp [is_free] at h2
    by_cases v_x : v = x
    . simp [v_x] at h2
    . simp [v_x] at h2
      exact show False from h1 h2

  theorem subst_bound_var {φ : Form} {x y : SVAR} (h : ¬is_free x φ) : (φ[y // x] = φ) := by
    induction φ with
    | svar v =>
        by_cases x_v : x = v
        . conv at h => rhs ; simp [is_free]
          simp at h
        . simp [subst_svar, x_v]
    | impl ψ χ ind₁ ind₂ =>
        simp [is_free, negated_disjunction] at h
        conv =>
          lhs
            simp [subst_svar]
            congr
            . rw [ind₁ h.left]
            . rw [ind₂ h.right]
    | box ψ ind =>
        simp [is_free] at h
        simp [subst_svar]
        apply ind
        assumption
    | bind v ψ ind =>
        simp [is_free] at h
        by_cases v_x : v = x
        . conv =>
            lhs
              simp [subst_svar, v_x]
          simp [v_x]
        . simp [is_free, v_x] at h
          conv =>
            lhs
              simp [subst_svar, Ne.symm v_x]
              rhs rw [ind h]
      | _ => simp [subst_svar]

  theorem not_bound_when_quantified : ¬is_free x (all x, φ) := by
    intro h
    simp [is_free] at h

end Substitutions

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