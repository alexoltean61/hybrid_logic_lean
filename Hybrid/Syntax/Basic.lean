import Hybrid.Util.Util
namespace Hybrid

def TotalSet := {n : ℕ | True}

structure PROP where
  letter : ℕ
deriving DecidableEq, Repr

structure SVAR where
  letter : ℕ
deriving DecidableEq, Repr

structure NOM (N : Set ℕ) where
  letter : N
deriving DecidableEq, Repr

inductive StateSymb (N : Set ℕ) where
  | SVAR : SVAR  → StateSymb N
  | NOM  : NOM N → StateSymb N
deriving DecidableEq, Repr

-- We parameterize hybrid languages (the type Form) by
--    a set of natural numbers N
inductive Form (N : Set ℕ) where
  | bttm : Form N
  | prop : PROP   → Form N
  | svar : SVAR   → Form N
  | nom  :  NOM N → Form N
  | impl : Form N → Form N → Form N
  | box  : Form N → Form N
  | bind :   SVAR → Form N → Form N
deriving DecidableEq, Repr

def Form.depth : Form N → ℕ
  | .impl φ ψ =>  1 + Form.depth φ + Form.depth ψ
  | .box  φ   =>  1 + Form.depth φ
  | .bind _ φ =>  2 + Form.depth φ
  | _       =>    0

def NOM.total : NOM N → NOM TotalSet := λ i => ⟨⟨i.letter, trivial⟩⟩

def Form.total : Form N → Form TotalSet
  | .bttm     => Form.bttm
  | .prop p   => Form.prop p
  | .svar v   => Form.svar v
  | .nom i    => Form.nom ⟨i.1.1, trivial⟩
  | .impl ψ χ => Form.impl ψ.total χ.total
  | .box ψ    => Form.box ψ.total
  | .bind v ψ => Form.bind v ψ.total

@[simp] def Form.neg      : Form N → Form N := λ φ => Form.impl φ Form.bttm
@[simp] def Form.conj     : Form N → Form N → Form N := λ φ => λ ψ => Form.neg (Form.impl φ (Form.neg ψ))
@[simp] def Form.iff      : Form N → Form N → Form N := λ φ => λ ψ => Form.conj (Form.impl φ ψ) (Form.impl ψ φ)
@[simp] def Form.disj     : Form N → Form N → Form N := λ φ => λ ψ => Form.impl (Form.neg φ) ψ
@[simp] def Form.diamond  : Form N → Form N := λ φ => Form.neg (Form.box (Form.neg φ))
@[simp,match_pattern]
def Form.bind_dual: SVAR → Form N → Form N := λ x => λ φ => Form.neg (Form.bind x (Form.neg φ))

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



-- Since we won't be assuming a transitive frame,
-- it will make sense to be able to construct formulas with
-- iterated modal operators at their beginning (ex., for axiom nom)
def iterate_nec (n : Nat) (φ : Form N) : Form N :=
  let rec loop : Nat → Form  N → Form N
    | 0, φ   => φ
    | n+1, φ => □ (loop n φ)
  loop n φ

def iterate_pos (n : Nat) (φ : Form N) : Form N :=
  let rec loop : Nat → Form N → Form N
    | 0, φ   => φ
    | n+1, φ => ◇ (loop n φ)
  loop n φ




-- We define what it is to conjunct the (finitely many) formulas in a list
--    Convention: the conjunction of the empty list is "T" (⊥ ⟶ ⊥)
--
-- We will be interested in expressing such statements as:
--    "Given a set Γ of formulas, there is a finite subset of Γ such that its conjunction proves φ"
--
-- Q: how shall we implement the notion of "conjunction of a finite subset"?
-- A: we make use of Lean's and Mathlib'a subtyping system, and we define the conjunction function on
--    *lists of elements in Γ*, not on lists of formulas in general:
def conjunction (Γ : Set (Form N)) (L : List Γ) : Form N :=
match L with
  | []     => ⊥ ⟶ ⊥
  | h :: t => h.val ⋀ conjunction Γ t


instance : Coe SVAR (StateSymb N) := ⟨StateSymb.SVAR⟩
instance explicit : Coe (NOM N) (StateSymb N) := ⟨StateSymb.NOM⟩

instance coePROP : Coe PROP     (Form N)  := ⟨Form.prop⟩
instance coeSVAR : Coe SVAR     (Form N)  := ⟨Form.svar⟩
instance coeNOM  : Coe (NOM N)  (Form N)  := ⟨Form.nom⟩
instance coeSSymb: Coe (StateSymb N) (Form N) := ⟨
    λ s => match s with
          | .SVAR x =>  x
          | .NOM i  =>  i
  ⟩

instance : Coe Nat PROP      := ⟨PROP.mk⟩
instance : Coe Nat SVAR      := ⟨SVAR.mk⟩
instance : Coe PROP Nat      := ⟨PROP.letter⟩
instance : Coe SVAR Nat      := ⟨SVAR.letter⟩
instance : OfNat PROP n      := ⟨PROP.mk n⟩
instance : OfNat SVAR n      := ⟨SVAR.mk n⟩

lemma PROP_eq {x y : PROP} : (x = y) ↔ (x.letter = y.letter) := by
  cases x
  cases y
  simp
lemma SVAR_eq {x y : SVAR} : (x = y) ↔ (x.letter = y.letter) := by
  cases x
  cases y
  simp
lemma NOM_eq {i j : NOM S} : (i = j) ↔ (i.letter = j.letter) := by
  cases i
  cases j
  simp
lemma NOM_eq' {i j : NOM S} : (i = j) ↔ (j.letter = i.letter) := by
  rw [NOM_eq, eq_comm]

instance : LinearOrder PROP := LinearOrder.lift' PROP.letter (λ _ _ => PROP_eq.mpr)
instance : LinearOrder SVAR := LinearOrder.lift' SVAR.letter (λ _ _ => SVAR_eq.mpr)
instance : LinearOrder (NOM N) := LinearOrder.lift' NOM.letter (λ _ _ => NOM_eq.mpr)

/-
@[simp] instance PROP.le : LE PROP   := ⟨λ p => λ q =>  p.letter ≤ q.letter⟩
@[simp] instance PROP.lt : LT PROP   := ⟨λ p => λ q =>  p.letter < q.letter⟩
@[simp] instance SVAR.le : LE SVAR   := ⟨λ x => λ y =>  x.letter ≤ y.letter⟩
@[simp] instance SVAR.lt : LT SVAR   := ⟨λ x => λ y =>  x.letter < y.letter⟩
@[simp] instance NOM.le : LE (NOM S) := ⟨λ x => λ y =>  x.letter ≤ y.letter⟩
@[simp] instance NOM.lt : LT (NOM S) := ⟨λ x => λ y =>  x.letter < y.letter⟩

@[simp] instance PROP.max : Max PROP          := ⟨λ p => λ q => ite (p > q) p q⟩
@[simp] instance NOM.max  : Max (NOM N)       := ⟨λ i => λ j => ite (i > j) i j⟩
@[simp] instance SVAR.max : Max SVAR          := ⟨λ x => λ y => ite (x > y) x y⟩
-/
/-
instance : DecidableRel (@LE.le (NOM N) NOM.le) := λ n m => if h : (n.letter ≤ m.letter) then (isTrue h) else (isFalse h)
instance : DecidableRel (@LE.le SVAR SVAR.le) := λ n m => if h : (n.letter ≤ m.letter) then (isTrue h) else (isFalse h)
@[simp] instance : Max (NOM N) := maxOfLe
@[simp] instance : Max SVAR    := maxOfLe

instance : IsTrans (NOM S) GT.gt := ⟨λ _ _ _ h1 h2 => Nat.lt_trans h2 h1⟩
instance : IsTotal (NOM S) GE.ge where
  total := by simp [NOM.le, LE.le, Nat.le_total]
instance : IsTrans (NOM S) GE.ge := ⟨λ _ _ _ h1 h2 => Nat.le_trans h2 h1⟩
-/


@[simp] instance SVAR.add : HAdd SVAR Nat SVAR where
  hAdd  := λ x => λ n => (x.letter + n)
@[simp] instance NOM.add : HAdd (NOM TotalSet) Nat (NOM TotalSet) where
  hAdd  := λ x => λ n => ⟨(x.letter + n), trivial⟩
@[simp] instance : HSub (NOM TotalSet) Nat (NOM TotalSet) where
  hSub  := λ x => λ n => ⟨(x.letter - n), trivial⟩
@[simp] instance : HMul (NOM TotalSet) Nat (NOM TotalSet) where
  hMul  := λ x => λ n => ⟨(x.letter * n), trivial⟩
@[simp] instance : HDiv (NOM TotalSet) Nat (NOM TotalSet) where
  hDiv  := λ x => λ n => ⟨(x.letter / n), trivial⟩
@[simp] instance NOM.hmul : HMul Nat (NOM TotalSet) (NOM TotalSet) where
  hMul  := λ n => λ x => ⟨(x.letter * n), trivial⟩
@[simp] instance : HMul (NOM TotalSet) ℕ ℕ where
  hMul  := λ x => λ n => x.letter * n

instance : OfNat (NOM TotalSet) n := ⟨NOM.mk  ⟨n, trivial⟩⟩


def Form.list_noms : (Form N) → List (NOM N)
| nom  i   => [i]
| impl φ ψ => (List.merge GE.ge φ.list_noms ψ.list_noms).dedup
| box φ    => φ.list_noms
| bind _ φ => φ.list_noms
| _        => []

/-
def Form.odd_list_noms : Form TotalSet → List (NOM TotalSet) := λ φ => φ.list_noms.map (λ i => 2*i+1)

def Form.odd_noms : Form TotalSet → Form TotalSet := λ φ => φ.bulk_subst φ.odd_list_noms φ.list_noms

def Set.odd_noms : Set (Form TotalSet) → Set (Form TotalSet) := λ Γ => {Form.odd_noms φ | φ ∈ Γ}

def nocc_bulk_property (l1 l2 : List (NOM TotalSet)) (φ : Form TotalSet) := ∀ {n : Fin l1.length} {i : NOM TotalSet}, (i = l1[n]) → (i ∉ φ.list_noms ∨ i ∈ l2.take n) ∧ i ∉ l1.take n
-/


/- At first sight, having a *type class* of for state symbols makes more sense. -/
/- This would be the implementation: -/
/-
class StateSymb (α : Type) (N : Set ℕ) where
  sort : PSum (α = SVAR) (α = NOM N)

instance {N : Set ℕ} : StateSymb SVAR N := ⟨PSum.inl (refl SVAR)⟩
instance : StateSymb (NOM N) N  := ⟨PSum.inr (refl (NOM N))⟩

--  Coerce a state symbol to a formula of the appropiate kind:
instance coeStateSymb [inst : StateSymb α N] (s : α) : CoeDep α s (Form N) where
  coe := match inst.sort with
         | PSum.inl x  => Form.svar (x ▸ s)
         | PSum.inr i  => Form.nom (i ▸ s)
-/

/- However, this generates a LOT of instance-related headaches. Better stick to the -/
/-  inductive type StateSymb.     -/
