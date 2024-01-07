import Hybrid.Form
import Hybrid.Tautology

inductive Proof : Form N → Type where
  -- Deduction rules:

  -- if φ is a theorem, ∀ v, φ is a theorem
  | general {φ : Form N} (v : SVAR):
        Proof φ → Proof (all v, φ)

  -- if φ is a theorem, □ φ is a theorem
  | necess {φ : Form N}:
        Proof φ → Proof (□ φ)

  -- modus ponens:
  | mp {φ ψ : Form N}:
        Proof (φ ⟶ ψ) → Proof φ → Proof ψ

  -- All propositional tautologies
  | tautology {φ : Form N}:
        Tautology φ → Proof φ

  -- Axioms for modal + hybrid logic:
  -- distribution schema (axiom K)
  | ax_k {φ ψ : Form N}:
        Proof (□ (φ ⟶ ψ) ⟶ (□ φ ⟶ □ ψ))

  | ax_q1 (φ ψ : Form N) {v : SVAR} (p : is_free v φ = false):
        Proof ((all v, φ ⟶ ψ) ⟶ (φ ⟶ all v, ψ))

  -- two different instances of Axiom Q2: one for SVAR, one for NOM
  | ax_q2_svar (φ : Form N) (v s : SVAR) (p : is_substable φ s v):
      Proof ((all v, φ) ⟶ φ[s // v])

  | ax_q2_nom (φ : Form N) (v : SVAR) (s : NOM N):
      Proof ((all v, φ) ⟶ φ[s // v])

  | ax_name (v : SVAR):
      Proof (ex v, v)

  | ax_nom {φ : Form N} {v : SVAR} (m n : Nat):
      Proof (all v, (iterate_pos m (v ⋀ φ) ⟶ iterate_nec n (v ⟶ φ)))

  | ax_brcn {φ : Form N} {v : SVAR}:
      Proof ((all v, □ φ) ⟶ (□ all v, φ))

def Proof.size : Proof φ → ℕ
  | .general _ pf => pf.size + 1
  | .necess pf    => pf.size + 1
  | .mp pf1 pf2   => pf1.size + pf2.size + 1
  | _ => 1

def Proof.contains {φ : Form N} : Proof φ → Form N → Bool :=
  λ pf ψ => φ == ψ ||
    match pf with
    | .general _ pf' => pf'.contains φ
    | .necess pf'    => pf'.contains φ
    | .mp pf1 pf2    => pf1.contains φ || pf2.contains φ
    | _ => false

def Proof.fresh_var : Proof φ → SVAR → Prop := λ pf x => ∀ ψ, pf.contains ψ → x ≥ ψ.new_var

def SyntacticConsequence (Γ : Set (Form N)) (φ : Form N) := Σ L, Proof ((conjunction Γ L) ⟶ φ)

prefix:500 "⊢"  => Proof
infix:500 "⊢"   => SyntacticConsequence

notation "⊬" φ    => (Proof φ) → False
notation Γ "⊬" φ  => (SyntacticConsequence Γ φ) → False


def consistent (Γ : Set (Form N)) := ∀ (_ : SyntacticConsequence Γ ⊥), False

def MCS (Γ : Set (Form N)) := consistent Γ ∧ (∀ {φ : Form N}, (¬φ ∈ Γ) → ¬consistent (Γ ∪ {φ}))

def witnessed (Γ : Set (Form N)) : Prop := ∀ {φ : Form N},
  φ ∈ Γ →
    match φ with
--      | ex x, ψ => ∃ i : NOM, ((ex x, ψ) ⟶ ψ[i // x]) ∈ Γ
      | ex x, ψ => ∃ i : NOM N, ψ[i // x] ∈ Γ
      | _   => φ ∈ Γ
