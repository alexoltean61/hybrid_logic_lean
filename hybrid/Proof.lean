import Hybrid.Form
import Hybrid.Tautology

inductive Proof : Form → Prop where
  -- Deduction rules:

  -- if φ is a theorem, ∀ v, φ is a theorem
  | general {φ : Form} (v : SVAR):
        Proof φ → Proof (all v, φ)

  -- if φ is a theorem, □ φ is a theorem 
  | necess (φ : Form):
        Proof φ → Proof (□ φ)

  -- modus ponens:
  | mp {φ ψ : Form}:
        Proof (φ ⟶ ψ) → Proof φ → Proof ψ

  -- All propositional tautologies
  | tautology {φ : Form}:
        Tautology φ → Proof φ

  -- Axioms for modal + hybrid logic:
  -- distribution schema (axiom K)
  | ax_k {φ ψ : Form}:
        Proof (□ (φ ⟶ ψ) ⟶ (□ φ ⟶ □ ψ))

  | ax_q1 (φ ψ : Form) {v : SVAR} (p : is_free v φ = false):
        Proof ((all v, φ ⟶ ψ) ⟶ (φ ⟶ all v, ψ))

  -- two different instances of Axiom Q2: one for SVAR, one for NOM
  | ax_q2_svar (φ : Form) (v s : SVAR) (p : is_substable φ s v):
      Proof ((all v, φ) ⟶ φ[s // v])

  | ax_q2_nom (φ : Form) (v : SVAR) (s : NOM):
      Proof ((all v, φ) ⟶ φ[s // v])

  | ax_name (v : SVAR):
      Proof (ex v, v)

  | ax_nom {φ : Form} {v : SVAR} (m n : Nat):
      Proof (all v, (iterate_pos m (v ⋀ φ) ⟶ iterate_nec n (v ⟶ φ)))

  | ax_brcn {φ : Form} {v : SVAR}:
      Proof ((all v, □ φ) ⟶ (□ all v, φ))

def SyntacticConsequence (Γ : Set Form) (φ : Form) : Prop := ∃ L, Proof ((conjunction Γ L) ⟶ φ)  


prefix:500 "⊢"  => Proof
infix:500 "⊢"   => SyntacticConsequence

notation "⊬" φ    => ¬ (Proof φ)
notation Γ "⊬" φ  => ¬ (SyntacticConsequence Γ φ) 

def Set.consistent (Γ : Set Form) := Γ ⊬ ⊥

def Set.MCS (Γ : Set Form) := Γ.consistent ∧ (∀ φ : Form, (¬φ ∈ Γ) → (Γ ∪ {φ}) ⊢ ⊥)

def Set.witnessed (Γ : Set Form) : Prop := ∀ {φ : Form},
  φ ∈ Γ → 
    match φ with 
      | ex x, ψ => ∃ i : NOM, ((ex x, ψ) ⟶ ψ[i // x]) ∈ Γ 
      | _   => φ ∈ Γ