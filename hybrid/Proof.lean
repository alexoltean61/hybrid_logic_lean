import Hybrid.Form

inductive Proof : Form → Prop where
  -- Deduction rules:

  -- if φ can be deduced from Γ, then so can ∀ v, φ
  -- todo: add restrictions 
  | general {φ : Form}:
        Proof φ → Proof (all v, φ)

  -- if φ is a theorem, □ φ can be deduced from any Γ 
  | necess {φ : Form}:
        Proof φ → Proof (□ φ)

  -- modus ponens:
  | ponens {φ ψ : Form}:
        Proof (φ ⟶ ψ) → Proof φ → Proof ψ

  -- add all instances of propositional tautologies...
  | tautology₁ {φ ψ : Form}:
        Proof (φ ⟶ (ψ ⟶ φ))
  | tautology₂ {φ ψ χ : Form}:
        Proof ((φ ⟶ (ψ ⟶ χ)) ⟶ ((φ ⟶ ψ) ⟶ (φ ⟶ χ))) 
  | tautology₃ {φ ψ : Form}:
        Proof ((∼φ ⟶ ∼ψ) ⟶ (ψ ⟶ φ))

  -- Axioms for modal + hybrid logic:
  -- distribution schema (axiom K)
  | ax_k {φ ψ : Form}:
        Proof (□ (φ ⟶ ψ) ⟶ (□ φ ⟶ □ ψ))

  | ax_q1 {φ ψ : Form} {v : SVAR} (p : ¬ is_free v φ):
        Proof ((all v, φ ⟶ ψ) ⟶ (φ ⟶ all v, ψ))

  -- two different instances of Axiom Q2: one for SVAR, one for NOM
  | ax_q2_svar {φ : Form} (v : SVAR) (s : SVAR) (p : is_substable φ s v):
      Proof ((all v, φ) ⟶ φ[s // v])

  | ax_q2_nom {φ : Form} (v : SVAR) (s : NOM):
      Proof ((all v, φ) ⟶ φ[s // v])

  | ax_name (v : SVAR):
      Proof (ex v, v)

  | ax_nom {φ : Form} {v : SVAR} (m n : Nat):
      Proof (all v, (iterate_pos m (v ⋀ φ) ⟶ iterate_nec n (v ⟶ φ)))

  | ax_brcn {φ : Form} {v : SVAR}:
      Proof ((all v, □ φ) ⟶ (□ all v, φ))

def SyntacticConsequence (Γ : List Form) (φ : Form) : Prop := Proof ((conjunction Γ) ⟶ φ)  

prefix:500 "⊢"  => Proof
infix:500 "⊢"   => SyntacticConsequence

notation "⊬" φ    => ¬ (Proof φ)
notation Γ "⊬" φ  => ¬ (SyntacticConsequence Γ φ) 

def consistent_set (Γ : List Form) := Γ ⊬ ⊥ 