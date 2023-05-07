import Hybrid.Form

inductive Proof : set Form → Form → Type where
  -- Deduction rules:
  -- all premises (elements of Γ) can be deduced from Γ
  | premise {Γ : set Form} {φ : Form}:
        (φ ∈ Γ) → Proof Γ φ

  -- if φ can be deduced from Γ, then so can ∀ v, φ
  -- todo: add restrictions 
  | general {Γ : set Form} {φ : Form} (v t : SVAR)
      (restrict₁ : ∀ ψ : Form, ((ψ ∈ Γ) → occurs t ψ = false))
      (restrict₂ : occurs v φ = false):    -- (restrict₂ : is_substable φ v t):
        Proof Γ φ → Proof Γ (all v, φ[v // t]) 

  -- if φ is a theorem, □ φ can be deduced from any Γ 
  | necess {Γ : set Form} {φ : Form}:
        (∀ Δ : set Form, Proof Δ φ) → Proof Γ (□ φ)

  -- modus ponens:
  | ponens {Γ : set Form} {φ ψ : Form}:
        Proof Γ (φ ⟶ ψ) → Proof Γ φ → Proof Γ ψ

  -- add all instances of propositional tautologies...
  | tautology₁ {Γ : set Form} {φ ψ : Form}:
        Proof Γ (φ ⟶ (ψ ⟶ φ))
  | tautology₂ {Γ : set Form} {φ ψ χ : Form}:
        Proof Γ ((φ ⟶ (ψ ⟶ χ)) ⟶ ((φ ⟶ ψ) ⟶ (φ ⟶ χ))) 
  | tautology₃ {Γ : set Form} {φ ψ : Form}:
        Proof Γ ((∼φ ⟶ ∼ψ) ⟶ (ψ ⟶ φ))

  -- Axioms for modal + hybrid logic:
  -- distribution schema (axiom K)
  | ax_k {Γ : set Form} {φ ψ : Form}:
        Proof Γ (□ (φ ⟶ ψ) ⟶ (□ φ ⟶ □ ψ))

  | ax_q1 {Γ : set Form} {φ ψ : Form} {v : SVAR} (p : ¬ is_free v φ):
        Proof Γ ((all v, φ ⟶ ψ) ⟶ (φ ⟶ all v, ψ))

  -- two different instances of Axiom Q2: one for SVAR, one for NOM
  | ax_q2_svar {Γ : set Form} {φ : Form} (v : SVAR) (s : SVAR) (p : is_substable φ s v):
      Proof Γ ((all v, φ) ⟶ φ[s // v])

  | ax_q2_nom  {Γ : set Form} {φ : Form} (v : SVAR) (s : NOM):
      Proof Γ ((all v, φ) ⟶ φ[s // v])

  | ax_name {Γ : set Form} (v : SVAR):
      Proof Γ (ex v, v)

  | ax_nom {Γ : set Form} {φ : Form} {v : SVAR} (m n : Nat):
      Proof Γ (all v, (iterate_pos m (v ⋀ φ) ⟶ iterate_nec n (v ⟶ φ)))

  | ax_brcn {Γ : set Form} {φ : Form} {v : SVAR}:
      Proof Γ ((all v, □ φ) ⟶ (□ all v, φ))

def Theorem {φ : Form} := ∀ Γ : set Form, Proof Γ φ  

infix:500 "⊢"  => Proof
prefix:500 "⊢" => Theorem