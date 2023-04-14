import Hybrid.Form

-- Axiom utils. Since we won't be assuming a transitive frame,
-- it will make sense to be able to construct formulas with
-- iterated modal operators at their beginning (ex., for axiom nom)
def iterate_nec (n : Nat) (φ : Form) : Form :=
  let rec loop : Nat → Form → Form
    | 0, φ   => φ
    | n+1, φ => □ (loop n φ)
  loop n φ

def iterate_pos (n : Nat) (φ : Form) : Form :=
  let rec loop : Nat → Form → Form
    | 0, φ   => φ
    | n+1, φ => ◇ (loop n φ)
  loop n φ

inductive Proof (Γ : set Form) : Form → Type where
  -- Deduction rules:
  -- all premises (elements of Γ) can be deduced from Γ
  | premise {φ : Form}:
        (φ ∈ Γ) → Proof Γ φ

  -- if φ can be deduced from Γ, then so can ∀ v, φ
  -- todo: add restrictions 
  | general {φ : Form} {t : SVAR} {v : SVAR}:
        Proof Γ φ → Proof Γ (all v, φ) 

  -- if φ can be deduced from Γ, then so can □ φ
  | necess {φ : Form}:
        Proof Γ φ → Proof Γ (□ φ)

  -- modus ponens:
  | ponens {φ ψ : Form}:
        Proof Γ (φ ⟶ ψ) → Proof Γ φ → Proof Γ ψ

  -- add all instances of propositional tautologies...

  -- Axioms for modal + hybrid logic:
  -- distribution schema (axiom K)
  | ax_k {φ ψ : Form}:
        Proof Γ (□ (φ ⟶ ψ) ⟶ (□ φ ⟶ □ ψ))

  | ax_q1 {φ ψ : Form} {v : SVAR} (p : ¬ is_free v φ):
        Proof Γ ((all v, φ ⟶ ψ) ⟶ (φ ⟶ all v, ψ))

  -- two different instances of Axiom Q2: one for SVAR, one for NOM
  | ax_q2_svar {φ : Form} (v : SVAR) (s : SVAR) (p : is_substable φ s v):
      Proof Γ ((all v, φ) ⟶ φ[s // v])

  | ax_q2_nom  {φ ψ : Form} (v : SVAR) (s : NOM):
      Proof Γ ((all v, φ) ⟶ φ[s // v])

  | ax_name (v : SVAR):
      Proof Γ (ex v, v)

  | ax_nom {φ : Form} {v : SVAR} (n m : Nat):
      Proof Γ (iterate_pos n (φ ⋀ v) ⟶ iterate_nec m (v ⟶ φ))

  | ax_brcn {φ : Form} {v : SVAR}:
      Proof Γ (all v, (□ φ) ⟶ (□ all v, φ))

def Theorem {φ : Form} := ∀ Γ : set Form, Proof Γ φ  

infix:500 "⊢"  => Proof
prefix:500 "⊢" => Theorem