import Hybrid.Syntax.Basic
namespace Hybrid

def occurs (s : StateSymb N) : Form N → Bool
| .bttm     => false
| .prop _   => false
| .svar x   => s == x
| .nom  i   => s == i
| .impl φ ψ => (occurs s φ) || (occurs s ψ)
| .box  φ   => occurs s φ
| .bind _ φ => occurs s φ

def is_free (x : SVAR) : Form N → Bool
| .bttm     => false
| .prop _   => false
| .svar y   => x == y
| .nom  _   => false
| .impl φ ψ => (is_free x φ) || (is_free x ψ)
| .box  φ   => is_free x φ
| .bind y φ => (y != x) && (is_free x φ)

def is_bound (x : SVAR) (φ : Form N) := (occurs x φ) && !(is_free x φ)

-- subst φ s₂ s₁ : substitute s₂ for all (free) occurrences of s₁ in φ
def subst : Form N → StateSymb N → StateSymb N → Form N
| .bttm, _, _         => .bttm
| .prop p, _, _       => p
| .svar x, s₂, s₁     => ite (s₁ = x) s₂ x
| .nom  i, s₂, s₁     => ite (s₁ = i) s₂ i
| φ ⟶ ψ, s₂, s₁      => (subst φ s₂ s₁) ⟶ (subst ψ s₂ s₁)
| □ φ, s₂, s₁         => □ (subst φ s₂ s₁)
| (all x, φ), s₂, s₁  =>
      match s₁ with
      | .SVAR y  => if (y = x) then (all x, φ) else (all x, (subst φ s₂ y))
      | .NOM  i  => all x, (subst φ s₂ i)

def is_substable : Form N → SVAR → SVAR → Bool
| .bttm, _, _     => true
| .prop _, _, _   => true
| .svar _, _, _   => true
| .nom  _, _, _   => true
| .impl φ ψ, y, x => (is_substable φ y x) && (is_substable ψ y x)
| .box  φ, y, x   => is_substable φ y x
| .bind z φ, y, x =>
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

notation:150 φ "[" s₂ "//" s₁ "]" => subst φ s₂ s₁

def Form.bulk_subst : Form N → List (StateSymb N) → List (StateSymb N) → Form N
| φ, h₁ :: t₁, h₂ :: t₂ => bulk_subst (φ[h₁ // h₂]) t₁ t₂
| φ, _, []    =>  φ
| φ, [], _    =>  φ

def all_nocc (i : NOM N) (Γ : Set (Form N)) := ∀ (φ : Form N), φ ∈ Γ → occurs i φ = false

theorem all_noc_conj (h : all_nocc i Γ) (L : List Γ) : occurs i (conjunction Γ L) = false := by
  induction L with
  | nil => simp [conjunction, occurs]
  | cons head tail ih =>
      simp [conjunction, occurs, ih, -Form.conj]
      exact h head head.2
