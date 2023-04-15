Code was written following Blackburn 1998, present in this repository as **blackburn1998.pdf**.

**Table of Contents**

[TOC]

### What was done
1. Defined the basics of hybrid language (specifically the language L(∀) as per Blackburn 1998): **Form.lean**. Proved some basics facts about substitutions and boundness.
2. Defined the proof system (but work is needed on propositional tautologies): **Proof.lean**.
3. Defined the semantics: **Truth.lean**. Proved some facts about interpretation variants and also that universal binding is commutative (semantically).
4. Started working on soundness: **Soundness.lean**. Proved the correctness of axioms **K**, **Q1** and **Q2 for state variables**.

### What needs work
#### 1. Substitution lemma
Convince Lean that the proof for *svar_substitution:* (is_substable φ y x) → (is_variant g g' x) → (g' x = g y) → **((M,s,g) ⊨ φ[y // x] ↔ (M,s,g') ⊨ φ**) terminates. Well-founded induction was used in two places there:
1. To prove the case for **φ = □ψ**, the induction hypothesis was applied to any neighbouring s' of s and to the formula ψ: **(M,s',g) ⊨ ψ[y // x] ↔ (M,s',g’) ⊨ ψ**.
2. To prove the case for **φ = all v, ψ**, the induction hypothesis was applied to any v-variant f of g and to the formula ψ: **(M,s,f) ⊨ ψ[y // x] ↔ (M,s,f’) ⊨ ψ**.

Both of these applications seem sound to me. In both cases **ψ < φ** w.r.t. formula size, and in the end recursion should terminate when ψ becomes an atomic formula (size 1). I tried providing proofs that **ψ < □ψ** and **ψ < all v, ψ** via *have* statements. But that did nothing, because the actual goal that Lean wanted me to prove for termination was much, much uglier. The tactic state needed for termination is so long that I had to attach it in a separate file, *termination_state*. I don't know how to prove that.
#### 2. Propositional tautologies
Add an instance of every propositional tautology as an axiom and prove their soundness. I saw the way it was done in Matching Logic via morphisms, but I still have to wrap my head around it.
#### 3. Soundness for the remaining axioms
Namely **Q2 for nominals**, **Name**, Nom and **Barcan**, and the remaining deduction rules (modus ponens, generalization, necessitation). Proofs for bolded axioms can be found in Blackburn 1998.
#### 4. Proving decidability
I know this isn't *necessary* since I'm using Classical, but I want to at least be able to do it. I wanted to write an instance of Decidable for is_free x φ and I got stuck. I think I must provide a proof of either isTrue (is_free x φ) or isFalse (is_free x φ), but I don't know how to do that.
#### 5. Completeness...

### In addition...
Blackburn's paper proves ⊢φ ↔ ⊨φ, what I started proving is Γ⊢φ ↔ Γ⊨φ. That already means a bit more care is necessary when dealing with, e.g., the universal generalization axiom. I hope it won't become even more troublesome as I progress with the proof.