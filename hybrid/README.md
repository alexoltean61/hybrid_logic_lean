Code was written following Blackburn 1998, present in this repository as **blackburn1998.pdf**.

**Table of Contents**

- [What was done](#what-was-done)
- [What needs work](#what-needs-work)
  * [1. Soundness for tautologies & deduction rules](#1-soundness-for-tautologies--deduction-rules)
  * [2. Propositional tautologies](#2-propositional-tautologies)
  * [3. Completeness...](#3-completeness)
- [In addition...](#in-addition)

### What was done
1. Defined the basics of hybrid language (specifically the language L(∀) as per Blackburn 1998): **Form.lean**. Proved some basics facts about substitutions and boundness.
2. Defined the proof system: **Proof.lean**.
3. Defined the semantics: **Truth.lean**. Proved some facts about interpretation variants and also that universal binding is commutative (semantically).
4. Started working on soundness: **Soundness.lean**. Proved the correctness of axioms **K**, **Q1**, **Q2**, **Name**, **Nom** and **Barcan**, and also **propositional tautologies** and **modus ponens**.

### What needs work
#### 1. Soundness for tautologies & deduction rules
A proof of soundness for **propositional tautologies**, the **necessitation rule** and the **universalization rule** is still required. For the two rules, the proof is trivial if you decide to prove merely that (⊢ φ) → (⊨ φ). (As Blackburn does in his paper!) It gets harder if you insist on proving *strong* soundness: (Γ ⊢ φ) → (Γ ⊨ φ).

#### 2. Propositional tautologies
This is not strictly necessary, but you can look into using truth assignments via morphisms instead of axioms. It would be nice to prove that tautologies via morphisms *really are* tautologies (ie., they are equivalent to the usual definition by evaluations).

#### 3. Completeness...

### In addition...
Blackburn's paper proves ⊢φ ↔ ⊨φ, what I started proving is Γ⊢φ ↔ Γ⊨φ. That already means a bit more care is necessary when dealing with, e.g., the universal generalization axiom. A decision must be made regarding whether to proceed like this or revert to the weak soundness/completeness.