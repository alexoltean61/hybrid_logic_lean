Code was written following Blackburn 1998, present in this repository as **blackburn1998.pdf**.

**Table of Contents**

- [What was done](#what-was-done)
- [What needs work](#what-needs-work)
  * [1. Completeness...](#1-completeness)

### What was done
1. Defined the basics of hybrid language (specifically the language L(∀) as per Blackburn 1998): **Form.lean**. Proved some basics facts about substitutions and boundness.
2. Defined the proof system: **Proof.lean**.
3. Defined the semantics: **Truth.lean**. Proved some facts about interpretation variants and also that universal binding is commutative (semantically).
4. Proved soundness: (Γ ⊢ φ) → (Γ ⊨ φ).

### What needs work
#### 1. Completeness...