open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    (fun hpqr : p → q ∨ r =>
      Or.elim
        (em p)
        (fun hp : p =>
          Or.elim
            (hpqr hp)
            (fun hq : q => Or.intro_left (p → r) (fun _ => hq))
            (fun hr : r => Or.intro_right (p → q) (fun _ => hr))
        )
        (fun hnp : ¬p =>
          Or.intro_right (p → q) (fun hp : p => False.elim (hnp hp))
        )
    )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    (fun hpq : ¬(p ∧ q) =>
      Or.elim
        (em p)
        (fun hp : p =>
          Or.inr (show ¬q from fun hq : q =>
            show False from hpq ⟨hp, hq⟩)
        )
        (fun hnp : ¬p => Or.inl hnp)
    )

-- basically a truth-table proof via syntax...
-- hackish
-- would be better if you proved by contradiction using deMorgan
-- but you had to prove deMorgan as an example, not a named theorem, so csf
example : ¬(p → q) → p ∧ ¬q :=
    (fun hyp : ¬(p → q) =>
      byCases
      -- case 1 : p
        (fun hp : p =>
          byCases
          -- case 1.a : p and q
            (fun hq : q =>
              ⟨
                hp, show ¬q from (fun _ => show False from hyp (fun _ => hq))
              ⟩
            )
          -- case 1.b : p and non q
            (fun hnq : ¬q => ⟨hp, hnq⟩)
        )
      -- case 2 : non p
        (fun hnp : ¬p => show (p ∧ ¬q) from False.elim
          (show False from hyp
            (show (p → q) from fun p : p =>
              (show q from False.elim (hnp p))
            )
          )
        )
    )

example : (p → q) → (¬p ∨ q) :=
  (fun h : p → q =>
    byCases
      (fun hp : p => Or.inr (h hp))
      (fun hnp : ¬p => Or.inl hnp)
  )

--- again, would be cleaner by contradiction
example : (¬q → ¬p) → (p → q) :=
    (fun hyp : (¬q → ¬p) =>
      byCases
        (fun hq : q =>
          byCases
            (fun _ : p => (fun _ => hq))
            (fun hnp : ¬p => (fun p => show q from False.elim (hnp p)))
        )
        (fun hnq : ¬q => (fun hp : p => show q from False.elim ((hyp hnq) hp)))
    )

example : p ∨ ¬p :=
  byContradiction
    (fun hyp : ¬(p ∨ ¬p) =>
      absurd (fun hp : p => show False from (hyp (Or.inl hp)))
             (fun hnp : ¬p => show False from (hyp (Or.inr hnp)))
    )

-- ugly
example : (((p → q) → p) → p) :=
    (fun impl : (p → q) → p =>
      byContradiction
      -- suppose not p
        (fun hyp : ¬p =>
          -- we reach the absurd conclusion that p
          -- by the implication that (p->q)->p
          absurd (impl
            -- since we can show that (p->q)
            (show (p → q) from (fun hp : p => show q from
              False.elim (hyp hp)
              )
            )
          ) hyp
        )
    )