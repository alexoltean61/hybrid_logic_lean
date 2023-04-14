open Classical

@[simp]
theorem double_negation : ¬¬p ↔ p :=
  Iff.intro
  (λ h =>
    Or.elim (em p)
    (λ hp  => hp)
    (λ hnp => absurd hnp h)
  )
  (λ p => λ np => absurd p np)

@[simp]
theorem implication_disjunction : (p → q) ↔ (¬p ∨ q) := by
  apply Iff.intro
  . intro impl
    exact byCases
      (λ hp  :  p => Or.inr (impl hp))
      (λ hnp : ¬p => Or.inl hnp)
  . intros disj hp
    exact Or.elim disj
      (λ hnp : ¬p => False.elim (hnp hp))
      (λ hq  :  q => hq)

@[simp]
theorem negated_disjunction : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hpq : ¬(p ∨ q) =>
      And.intro
        (fun hp : p =>
          show False from hpq (Or.intro_left q hp)
        )
        (fun hq : q =>
          show False from hpq (Or.intro_right p hq)
        )
    )
    (fun hpq : ¬p ∧ ¬q =>
      (fun disj : p ∨ q =>
        show False from
          Or.elim
           disj
           (fun hp : p => hpq.left hp)
           (fun hq : q => hpq.right hq)
      )
    )

@[simp]
theorem negated_impl : ¬(p → q) ↔ p ∧ ¬q :=
  Iff.intro
    (fun hyp : ¬(p → q) =>
      byCases
      -- case 1 : p
        (fun hp : p =>
          byCases
          -- case 1.a : p and q
            (fun hq : q =>
              ⟨
                hp, show ¬q from (fun q => show False from hyp (fun p => hq))
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
    (fun hyp : p ∧ ¬ q =>
      fun impl : p → q =>
        absurd (impl hyp.left) hyp.right
    )

@[simp]
theorem negated_universal {α : Type} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    Iff.intro
    (fun h1 : ¬ ∀ x, p x =>
      byContradiction
      (fun hcon1 : ¬ ∃ x, ¬ p x =>
        have neg_h1 := (fun a : α =>
          byContradiction
          (fun hcon2 : ¬ p a => show False from hcon1 (⟨a, hcon2⟩))
        )
        show False from h1 neg_h1
      )
    )
    (fun h2 : ∃ x, ¬ p x =>
      (fun hxp : ∀ x, p x =>
        match h2 with
        | ⟨w, hw⟩ => show False from hw (hxp w)
      )
    )

theorem conj_comm : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun hpq : p ∧ q =>
      ⟨hpq.right, hpq.left⟩ 
    )
    (fun hqp : q ∧ p =>
      ⟨hqp.right, hqp.left⟩
    )