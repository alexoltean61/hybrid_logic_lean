variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun hpq : p ∧ q =>
      ⟨hpq.right, hpq.left⟩ 
    )
    (fun hqp : q ∧ p =>
      ⟨hqp.right, hqp.left⟩
    )

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hpq : p ∨ q =>
      Or.elim
        hpq
        (fun hp : p => Or.intro_right q hp)
        (fun hq : q => Or.intro_left p hq)
    )
    (fun hqp : q ∨ p =>
      Or.elim
        hqp
        (fun hq : q => Or.intro_right p hq)
        (fun hp : p => Or.intro_left q hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      (fun itz : (p ∧ q) ∧ r => ⟨itz.left.left, itz.left.right, itz.right⟩)
      (fun itz : p ∧ (q ∧ r) => ⟨⟨itz.left, itz.right.left⟩, itz.right.right⟩)

   
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
    Iff.intro
      (fun lbrack : (p ∨ q) ∨ r =>
        Or.elim
          lbrack
          (fun hpq : p ∨ q =>
            Or.elim
              hpq
              (fun hp : p => Or.intro_left (q ∨ r) hp)
              (fun hq : q => Or.intro_right p (Or.intro_left r hq))
          )
          (fun hr : r => Or.intro_right p (Or.intro_right q hr))
      )
      (fun rbrack : p ∨ (q ∨ r) =>
        Or.elim
          rbrack
          (fun hp : p => Or.intro_left r (Or.intro_left q hp))
          (fun hqr : q ∨ r =>
            Or.elim
            hqr
            (fun hq : q => Or.intro_left r (Or.intro_right p hq))
            (fun hr : r => Or.intro_right (p ∨ q) hr)
          )
      )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
    Iff.intro
      (fun hyp : p ∧ (q ∨ r) =>
        Or.elim
          hyp.right
          (fun hq : q => Or.intro_left (p ∧ r) ⟨hyp.left, hq⟩)
          (fun hr : r => Or.intro_right (p ∧ q) ⟨hyp.left, hr⟩)
      )
      (fun hyp : (p ∧ q) ∨ (p ∧ r) =>
        Or.elim
          hyp
          (fun hpq : p ∧ q => And.intro hpq.left (Or.intro_left r hpq.right))
          (fun hpr : p ∧ r => And.intro hpr.left (Or.intro_right q hpr.right))
      )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
      (fun hyp : p ∨ (q ∧ r) =>
        Or.elim
          hyp
          (fun hp : p => And.intro (Or.intro_left q hp) (Or.intro_left r hp))
          (fun hqr : q ∧ r => And.intro (Or.intro_right p hqr.left) (Or.intro_right p hqr.right))
      )
      (fun hyp : (p ∨ q) ∧ (p ∨ r) =>
        Or.elim
          hyp.left
          (fun hp : p => Or.intro_left (q ∧ r) hp)
          (fun hq : q =>
            Or.elim
              hyp.right
              (fun hp : p => Or.intro_left (q ∧ r) hp)
              (fun hr : r => Or.intro_right p ⟨hq, hr⟩)
          )
      )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
      (fun hpqr : p → (q → r) =>
        fun hpq : p ∧ q =>
          hpqr hpq.left hpq.right 
      )
      (fun hpqr : p ∧ q → r =>
        fun hp : p =>
          fun hq : q =>
            hpqr ⟨hp, hq⟩    
      )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
    Iff.intro
      (fun hpqr : (p ∨ q) → r =>
        And.intro
          (fun hp : p => hpqr (Or.intro_left q hp))
          (fun hq : q => hpqr (Or.intro_right p hq))
      )
      (fun conj : (p → r) ∧ (q → r) =>
        fun disj : p ∨ q =>
          Or.elim
            disj
            (fun hp : p => conj.left hp)
            (fun hq : q => conj.right hq)
      )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
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

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun hpq : ¬p ∨ ¬q =>
      Or.elim
        hpq
        (fun hp : ¬p =>
          fun hpq : p ∧ q =>
            show False from hp hpq.left
        )
        (fun hq : ¬q =>
          fun hpq : p ∧ q =>
            show False from hq hpq.right 
        )

example : ¬(p ∧ ¬p) :=
    fun nonc : p ∧ ¬p =>
      show False from nonc.right nonc.left

example : p ∧ ¬q → ¬(p → q) :=
    fun hpq : p ∧ ¬q =>
      fun con : p → q =>
        show False from hpq.right (con hpq.left)

example : ¬p → (p → q) :=
    fun hnp : ¬p =>
      fun hp : p =>
        False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
    fun hpq : ¬p ∨ q =>
      Or.elim
        hpq
        (fun hnp : ¬p => (fun hp : p => False.elim (hnp hp)))
        (fun hq : q => (fun p => hq))

example : p ∨ False ↔ p :=
    Iff.intro
      (fun hpf : p ∨ False =>
        Or.elim
          hpf
          (fun p => p)
          (fun False => False.elim)
      )
      (fun hp : p => Or.intro_left False hp)

example : p ∧ False ↔ False :=
    Iff.intro
      (fun hpf : p ∧ False => hpf.right)
      (fun False => False.elim)

example : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q =>
    fun hnq : ¬q =>
      fun hp : p => show False from hnq (hpq hp)