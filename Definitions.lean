def even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

def prime (n : Nat) : Prop :=
  ∀ m1 m2 : Nat, (m1 * m2 = n) → (m1 = n ∨ m2 = n) 

def infinitely_many_primes : Prop :=
  ∀ n m : Nat, (m > n ∧ prime m)

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ k : Nat, n = (2 ^ (2 ^ k) + 1) 

def infinitely_many_Fermat_primes : Prop :=
  ∀ n m : Nat, (m > n ∧ Fermat_prime m) 

def goldbach_conjecture : Prop :=
  ∀ n : Nat, (n > 2) → (∃ s1 s2 : Nat, (prime s1 ∧ prime s2) ∧ (s1 + s2 = n))

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, ((n > 5) ∧ ¬ (even n)) → (∃ s1 s2 s3 : Nat, (prime s1 ∧ prime s2 ∧ prime s3) ∧ (s1 + s2 + s3 = n))  

def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, (n > 2) → (∀ a b c : Nat, a^n + b^n ≠ c^n) 