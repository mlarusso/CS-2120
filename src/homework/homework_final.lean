import algebra.algebra.basic tactic.ring
/-
Mia LaRusso mnl6sc 12/08/21
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
Write the principle of complete induction using the notation of symbolic logic:
∀ P, (P(0) ∧ (∀ n', P(n') → P(n'+1)) → (∀ n, P n))

#2. Solve at least one of #2 and #3. Give detailed but informal proofs. 

Detailed Informal Proof #2: 
We first define a function that returns the sum
of all natural numbers from 0 to n (the argument). 
Lets call this function sum_n. 

Using this function, sum_n, we can state that for
a given value n, sum_n n = n * (n + 1) * (1 + (2 * n)) / 6. 
or 6 * sum_n n = n * (n + 1) * (1 + (2 * n)). This is 
our proposition. 

Next we can define a function, P, that takes a value
n, of type nat, and reduced to the proposition: 
6 * (sum_n n) = n * (n + 1) * (1 + (2 * n)).

Using induction on n, we will be proving that every
value of type n has property P: (forall n, P n). 
We can use this to conclude that for every nat, n, 
6 * (sum_n n) = n * (n + 1) * (1 + (2 * n)).

By using proof by induction on n, we have the base
case: proof of (P 0) which provides that sum_n 0 = 0 * (1) * (1).

The second case assumes an arbitrary n, lets call it n’
and proves that (P n’) holds: sum_n n’ = n’ * (n’ + 1) * (1 + (2 * n’)) / 6.

Given these cases we have shown that if P holds 
for n’ then it holds for (n’+1). With both cases 
(base & second) proved, we can finally apply induction 
to get a proof of forall n P n. (every value of type 
n has property P). QED.
-/

/-
To test out of the final exam ...
***
#1: Give a formal proof for #2 or #3.
#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9


-/

--Exam Exemption--
-- #1. Foraml proof of #2:
def sum_n : ℕ → ℕ 
| (nat.zero)    := nat.zero                
| (nat.succ n')  := (sum_n n') + (n'.succ * n'.succ) 

def P : ℕ → Prop := 
  λ n, 6 * sum_n n = n * (n + 1) * (1 + (2 * n))

def conjecture_p := ∀ n, P n 

theorem sum_n_opt : conjecture_p := 
begin
    unfold conjecture_p,
    assume n,
    unfold P,
    induction n with n' ih_n',
    apply rfl,
    simp [sum_n],
    rw mul_add,
    rw ih_n',
    rw nat.succ_eq_add_one,
    ring,
end

-- #2 10-13:
-- 10
def mult_one : ℕ → ℕ → ℕ 
| q (nat.zero) := nat.zero
| q (nat.succ n') := q * n' + q --(define multiplication: m * succ(n) = m * n + n)

def Q : ℕ → Prop :=
  λ n, mult_one 1 n = n

def conjecture_q := ∀ n, Q n 

theorem mult_one_opt : conjecture_q :=
begin
    unfold conjecture_q,
    assume n,
    unfold Q,
    induction n,
    apply rfl,
    simp[mult_one],
end
-- 11
example : ∀ (m n k : ℕ), m * (n + k) = m * n + m * k :=
begin
    assume m n k,
    induction m,
    induction n,
    induction k,
    apply rfl,
    rw mul_add,
    rw nat.succ_eq_add_one,
    ring,
    ring,
end
-- 12
example : ∀ (m n k: ℕ), m * (n * k) = (m * n) * k :=
begin
    assume m n k,
    induction m,
    induction n,
    induction k,
    apply rfl,
    exact k_ih,
    rw nat.succ_eq_add_one,
    ring,
    ring,
end
-- 13
example : ∀ (m n k: ℕ), m * n  = n * m :=
begin
    assume m n k,
    induction m,
    induction n,
    induction k,
    apply rfl,
    exact k_ih,
    exact n_ih,
    rw nat.succ_eq_add_one,
    ring,
end