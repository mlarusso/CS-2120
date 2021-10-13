-- Mia LaRusso mnl6sc 10/07/2021 --
/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points] 

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION --TODO

Complete the definition of the elimination
rule for →.

-- answer --
(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- → elim
              q : Q
-/

-- Give a formal proof of the following --

-- answer --
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume p,
  exact p,
end

-- Extra credit [2 points]. Who invented this principle?



-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- answer --
-- true has a proof that is logically true --

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following: 

-- answer --
example : true := true.intro 


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Give an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- answer --
/-If P and Q are propositions, in which a proof of P 
and a proof of Q exist. We can deduce P and Q using the
introduction rule for and on such proofs.-/

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.
-/

-- answer --
/-
(P Q : Prop) (pq : P ∧ Q)
-------------------------- ∧ elim (left)
            p : P

(P Q : Prop) (pq : P ∧ Q)
-------------------------- ∧ elim (right)
          q : Q

Assuming we have two propositions, P and Q, we can get
a proof of P, p by applying the left and elimination 
rule to the proposition: P and Q, and we can get a proof 
of Q, q by applying the right and elimination rule to 
the proposition: P and Q.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

-- answer --
example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
  assume P Q,
  assume pq,
  apply and.elim_right pq,
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION
LEC 4
Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- answer --
/-
For all types T, there exists a proof of Q, given that Q
is a predicate that has some property that is of type T.
To prove (∀ (t : T), Q) we assume that we are given some 
property by Q that is of type T and then we prove Q is true. 
If Q is proven to be true, asserting a property of type T, 
then we an assume that it is true for all t of type T.
-/

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- ∀ elim
                    (q : Q t)

-- answer --
For all types T, there exists a proposition of Q that 
asserts some property of type T. We have a proof (pf) that
for all t of type T, t has a property Q. We use the elimination
rule for ∀ by applying pf to t which will provide a proof that
t has the property Q.


Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- answer here --
We use pf to prove Q by applying pf to t. Since for all t
of type T, t has property Q, we can assume Q is true for all 
types t, in doing so we can derive the proof Q is true.
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- answers --
  -- (1) Lynn is a person
  (Lynn p: Person)
  -- (2) Lynn knows logic
  (LKL: KnowsLogic p)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀ (p : Person), (Lynn p: BetterComputerScientist p):= 
/-I am not sure why Lynn is not working for for this problem.
My thought process was to use Lynn of type p (Person) is a
better computer scientist (BetterComputerScientist p). -/


-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- answer --
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/ 

-- answer --
/-Proof by negation derives a proof of not P from the 
proof that P implies false.
The rule proves a proposition ¬P by assuming P is true and 
then showing that P implies false through a contradiction 
-/


/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

--answer--
Proof by contradiction proves P by assuming ¬P and 
then deriving false from this assumption.

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that *there is a contradiction.*
From this derivation you can conclude *¬¬P*.
Then you apply the rule of negation *elimination*
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is *classically* valid, and that accepting the axiom
of the proposition suffices to establish negation
*¬P* (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

-- answer --
example : ∀ (P Q : Prop), (P ∧ Q) ↔ (P ∧ Q) :=
begin
  assume P Q,
  apply iff.intro,

  assume pq,
  cases pq,
  apply and.intro,
  exact pq_left,
  exact pq_right,

  assume qp,
  cases qp,
  apply and.intro,
  exact qp_left,
  exact qp_right,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/
--answers--
/- For all types Person there exists a proposition 
that a Person is Nice, a Person is Talented, and a 
Person likes a Person of a certain proposition. The proof
elantp prooves that for all types person, a Nice person
implies a Talented person which implies that for all types 
Person, (everyone) likes JohnLennon because JohnLennon is a
Nice and Talented Person. 
-/
def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 

      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
--answer--
example : ELJL := 
begin
  intros Person Nice Talented Likes elantp JohnLennon JLNT q,
  have a := JLNT.right,
  have b := JLNT.left,
  have c := elantp JohnLennon b a,
  have d := q,
  apply c,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that if every car 
is rad, then:
the car is
 rad and heavy and red or
 rad and heavy and blue or
 rad and light and red or 
 rad and light and blue


-- how many cases will need to be considered? 4 cases
-- list the cases (informaly)
    -- answer here --
    rad and heavy and red
    rad and heavy and blue
    rad and light and red 
    rad and light and blue
-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

-- answers --
def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (a b c : T), a = b → b = c → a = c

/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/
--LEC 10
def negelim_equiv_exmid : Prop := 
∀ (P : Prop),
(P ∨ ¬P) → (¬¬ P)

example: negelim_equiv_exmid :=
begin
  assume P,
  assume p,
  cases p,
  contradiction,
  
end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : ∀(Person : Prop), Person → Person:= 
begin
  assume P,
  assume p,
  exact p,
end
