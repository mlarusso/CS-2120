--Mia LaRusso mnl6sc 11/14/21 
--(extension granted by professor sullivan due to sickness)
import data.set
import tactic.ring 
namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  
--...is realated to...

/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric,
  unfold reflexive,

  assume p,
  cases p with a b,
  
  assume prop,
  apply not.intro,
  assume pp,
  --have to prove false
  have m := prop (pp a),
  have l := pp (a),
  contradiction,
end
/- If you remove the first condition, the proposition is no longer true
because you need to extablish the truth before the proposition in order
to be able to prove such type of β is asymmetric but cannot be relfexive.
English Language:
        First, we unfold asymmetric and reflexive propositions to be applied
        to the definitions established above. Next we assume p is the proposition
        representing the first condition that β is inhibited. Next we apply cases
        to p with two instances a and b which represent β and true props. After 
        assuming some proposition prop, we apply the not introduction rule and 
        assume another proposition pp. Finally, we need to prove false. To do so
        we create two variables m and l. m represents the proposition not-r in 
        respect to a. l represents r in respect to a. Last, performing a contradiciton 
        derives our proof of false.-/



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
-- add condition there exists type b that is true (b is inhabited)
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume x y z p,
  cases x with a b,
  apply not.intro,
  assume a,
  --3 goals false and prop
  contradiction,
end


/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume p q f h,

  apply set.ext,
  assume z,
  apply iff.intro,
  
  assume a,
  exact f a,

  assume b,
  exact h b,
end
/- informal proof:
      Given a set s, set s1, and set s2, all of the same type, first
      we assume the proposition p that there exists set s1 in a powerset
      of set s, and we assume proposition q that there exists set s2 in
      a powerset of set s. Then we assume f is the proposition s1 subset 
      s2 and assume h is the proposition s2 subset s1. By assuming there
      exists some type z in both s1 and s2, the relation of powerset of 
      set s is antisymetric with the iff introduction rule.
      -/

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/
-- Lecture 22
-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring_nf, --how to prove n = 1
end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume a,
  unfold divides,
  apply exists.intro 1, 
  --a = 1 * a
  ring,
end
/-First we assume n is a natural number. By unfolding
divides we get a * some number (k) = a. Next we apply 
the exists introduction rule 1 to have k = 1. Finally 
we can derive that a = a * 1 by the ring axioms.-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive,
  unfold divides,
  assume a,
  apply exists.intro 1,
  --a = 1 * a
  ring,
end 
/-First we unfold reflexive and divides. Next we have to 
assume some number a is a natural number to next derive 
the proposition that a = a * some number (k). By applying
the exists introduction rule with 1, we get a = 1 * a which
can be proved by basic algebra, or the ring axioms.-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive,
  unfold divides,
  assume n,
  cases n with a b,
  assume p,
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-Divides is not symmetric-/


/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin
   assume n,
   unfold divides,
   apply exists.intro,
end


/- #5
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume a b c,
  have p := a (c),
  contradiction,
end
/- First we unfold asymmetric and irreflexive. Next we assume
propositions a b and c. After this we can create a variable p that
represents r with propositions b b. Finally we need to prove false
which can be done with a contradiction.-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume a b c d,
  have p := a (d),
  assume pp,
  apply not.intro,
  assume f,
  --prove false
  contradiction,
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume a b c
  have p := b(c),
end


end relation
