--Mia LaRusso
/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/
--DUE SAT BY 3
example : true := true.intro

example : false := /-not possible, there is no proof of false, only proof of true-/

example : ∀ (P : Prop), P ∨ P ↔ P :=
begin
  assume P, 
  apply iff.intro _ _,
  --forward
  assume prop,
  apply or.elim prop,
  --where left disjunct is true
  assume p,
  exact p,
  --where right discjunct is true
  assume p,
  exact p,
  --backwards
  assume p,
  exact or.intro_left P p,
end
/- Assume P is a proposition. Apply the iff introduction rule. 
Assume prop is a proof of P or P. Apply the or elimination rule to prop
to get a proof of just p where P implies P. Assume p implies P or P and
apply this to p. Apply the left or introduction rule to P and p.-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume pP,
  apply and.elim_right pP,
  assume p,
  exact and.intro p p,
end

/- Assume P is a proposition. Apply the iff introduction
rule. Assume pP is a proof of P. Apply the right and elimination rule
to pP to get a proof of just P. Assume p is a proposition and apply 
the and introduction rule to p twice. -/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pq,
  cases pq,
  apply or.intro_right,
  exact pq,
  apply or.intro_left,
  exact pq,
  assume PQ,
  cases PQ,
  apply or.intro_right,
  exact PQ,
  apply or.intro_left,
  exact PQ,
end
/- Assume P and Q are propositions. Apply the iff introduction
rule. Assume pq is a proof of P. Do a case analysis of pq and 
apply the right or introduction rule to exact P. Next, apply 
the or introduction rule to pq to exact Q. Now you have a proof
from the right side implies. Next assume PQ and apply the or intro
rule from the right and the left to exact PQ and get a proof 
from the left direction implies prop.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  assume pq,
  cases pq,
  apply and.intro,
  apply and.elim_right,
  apply and.elim_left,
end
/- Assume P and Q are propositions. Apply the iff introduction rule.
Assume pq is a proof of P and Q. Use cases on pq. Apply the and introduction
rule. Apply the right and left elimination rule.-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  assume prop,
  have p: P := and.elim_left prop,
  have qr: Q ∨ R := and.elim_right prop,
  cases qr,
  apply or.intro_left,
  apply and.intro,
  exact p,
  exact qr,
  apply or.intro_right,
  apply and.intro,
  exact p,
  exact qr,
  assume prop,
  cases prop,
  have p: P := and.elim_left prop,
  have q: Q := and.elim_right prop,
  apply and.intro,
  exact p,
  apply or.intro_left,
  exact q,
  apply and.elim prop,
  assume p r,
  apply and.intro,
  exact p,
  apply or.intro_right,
  exact r,
end
/- Assume P Q and R are propositions. Apply the iff introduction rule. Assume
prop is a proof of the left side of the proposition. Have p be P when the and
left elimination rule is applied to prop. Have qr be Q or R when the right and
 elimination rule is applied to prop. Use cases on qr and apply the or introduction 
 rule to the left. Apply the and introduction rule. Apply p to this and then qr.
 Apply the right or introduction rule. Then apply the and introduction rule, applying
 p and then qr. Assume prop is a proof. Uses cases on prop. Have p be P when the 
 and left elimination rule is applied to prop. Have q be Q when the right and elimination
 rule is applied to prop. Apply the and introduction rule and get p. Apply the left or
 introduction rule and get q. Apply the and elimination rule to prop. Assume p and r are
  proofs of P and R respectively. Apply the and introduction rule and apply p. Apply 
  the right or introduction rule and apply r-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  assume prop,
  apply or.elim prop,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
--I am confused on this problem... not sure what to do now but I gave it a try.
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume p,
  apply and.elim_left p,
  assume p,
  apply and.intro,
  exact p,
  apply or.intro_left,
  exact p,
end
/- Assume P and Q are propositions. Apply the iff introduction
rule. Assume p is a proof and apply the and elimination rule to p.
We then assume p and apply the and introduction rule to build 
up the proof. Exact p and apply the left or introduction rule to
get P or Q. Exact p again to get the whole proof.-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume pq,
  apply or.elim pq,
  assume p,
  exact p,
  assume pq,
  apply and.elim_left pq,
  apply or.intro_left,
end
/-Assume P and Q are propositions. Apply the iff introduction rule
assume pq is a proof of P or P and Q. Apply the or elimination rule to pq. 
Assume p is a proof of P. Apply p to the proof. Assume pq is a proof of
P and Q. Apply the left and elimination rule to pq. Apply the left or
introduction rule.-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume p,
  apply true.intro,
  assume t,
  apply or.intro_right,
  apply true.intro,
end
/- Assume P is a proposition. Apply the iff introduction rule.
Assume p is a proof of P or true. Apply the true introduction rule.
Assume t is a proof of true. Apply the right or introduction rule.
Apply the true introduction rule.-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume p,
  cases p,
  exact p,
  cases p,
  assume pf,
  apply or.intro_left,
  exact pf,
end


example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume p,
  apply and.elim_left p,
  assume p,
  apply and.intro p,
  apply true.intro,
end
/- Assume P is a proposition. Apply the iff introduction rule to P.
Assume p is a proof of P and true. Apply the left and elimination rule to p
to get a proof of P. Apply the and introduction rule to p. Apply the 
true introduction rule.-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume p,
  cases p,
  exact p_right,
  apply and.intro,
  apply false.elim,
end
/- Assume P is a proposition. Apply the iff introduction rule. Assume p is 
a proof of P and false. Use cases on p and apply right p. Apply the and 
introduction rule. Apply the false elimination rule.-/