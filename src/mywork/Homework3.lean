/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := /-(not possible) there is no proof of false, only proof of true-/  -- trick question? why?

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

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end
