--mnl6sc Mia LaRusso 09/29/21
/- 
worked with: 
fpg2kv@virginia.edu 
npj5kr@virginia.edu 
-/
-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  -- could use contradiction, to prove false
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P, --classical reasoning, gives you P and not P
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  assume left,
  apply or.elim (em P),
  assume hP,
  apply or.inr,
  assume hQ : Q,
  show false, from left (and.intro hP hQ),
  assume nP,
  apply or.inl,
  exact nP,
  assume nPoQ,
  apply or.elim nPoQ,
  assume nP, 
  apply or.elim (or.swap nPoQ),
  assume nQ,
  apply not.intro,
  assume PaQ,
  have P := and.elim_left PaQ,
  have Q := and.elim_right PaQ,
  apply not.intro nP,
  exact P,
  assume nP,
  apply not.intro,
  assume PaQ,
  apply not.intro nP,
  exact and.elim_left PaQ,
  assume nQ,
  apply not.intro,
  assume PaQ,
  apply not.intro nQ,
  exact and.elim_right PaQ,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume first,
  have PonP := classical.em P,
  have QonQ := classical.em Q,
  apply and.intro,
  apply not.intro,
  assume P,
  apply not.intro first,
  apply or.intro_left,
  exact P,
  apply not.intro,
  assume Q,
  apply not.intro first,
  apply or.intro_right,
  exact Q,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  have Pem := em P,
  have Qem := em Q,
  apply iff.intro, 
  assume first,
  apply or.elim first,
  assume P,
  apply or.intro_left,
  exact P,

  assume nPaQ,
  apply or.intro_right,
  have Q := and.elim_right nPaQ,
  exact Q,

  cases Pem,
  cases Qem,
  assume PoQ,
  apply or.inl,
  exact Pem,
  assume PoQ,
  apply or.inl,
  exact Pem,
  assume PoQ,
  apply or.inr,
  apply and.intro,
  exact Pem,
  have x := em P,
  have P := or.intro_right Q Qem,
  apply or.elim P,
  assume Q,
  exact Q,

  assume QonQ,
  have j:= or.intro_left Q Qem,
  apply or.elim QonQ,
  assume Q,
  exact Q,

  assume nQ,
  have k := or.intro_left Q Pem,
  apply or.elim PoQ,
  assume P,
  have lk := or.neg_resolve_left k,
  show Q, from lk P,
  assume Q,
  exact Q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  assume first,
  cases first,
  cases first_right,
  apply or.inl,
  
  exact first_right,

  cases first_left,
  apply or.inl,
  exact first_left,
  apply or.inr,

  have x := and.intro first_left first_right,
  exact x,

  assume twp,
  apply and.intro,
  cases twp,
  apply or.inl,
  exact twp,
  apply or.inr,
  have x := and.left twp,
  exact x,
  cases twp,
  apply or.inl,
  exact twp,
  apply or.inr,
  have x := and.right twp,
  exact x,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,

  --iff intro (left and right)
  apply iff.intro,
  assume first,
  cases first,
  cases first_left,
  cases first_right,
  apply or.inl,

  have x := and.intro
  first_left
  first_right,
  exact x,

  apply or.inr,
  apply or.inl,

  have x := and.intro
  first_left
  first_right,
  exact x,
  --right
  cases first_right,
  apply or.inr,
  apply or.inr,
  apply or.inl,
  --repeat again,
  have x:= and.intro
  first_left
  first_right,
  exact x,
  apply or.inr,
  apply or.inr,
  apply or.inr,

  have x:= and.intro
  first_left
  first_right,
  exact x,
  assume second,
  cases second,
  apply and.intro,
  apply or.inl,
  --proof other side
  have x := and.left second,
  exact x,
  apply or.inl,
  have x := and.right second,
  exact x,
  cases second,
  apply and.intro,
  apply or.inl,

  have x:= and.left second,
  exact x,
  apply or.inr,
  --right left
  have x := and.right second,
  exact x,
  cases second,
  apply and.intro,
  apply or.inr,
  have x := and.left second,
  exact x,
  apply or.inl,

  have x := second.right,
  exact x,
  apply and.intro,
  apply or.inr,

  have x := second.left,
  exact x,
  apply or.inr,

  have x := second.right,
  exact x,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ ∀ (n : ℕ), n = 0 :=
begin
  assume n,
  have contradictory := n 1,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  have x := em P,
  apply iff.intro,
  assume first,
  cases x,
  apply or.inr,
  have q := first x,
  exact q,
  apply or.inl,
  exact x,

  assume second,

  have y := em Q,
  cases y,
  cases second,
  assume p,
  exact y,
  assume P,
  exact y,
  assume P,
  cases second,
  contradiction,
  assumption,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume p,
  assume q,
  have emP := classical.em P,
  have emQ := classical.em Q,
  cases emP,
  have h := p emP,
  contradiction,
  assumption,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume p,
  assume qp,
  have emP := em P,
  have emQ := em Q,
  cases emP,
  exact emP,
  have k := p emP,
  contradiction,
end
