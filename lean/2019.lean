import .lovelib

import .love03_forward_proofs_demo

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

-- # Question 1. Variable substitution (5+6 points)

inductive exp : Type
| Var :string → exp 
| Num : ℤ → exp
| Plus : exp → exp → exp

export exp (Var Num Plus)

/- __1a.__ Complete the following recursive Lean definition of a function `subst` that performs 
simultaneous substitution of variables. The application `subst ρ e` simultaneously replaces 
every variable in e with a new subexpression: Each occurrence of `Var x` is replaced with `ρ x`.
-/

def subst (ρ : string → exp) : exp → exp
| (exp.Var  s) := ρ s
| (exp.Num  n) := exp.Num n
| (exp.Plus i j) := exp.Plus (subst i) (subst j)

/-
__1b.__ If we perform simultaneous substitution with λx, Var x, we should get the identity function on
expressions:
-/
lemma subst_Var (e : exp) : subst (λx, Var x) e = e:=
begin
    induction' e,
    {rw subst},
    {rw subst,},
    {rw subst,cc,}
end

-- # Question 2. Identity monad (4+7 points)
/-The identity monad is a monad that simply stores a value of type α, without any special effects or 
computational strategy. In other words, it simply provides a box containing a single value of type α. 
Viewed as a type constructor, the identity monad is the identity function `λα : Type, α`. When applying it 
to a type variable α, we end up with `(λα : Type, α) α`, i.e., α itself.-/

/-__2a.__ Complete the Lean definitions of the pure and bind operations:-/

-- def id.pure {α : Type} : α → α :=
-- id

-- def id.bind {α β : Type} : α → (α → β) → β
-- | a f := f a

def id.pure {α : Type} : α → id α :=
id

def id.bind {α β : Type} : id α → (α → id β) → id β
| a f := f a

/-__2b.__ Assume `ma >>= f` is syntactic sugar for `id.bind ma f`. Prove the three monadic laws. Your proofs should 
be step-by-step calculational, with at most one rewrite rule or definition expansion per step, so that 
we can clearly see what happens.-/


-- lemma id.pure_bind {α β : Type} (a : α) (f : α → β) : 
-- (id.pure a >>= f) = f a :=
-- begin
--     simp[id.pure],
-- end

-- ∀ {α β : Type} (a : α) (f : α → id β), pure a >>= f = f a
lemma id.pure_bind {α β : Type} (a : α) (f : α → id β) :   -- NOTE: 这个是倒着的
(id.pure a >>= f) = f a :=
begin
    simp[id.bind],
    simp[id.pure],
end

-- lemma id.bind_pure {α : Type} (ma : α) : 
-- (ma >>= id.pure) = ma :=
-- begin
-- sorry
-- end

--  ∀ {α : Type} (ma : id α), ma >>= pure = ma
lemma id.bind_pure {α : Type} (ma : id α):
(ma >>= pure) = ma :=
begin
    simp[id.pure],
end


-- lemma id.bind_assoc {α β γ : Type} (f : α → β) (g : β → γ) (ma : α) : 
-- ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)) :=
-- sorry

-- ∀ {α β γ : Type} (f : α → id β) (g : β → id γ) (ma : id α), ma >>= f >>= g = ma >>= λ (a : α), f a >>= g

lemma id.bind_assoc {α β γ : Type} (f : α → id β) (g : β → id γ) (ma : id α):
(ma >>= f >>= g) = (ma >>= λ (a : α), f a >>= g) :=
begin
    simp[id.pure_bind],
end

-- # 3a

inductive program : Type
| skip {}   : program
| havoc     : string → program
| seq       : program → program → program
| choose    : program → program → program
| loop      : program → program

export program (skip havoc seq choose loop)


inductive small_step : program × state → program × state → Prop 

-- # Question 5. Palindromes (6+7+6 points)
/- Palindromes are lists that read the same from left to right and from right to left. For example,
[a, b, b, a] and [a, h, a] are palindromes. -/


/- __5a.__ Define an inductive predicate that is true if and only if the list passed as argument is a palin-
drome, by completing the Lean definition below: -/

inductive palindrome {α : Type} : list α → Prop 
| nil : 
    palindrome []
| single (x : α) : 
    palindrome [x]
| sandwich (x : α) (xs : list α) (hxs : palindrome xs) :  -- NOTE 应用时候每个圆括号都需要代表物
    palindrome ([x] ++ xs ++ [x])

/- The definition should distinguish three cases:
1. The empty list [] is a palindrome.
2. For any element x : α, the singleton list [x] is a palindrome.
3. For any element x : α and any palindrome [y1, ..., yn], the list [x, y1, ..., yn, x] is a palindrome.
-/


/- __5b.__ Let reverse be the following operation:-/
-- def reverse {α : Type} : list α → list α 
-- | [] := []
-- | (x :: xs) := reverse xs ++ [x]

lemma reverse_append_sandwich {α : Type} (x : α) (ys : list α) : 
reverse ([x] ++ ys ++ [x]) = [x] ++ reverse ys ++ [x] :=
begin
    simp [reverse], 
    simp[reverse_append],
    refl,
end

/- Using reverse, prove that the reverse of a palindrome is also a palindrome:-/
lemma rev_palindrome {α : Type} (xs : list α) 
(pal_xs : palindrome xs) :
    palindrome (reverse xs):=
    begin
        induction' pal_xs,
        {simp[reverse],
        apply palindrome.nil},
        {simp[reverse],
        apply palindrome.single},
        {
            rw reverse_append_sandwich,
            apply palindrome.sandwich,
            apply ih,}
        
    end

/- Make sure to follow the proof guidelines given on page 1. If it helps, you may invoke the following lem-
ma (without having to prove it): -/
-- lemma reverse_append_sandwich {α : Type} (x : α) (ys : list α) : 
-- reverse ([x] ++ ys ++ [x]) = [x] ++ reverse ys ++ [x] :=
-- sorry

/- 5c. Prove that the lists [], [a, a], and [a, b, a] are palindromes, corresponding to the following lemma 
statements in Lean:-/
lemma palindrome_nil {α : Type} : palindrome ([] : list α):=
palindrome.nil

lemma palindrome_aa {α : Type} (a : α) : 
palindrome [a, a]:=
 palindrome.sandwich a _ palindrome.nil


lemma palindrome_aba {α : Type} (a b : α) : 
palindrome [a, b, a]:=
 palindrome.sandwich a _ (palindrome.single b)

-- # Question 6. One-point rules (5+5+3 points)
/- One-point rules are lemmas that can be used to remove a quantifier from a proposition when the quantified 
variable can effectively take only one value. For example, ∀x, x = 5 → p x is equivalent to the much simpler p 5.
-/

/- __6a.__ Prove the one-point rule for ∀. In your proof, identify clearly how the quantifier is instantiated. -/
lemma forall.one_point_rule {α : Type} {t : α} {p : α → Prop} :
(∀x : α, x = t → p x) ↔ p t :=
begin
    apply iff.intro,
    {intros h,
    apply h,
    refl},
    {intros pt x hxt,
    cc}
end


/- __6b.__ Prove the one-point rule for ∃. In your proof, identify clearly which witness is supplied for the
quantifier.
-/ 

lemma exists.one_point_rule {α : Type} {t : α} {p : α → Prop} :  -- important
(∃x : α, x = t ∧ p x) ↔ p t :=
begin
    apply iff.intro,
    {
        intros h,
        apply exists.elim h,
        cc,
    },
    {
        intros h,
        apply exists.intro t,
        cc,
    }
end

/-
__6c.__ Alyssa P. Hacker proposes the following alternative one-point rule for ∀:
-/ 
lemma forall.one_point_rule' {α : Type} {t : α} {p : α → Prop} :
(∀x : α, x = t ∧ p x) ↔ p t :=
begin
    apply iff.intro,
    {intros h,
    apply and.right,
    apply h,},
    {intros h x,
    apply and.intro,
    }
end

-- What is wrong with this rule?

end LoVe
