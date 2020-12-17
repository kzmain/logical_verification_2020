-- ZZZZ: 8.5pt -- see comments below

import .love04_functional_programming_demo


/- # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (2 points): Maps

1.1 (1 point). Complete the following definition. The `map_btree` function
should apply its argument `f` to all values of type `α` stored in the tree and
otherwise preserve the tree's structure. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β 
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node (f a) (map_btree l) (map_btree r)

/- 1.2 (1 point). Prove the following lemma about your `map_btree` function. -/

lemma map_btree_iden {α : Type} :
  ∀t : btree α, map_btree (λa, a) t = t
| btree.empty        := by refl
| (btree.node a l r) :=
begin
  simp[map_btree],
  simp[map_btree_iden],
end


/- ## Question 2 (4 points): Tail-Recursive Factorials -/

/- Recall the definition of the factorial functions -/

#check fact

/- 2.1 (2 points). Experienced functional programmers tend to avoid definitions
such as the above, because they lead to a deep call stack. Tail recursion can be
used to avoid this. Results are accumulated in an argument and returned. This
can be optimized by compilers. For factorials, this gives the following
definition: -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

lemma accufact_an_eq_afactn:
  ∀ a n : ℕ, accufact a n = a * (fact n) 
| a        0 := by simp[fact, accufact]
| a  (n + 1) := begin
simp[fact],
simp[accufact],
simp[accufact_an_eq_afactn],
-- ZZZ: You can merge these `simp`s if you want.
cc
end

lemma factn_eq_qfactn(n : ℕ) :
1 * (fact n) = fact n := by simp[mul_comm]


lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = fact n := 
  by simp[accufact_an_eq_afactn]


/- 2.2 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

/--
For the goal of this lemma is to proof:`∀n:ℕ, accufact 1 n = fact n`, and we can get following trsmition:
`∀n:ℕ, accufact 1 n = fact n`
= `∀n:ℕ, accufact 1 n = 1 * (fact n)` --by definition of `mul_comm` (Proved in `factn_eq_qfactn`)
= `∀a n:ℕ, accufact a n = a * (fact n)` when `a = 1`
-- ZZZ: This last step makes no sense. I don't even understand what you're trying to
-- prove here.

-- ZZZ: You've ignored the guidelines given in question 1.4 of the exercise, about the
-- need to state induction hypotheses, invocations of inductions, etc. For
-- ∀n:ℕ, accufact 1 n = fact n`, there's a spurious case distinction (which your
-- Lean proof doesn't have). -1.5pt

### 2.2 Proof of qeustion 2.1
So as shown above, as long as I can proof `∀a n:ℕ, accufact a n = a * (fact n)` then I can get `∀n:ℕ, accufact 1 n = fact n`, because it is a special case of `∀a n:ℕ, accufact a n = a * (fact n)`. I defined `∀a n:ℕ, accufact a n = a * (fact n)` as a sub-goal to accomplish the final goal.

#### Sub-goal `∀a n:ℕ, accufact a n = a * (fact n)`'s proof
__case a  0__
To simplify the sub-goal's left-hand side's case `a  0`:
accufact a  0:
= a                                   -- by definition of `accufact`

To simplify the sub-goal's right-hand side's case `a  0`:
a * (fact n):
= a * 1                              -- by definition of `fact`
= a                                  -- by definition of `mul_comm`

The two sides are equal with case `a 0`.
__case a  (n + 1)__
To simplify the sub-goal's left-hand side's case `a  (n + 1)`:
accufact a  (n + 1):
= accufact ((n + 1) * a) n           -- by definition of `accufact`
= ((n + 1) * a) * (fact n)           -- by the sub-goal's induction hypothesis

To simplify the sub-goal's right-hand side's case `a  (n + 1)`:
a * (fact n + 1)
= a * ((n + 1) * fact n)             -- by definition of `fact`

The two sides are equal with case `a  (n + 1)`.

For both case the sub-goal's induction hypothesis is true.

#### Goal `∀n:ℕ, accufact 1 n = fact n`'s proof
__case 0__
To simplify the goal's left-hand side's case `0`:
accufact 1 0
= 1                                 -- by definition of `accufact`

To simplify the goal's right-hand side's case `0`:
fact 0
= 1 * (fact 0)                      -- by definition of `factn_eq_qfactn`
= 1 * 1                             -- by definition of `fact`
= 1
The two sides are equal with case `0`.

__case (n + 1)__
To simplify the goal's left-hand side's case `(n + 1)`:
accufact 1 (n + 1)
= ((n + 1) * 1) * (fact n)      -- by definition of sub-goal's

To simplify the goal's right-hand side's case `(n + 1)`:
fact (n + 1)
= (n + 1) * fact n      -- by definition of `fact`

The two sides are equal with case `(n + 1)`.

The two sides are equal. QED
--/

-- ZZZ: Our solution (very similar to the model answer to exercise 4 question 1.4):

/- The generalized lemma we prove is `accufact_eq_fact_mul`:

    ∀n a, accufact a n = fact n * a

We perform the proof by structural (mathematical) induction on `n`,
generalizing `a`.

Case 0: The goal is `accufact a 0 = fact 0 * a`. The left-hand side is `a` by
definition of `accufact`. The right-hand side is `a` by definition of `fact` and
`*`.

Case `m + 1`: The goal is `accufact a (m + 1) = fact (m + 1) * a`. The induction
hypothesis is `∀a, accufact a m = fact m * a`.

Let us simplify the goal's left-hand side:

      accufact a (m + 1)
    = accufact ((m + 1) * a) m   -- by definition of `accufact`
    = fact m * ((m + 1) * a)     -- by the induction hypothesis
    = fact m * (m + 1) * a       -- by associativity of `*`

Now let us massage the right-hand side so that it matches the simplified
left-hand side:

      fact (m + 1) * a
    = (m + 1) * fact m * a        -- by definition of `fact`
    = fact m * (m + 1) * a        -- by commutativity of `*`

The two sides are equal.

The desired propery follows from `accufact_eq_fact_mul` by setting `a` to be `1`
and by simplifying away `* 1`. QED -/


/- ## Question 3 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/- 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma nat.succ_eq_1_self (n : ℕ) :
  nat.succ n = n + 1 :=
begin
  induction' n,
  { simp },
  { simp [ih] }
end

lemma nat.doublen_add2_eq_2mul_nadd1 (n: ℕ):
2 * n + 2 = 2 * (n + 1):=
begin
  induction' n,
  {simp},
  {
    simp[nat.succ_eq_1_self],
    simp[mul_add],
    }
end

lemma sum_upto_eq (m : ℕ):
   2 * sum_upto (λi, i) m = m * (m + 1) :=
begin 
  induction' m,
  case nat.zero {refl},
  case nat.succ: m ih {  
    
    simp[sum_upto], -- 2 * (sum_upto (λ (i : ℕ), i) n + (n + 1)) = nat.succ n * nat.succ n + nat.succ n
    simp[nat.succ_eq_1_self],
    simp[mul_add],
    simp[ih],
    simp[nat.doublen_add2_eq_2mul_nadd1],
    simp[two_mul],
    cc
  },
end


/- 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n 
| 0      := by refl
| (n + 1):= begin
 simp[sum_upto],
 simp[sum_upto_mul],
 cc
end

end LoVe
