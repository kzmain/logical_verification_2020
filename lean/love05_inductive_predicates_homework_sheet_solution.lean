--ZZZZ: 9pt – see comments below.
import .lovelib


/- # LoVe Homework 5: Inductive Predicates

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (3 points): A Type of λ-Terms

Recall the following type of λ-terms from question 3 of exercise 4. -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/- 1.1 (1 point). Define an inductive predicate `is_app` that returns true if
and only if its argument has an `app` constructor at the top level. -/

-- enter your definition here
inductive is_app {α β : term}: term → Prop
| app: is_app(term.app α β)

/- 1.2 (2 points). Define an inductive predicate `is_abs_free` that is true if
and only if its argument is a λ-term that contains no λ-expressions. -/

-- enter your definition here
inductive is_abs_free{α β : term} {s: string}: term → Prop
| var: is_abs_free(term.var s)
| app: is_abs_free(term.app α β)

--ZZZ: -1pt because your predicate tests if a term isn't a λ-expression isntead of testing if it doesn't contain one as a subterm. Consequenlty you miss the point of writing recursion/induction aspect of the predicate. A desired solution is
inductive is_abs_free' : term → Prop
| var (s : string) : is_abs_free' (term.var s)
| app (t u : term) (ht : is_abs_free' t) (hu : is_abs_free' u) :
  is_abs_free' (term.app t u)


/- ## Question 2 (6 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive even : ℕ → Prop
| zero            : even 0
| add_two {n : ℕ} : even n → even (n + 2)

/- 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `even`,
and should not rely on `even`. -/

inductive odd : ℕ → Prop
| one            : odd 1
| add_two {n : ℕ} : odd n → odd (n + 2)

/- 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

lemma odd_3 :
  odd 3 :=
begin
  apply odd.add_two,
  apply odd.one
end

lemma odd_5 :
  odd 5 :=
begin
  apply odd.add_two,
  apply odd.add_two,
  apply odd.one
end

/- 2.3 (2 points). Prove the following lemma by rule induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how rule
induction works (and is good practice for the final exam).

    lemma even_odd {n : ℕ} (heven : even n) :
      odd (n + 1) :=

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

/- The generalized lemma we prove is `even_odd`:

    ∀n: ℕ, heven : even n, odd (n + 1)

I perform the proof by structural (mathematical) induction on `heven`.

Case 0: The goal is to prove `odd(0 + 1)` is true.

Let us simplify the goal:

  odd(0 + 1)
= odd 1       -- by simp
= true        -- by definition of `odd.one`

Case `add_two`: The goal is to prove `odd (n + 2 + 1)` is true. The induction
hypothesis is ` ∀n: ℕ, heven : even n, odd (n + 1)` is true.
ZZZ: Your claimed IH is the lemma itself. Instead the IH is just odd(n+1).

Let us simplify the goal's left-hand side:

      odd (n + 2 + 1)
    = odd (n + 1)   -- by definition of `odd.add_two`
    = true          -- by the induction hypothesis

The two cases are true. QED -/

/- 2.4 (1 point). Prove the same lemma again, but this time in Lean: -/

lemma even_odd {n : ℕ} (heven : even n) :
  odd (n + 1) :=
begin
  induction' heven,
  case zero{
    simp,
    apply odd.one
  },
  case add_two: n heven ih{
    apply odd.add_two,
    simp [ih]
  }
end

/- 2.5 (1 point). Prove the following lemma in Lean.

Hint: Recall that `¬ a` is defined as `a → false`. -/

lemma even_not_odd {n : ℕ} (heven : even n) :
  ¬ odd n :=
begin
  apply not.intro,
  intro hodd,
  induction' hodd,
  case one:{
    induction' heven,
  },
  case add_two: heven hodd ih{
    apply ih,
    induction' heven,
    apply heven,    
  }
end

end LoVe
