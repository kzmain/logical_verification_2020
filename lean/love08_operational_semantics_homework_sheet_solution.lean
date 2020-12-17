-- ZZZZ: 10pt -- well done! -- see comments

import .lovelib
-- import .love07_metaprogramming_homework_sheet

/- # LoVe Homework 8: Operational Semantics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (6 points + 1 bonus point): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| unless : (state → Prop) → stmt → stmt
| repeat : ℕ → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/- The `skip`, `assign`, and `S ;; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b S` statement executes `S` unless `b` is true—i.e., it executes `S`
if `b` is false. Otherwise, `unless b S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S` is
equivalent to `S ;; S ;; S ;; S ;; S` (in terms of a big-step semantics at
least) and `repeat 0 S` is equivalent to `skip`.

1.1 (1.5 points). Complete the following definition of a big-step
semantics: -/

inductive big_step : stmt × state → state → Prop
| skip {s} :
  big_step (stmt.skip, s) s
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
| unless_false {b : state → Prop} {S s t} 
    (hS: big_step (S, s) t) (hcond: ¬ b s):
  big_step (stmt.unless b S, s) t
| unless_true {b : state → Prop} {S s} 
    (hcond: b s):
  big_step (stmt.unless b S, s) s
| repeat_0 {S s} 
    (n = 0 ):
   big_step (stmt.repeat n S, s) s
   -- ZZZ: You can kill `n` and write `0` directly instead. See my forthcoming
   -- Canvas post.
| repeat_n {n: ℕ} {S s u} (t)
    (hS: big_step (S, s) t)
    (hR: big_step(stmt.repeat n S, t) u):
  big_step(stmt.repeat (n + 1) S, s) u

infix ` ⟹ ` : 110 := big_step

/- 1.2 (1.5 points). Complete the following definition of a small-step
semantics: -/

inductive small_step : stmt × state → stmt × state → Prop
| assign {x a s} :
  small_step (stmt.assign x a, s) (stmt.skip, s{x ↦ a s})
| seq_step {S S' T s s'} (hS : small_step (S, s) (S', s')) :
  small_step (S ;; T, s) (S' ;; T, s')
| seq_skip {T s} :
  small_step (stmt.skip ;; T, s) (T, s)
| unless_false {b : state → Prop} {S s} (hcond: ¬ b s):
  small_step (stmt.unless b S, s) (S, s)
| unless_true  {b : state → Prop} {S s} (hcond:   b s):
  small_step (stmt.unless b S, s) (stmt.skip, s)
| repeat_0 {n : ℕ} {S s} (n = 0):
  small_step (stmt.repeat n S, s) (stmt.skip, s)
  -- ZZZ: Ditto.
| repeat_n {n : ℕ} {S s} :
  small_step (stmt.repeat (n + 1) S, s) 
    (S ;; stmt.repeat n S, s)

-- enter the missing cases here


infixr ` ⇒ ` := small_step
infixr ` ⇒* ` : 100 := star small_step

/- 1.3 (1 point). We will now attempt to prove termination of the REPEAT
language. More precisely, we will show that there cannot be infinite chains of
the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : stmt → ℕ
| stmt.skip         := 0
| (stmt.assign _ _) := 1
| (stmt.seq    stmt₀     stmt₁) := 1 + (mess stmt₀) + (mess stmt₁)
| (stmt.unless ____      stmt₁) := 1 + (mess stmt₁)
-- | (stmt.repeat 0         stmt₁) := 1
| (stmt.repeat n         stmt₁) := (n )* (mess stmt₁ + 2) + 1

-- enter the missing cases here

/- 1.4 (1 point). Consider the following program `S₀`: -/

def incr (x : string) : stmt :=
stmt.assign x (λs, s x + 1)

def S₀ : stmt :=
stmt.repeat 1 (incr "m" ;; incr "n")

/- Check that `mess` strictly decreases with each step of its small-step
evaluation, by giving `S₀`, `S₁`, `S₂`, …, as well as the corresponding values
of `mess` (which you can obtain using `#eval`). -/

-- enter your answer here
#eval mess S₀ -- expected 6

def S₁ : stmt :=
incr "m" ;;incr "n";;stmt.repeat 0 (incr "m" ;; incr "n")

#eval mess S₁ -- expected 5

def S₂ : stmt :=
stmt.skip;;incr "n";;stmt.repeat 0 (incr "m" ;; incr "n")

#eval mess S₂ -- expected 4

def S₃ : stmt :=
incr "n";;stmt.repeat 0 (incr "m" ;; incr "n")

#eval mess S₃ -- expected 3

def S₄ : stmt :=
stmt.skip;;stmt.repeat 0 (incr "m" ;; incr "n")

#eval mess S₄ -- expected 2

def S₅ : stmt :=
stmt.repeat 0 (incr "m" ;; incr "n")

#eval mess S₅ -- expected 1

def S₆ : stmt :=
stmt.skip

#eval mess S₅ -- expected 0

/- 1.5 (1 point). Prove that the measure decreases with each small-step
transition. If necessary, revise your answer to question 1.3. -/

lemma small_step_mess_decreases {Ss Tt : stmt × state} (h : Ss ⇒ Tt) :
  mess (prod.fst Ss) > mess (prod.fst Tt) :=
begin
  induction' h,
  repeat { 
      simp [mess],
      try{linarith}
  }
end

-- ZZZ: Lovely! For the record, our version:

lemma small_step_mess_decreases_ZZZ {Ss Tt : stmt × state} (h : Ss ⇒ Tt) :
  mess (prod.fst Ss) > mess (prod.fst Tt) :=
by induction' h; simp [mess, mul_add, add_mul] at *; linarith


/- 1.6 (1 bonus point). Prove that the inverse of the `⇒` relation is well
founded. The inverse is simply `λTt Ss, Ss ⇒ Tt`. A relation `≺` is well founded
if there exist no infinite left-descending chains of the form

    `⋯ ≺ x₂ ≺ x₁ ≺ x₀`

Proof strategy: The `measure` function from `mathlib` converts a function to `ℕ`
to a relation, using `<` to compare two numbers. Hence, start by proving that
`measure mess`, or rather `measure (mess ∘ prod.fst)`, is well founded. Here,
`library_search` can help, or just search manually in `wf.lean`, close to the
definition of `measure`. Then prove that `λTt Ss, Ss ⇒ Tt` is a subrelation of
`measure (mess ∘ prod.fst)` (using lemma `small_step_mess_decreases` from
question 1.4) and therefore (using another lemma from `wf.lean`) that it must be
well founded. -/

lemma small_step_wf :
  well_founded (λTt Ss, Ss ⇒ Tt) :=
begin
  sorry  -- ZZZ: -1pt
end

/- ## Question 2 (3 points): Inversion Rules

2.1 (1 point). Prove the following inversion rule for the big-step semantics
of `unless`. -/

lemma big_step_ite_iff {b S s t} :
  (stmt.unless b S, s) ⟹ t ↔ (b s ∧ s = t) ∨ (¬ b s ∧ (S, s) ⟹ t) :=
begin
  apply iff.intro,
  {
    intros h,
    cases' h,
    apply or.intro_right,
    cc,
    apply or.intro_left,
    cc
  },
  {
    intros h,
    cases' h,
    {
      cases' h,
      rw eq.symm right,
      apply big_step.unless_true,
      cc
    },
    {
      apply big_step.unless_false,
      cc,
      cc,
    }
  }
end
#print big_step.repeat_0

/- 2.2 (2 points). Prove the following inversion rule for the big-step
semantics of `repeat`. -/

lemma big_step_repeat_iff {n S s u} :
  (stmt.repeat n S, s) ⟹ u ↔
  (n = 0 ∧ u = s)
  ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (stmt.repeat m S, t) ⟹ u) :=
begin
  apply iff.intro,
  {
    intro h,
    induction' h,
    {
      apply or.intro_left,
      cc,
    },
    {
      apply or.intro_right,
      apply exists.intro (n),
      apply exists.intro t,
      simp[h, h_1],
    }
  },
  {
    intro h,
    cases' h,
    {
      cases' h,
      simp [left, right],
      apply big_step.repeat_0,
      refl
    },
    {
      cases' h,
      cases' h,
      cases' h,
      rw left,
      apply big_step.repeat_n,
      apply (and.elim_left right),
      apply (and.elim_right right),
    }
  }
end
#print big_step.repeat_n
end LoVe
