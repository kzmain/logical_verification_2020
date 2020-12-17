--ZZZZ: 8pt – Good work on question 1, but never change lemma statements like you do in question 2!
import .love02_backward_proofs_exercise_sheet


/- # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (6 points + 1 bonus point): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn:
  double_negation → peirce :=
  assume hdn: double_negation,
  have hem: excluded_middle:=
  sorry_lemmas.em_of_dn (hdn),
  have hpei: peirce:=
    peirce_of_em (hem),
  show peirce, from hpei

lemma em_of_peirce :
  peirce → excluded_middle :=
  assume hp : peirce,
  have hdn: double_negation:=
  dn_of_peirce (hp),
  have hem: excluded_middle:=
  sorry_lemmas.em_of_dn (hdn),
  show excluded_middle, from hem

lemma dn_of_em :
  excluded_middle → double_negation :=
  assume hem: excluded_middle,
  have hp: peirce:=
  peirce_of_em hem,
  have hdn: double_negation:=
  dn_of_peirce hp,
  show double_negation, from hdn


end backward_proofs

/- 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
iff.intro 
  (
    assume hpq: ∃ x , p x ∧ q x,
    exists.elim hpq 
    (assume x,
    assume hx : p x ∧ q x,
    show ∃ x, q x ∧ p x, from ⟨x, hx.right, hx.left⟩)
  )
  (
    assume hqp: ∃ x , q x ∧ p x,
    exists.elim hqp 
    (assume x,
    assume hx : q x ∧ p x,
    show ∃ x, p x ∧ q x, from ⟨x, hx.right, hx.left⟩)
  )

/- 1.3 (1 bonus point). Supply a structured proof of the following property,
which can be used pull a `∀`-quantifier past an `∃`-quantifier. -/

lemma forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hxy : ∃ x , ∀ y , p x y,
  exists.elim hxy(
    assume a: α,
    assume hdd: (∀ y , p a y),
    show ∀ (y : α), ∃ (x : α), p x y, from 
      begin
        intros e,
        apply exists.intro a,
        apply hdd e,
      end
   )
   

/- ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied "Logic and Sets" with Prof. Fokkink, you will know he is
very fond of logic puzzles. This question is meant as a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/- 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma weak_peirce₂ (a b: Prop): --ZZZ: (hb: b): – Never change lemma statements!
   ((((a → b) → a) → a) → b) → b := --ZZZ: λg, hb – This is cheating!
--ZZZ: -1pt, a solution is
λ(habaab : (((a → b) → a) → a) → b),
  habaab (λhabaa : (a → b) → a,
    habaa (λha : a,
      habaab (λhaba : (a → b) → a,
        ha)))

/- There are in fact three easy ways:

* Copy-paste the result of `#print weak_peirce`.

* Simply enter `weak_peirce` as the proof term for `weak_peirce₂`.

* Reuse the answer to question 3.2 of homework 1. -/


/- 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ (a b: Prop): --ZZZ: (hb: b): – Never change lemma statements!
((((a → b) → a) → a) → b) → b :=
/-ZZZ: assume habaab : (((a → b) → a) → a) → b ,
       show b, from hb – This is cheating!
-2pt, a solution is -/
assume habaab : (((a → b) → a) → a) → b,
show b, from
  habaab
    (assume habaa : (a → b) → a,
     show a, from
       habaa
         (assume ha : a,
          show b, from
            habaab
              (assume haba : (a → b) → a,
                show a, from
                  ha)))


end LoVe
