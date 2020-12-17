-- ZZZZ: 8.5pt -- see comments below

import .love02_backward_proofs_exercise_sheet


/- # LoVe Homework 2: Backward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/- ## Question 1 (4 points): Connectives and Quantifiers

1.1 (3 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
begin
  intros hab hca hc,
  apply hab,
  apply hca,
  apply hc,
end

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
begin
  intros habc hab ha,
  apply habc,
  apply ha,
  apply hab,
  apply ha,
end

lemma more_nonsense (a b c : Prop):
  (c → (a → b) → a) → c → b → a :=
begin
  intros hcaba hc hb,
  apply hcaba,
  apply hc,
  intros ha,
  apply hb
end

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
begin
  intros haab hbc ha hb,
  apply hbc,
  apply haab,
  apply ha,
  apply ha,
end

/- 1.2 (1 point). Prove the following lemma using basic tactics. -/

lemma weak_peirce (a b : Prop):
  ((((a → b) → a) → a) → b) → b :=
begin
  intro habaab,
  apply habaab,
  intros haba,
  apply haba,
  intros ha,
  apply habaab,
  intros haba',
  apply ha,
end
/- ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about implication using basic
tactics.

Hints:

* Keep in mind that `¬ a` is the same as `≈. You can start by invoking
  `rw not_def` if this helps you.

* You will need to apply the elimination rules for `∨` and `false` at some
  point. -/

lemma about_implication (a b : Prop):
  ¬ a ∨ b → a → b :=
begin
  rw not_def,
  intros hnab ha,
  induction' hnab,
  {cc,},
  {apply h}
end
/- 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* You can use `rw double_negation` to unfold the definition of
  `double_negation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn :
  double_negation → excluded_middle :=
begin
  rw double_negation,
  rw excluded_middle,
  intros hdn a,
  apply hdn,
  intros nana,
  apply nana,
  apply or.intro_right a,
  sorry -- ZZZ -0.5pt

end

-- ZZZ: Our solution:

lemma em_of_dn_ZZZ :
  double_negation → excluded_middle :=
begin
  rw double_negation,
  rw excluded_middle,
  intros hdoubleneg a,
  apply hdoubleneg,
  intro hnaona,
  apply hnaona,
  apply or.intro_right,
  intro hna,
  apply hnaona,
  apply or.intro_left,
  assumption
end


/- 2.3 (2 points). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

-- ZZZ: You ignored the "exploiting the three theorems we already have" part of
-- the question. -1pt. We expected something like this (three times):

lemma peirce_of_dn_ZZZ :
  double_negation → peirce :=
begin
  intro h,
  apply peirce_of_em,
  apply em_of_dn,
  exact h
end

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

-- enter your solution here
lemma dn_of_em :
  excluded_middle → double_negation :=
begin
  rw excluded_middle,
  rw double_negation,
  intros hem a hnna,
  apply or.elim (hem a),
  { intro ha,
    assumption },
  {
    intro hna,
    apply false.elim,
    apply hnna,
    exact hna,
  }
end

lemma em_of_peirce :
  peirce → excluded_middle :=
begin
  rw peirce,
  rw excluded_middle,
  intros hpeirce a,
  apply hpeirce,
  intros hem,
  apply hem,
  apply or.intro_right a,
  sorry
end

lemma peirce_of_dn :
double_negation → peirce:=
begin
  rw double_negation,
  rw peirce,
  intros hdn a b haba,
  apply hdn,
  intros hna,
  sorry
end
end backward_proofs

end LoVe
