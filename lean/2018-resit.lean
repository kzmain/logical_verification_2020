import .lovelib

import .love03_forward_proofs_demo

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe
namespace temp

inductive tc₁ {α:Type} (r : α → α → Prop): α → α → Prop 
|base:∀a b,r a b → tc₁ a b
|step:∀a b c,r a b → tc₁ b c → tc₁ a c

inductive tc₂ {α:Type} (r : α → α → Prop): α → α → Prop 
|pet :∀a b c, (tc₂ a b) → (r b c) → tc₂ a c

inductive tc₃ {α:Type} (r : α → α → Prop): α → α → Prop 
|trans :∀a b c, (tc₃ a b) → (tc₃ b c) → tc₃ a c

lemma tc3_step {α : Type} (r : α → α → Prop) : 
    ∀a b c:α, r a b → tc₃ r b c → tc₃ r a c:=
    begin
        intros a b c hrab h3rbc,
        apply tc₃.trans,
        {
            sorry
        },
        {apply h3rbc,},
    end


lemma tc1_pets {α : Type} (r : α → α → Prop) : 
    ∀a b c : α, tc₁ r a b → r b c → tc₁ r a c :=
    begin
        intros a b c htcab hrbc,
        sorry
    end

def mem {α : Type} (a : α) : list α → Prop
| []        := false
| (x :: xs) := x = a ∨ mem xs

def reverse {α : Type} : list α → list α 
| [] := []
| (x :: xs) := reverse xs ++ [x]

def count {α : Type} (a : α):  list α →  ℕ
| list.nil        := 0
| (x::xs)         := 1 + (count xs)
-- | []        := 0
-- | (x :: xs) := count xs + 1


lemma count_eq_zero_iff_not_mem {α : Type} (a : α) 
    : ∀xs, count a xs = 0 ↔ ¬ mem a xs
| []            := begin
    apply iff.intro,
    intros hc hm,
    finish,
    intros,
    finish,
end
| (x::xs)       := begin
    apply iff.intro,
    {intros hc hm,
    finish
    },
    {
        intros hm,
        finish,
    }
end 

lemma count_append {α : Type} (a : α):
  ∀xs ys : list α, count a (xs ++ ys) = count a ys + count a xs
  | []        ys := by simp [count]
  | xs        [] := by simp [count]
  | (x :: xs) (y::ys) := begin
      simp[count],
      simp[count_append],
      simp[count],
      cc,
  end

lemma count_reverse_eq_count {α : Type} (a : α) :
∀xs : list α, count a (reverse xs) = count a xs
| []         := by refl
| (x::xs)         := begin
simp[count],
simp[reverse],
simp[count_append],
finish,
end

inductive tree (α : Type) : Type
| empty {} : tree
| bin : α → tree → tree → tree
| ter : α → tree → tree → tree → tree

def map_tree {α β : Type} (f : α → β) : tree α → tree β
-- :=
-- sorry
| tree.empty := tree.empty
| (tree.bin a l r) := tree.bin (f a) (map_tree l) (map_tree r)
| (tree.ter a l m r) := tree.ter (f a) (map_tree l) (map_tree m) (map_tree r)

inductive is_binary {α : Type} : tree α → Prop 
| empty                         : is_binary tree.empty
| node (a : α) (l r : tree α)   : is_binary (tree.bin a l r)

lemma is_binary_map_tree {α β : Type} {f : α → β} 
: ∀t : tree α, is_binary t → is_binary (map_tree f t):=
begin
    intros t hbt,
    induction' hbt,
    {simp[map_tree],
    simp[is_binary.empty]},
    {simp[map_tree],
    simp[is_binary.node],}
end

def btree (α : Type) : Type 
-- := _
| btree.empty : btree
| node     : α → btree → btree → btree

end temp
end LoVe

