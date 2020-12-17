-- import lean.love04_functional_programming_demo
namespace LoVe
lemma forall.one_point_rule {α: Type} {t : α} {p : α → Prop}:
(∀x : α, x = t → p x) ↔ p t:=
sorry

lemma exists.one_point_rule {α: Type} {t : α} {p : α → Prop}:
(∃x : α, x = t ∧ p x) ↔ p t:=
begin
    apply iff.intro,
    {
        intros h,
        sorry
    },
    {
        intros h,
        apply exists.intro t,
        apply and.intro,
        cc,
        cc
    }
end

lemma forall.one_point_rule_false₁ {α : Type} {t : α} {p : α → Prop} :
(∀x : α, x = t ∧ p x) ↔ p t:=
begin
    apply iff.intro,
    {
        intros _ ,
        apply and.elim_right,
        apply a,
    },
    {
        intros _ _,
        sorry
    }
end

lemma exists.one_point_false₂ {α : Type} {t : α} {p : α → Prop} :
(∃x : α, x = t → p x) ↔ p t:=
begin
    apply iff.intro,
    {
        intros h ,
        sorry
    },
    {
        intros pt,
        apply exists.intro t,
        intros _,
        apply pt,
    }
end

lemma forall_exists.one_point_rule {α : Type} {t : α} {p : α → Prop} :
(∀x : α, x = t → p x) ↔ (∃x : α, x = t ∧ p x):=
begin
    apply iff.intro,
    {intros h,
    apply exists.intro t,
    apply and.intro,
    refl,
    apply h,
    refl,
    },
    {
        intros h x eq,
        simp[eq],
        sorry
    }
end

def concat {α : Type} : list (list α) → list α
| [] := []
| (xs :: xss) := xs ++ concat xss

def map {α β : Type} (f : α → β) : list α → list β
| [] := []
| (x :: xs) := f x :: map xs

lemma map_concat {α β : Type} (f : α → β) :
∀xss : list (list α), map f (concat xss) = concat (map (map f) xss):=
begin
    intros xss,
    induction xss,
    case list.nil{refl},
    case list.cons{
        cases xss_hd,
        {
            apply xss_ih,
        },
        {
            simp[concat],
            simp[map],
            rw concat,
            rw ← xss_ih,
            simp,
            -- refl,
            sorry
        }
    }
end


inductive tree (α : Type) : Type
| empty {} : tree
| bin : α → tree → tree → tree
| ter : α → tree → tree → tree → tree

def map_tree {α β : Type} (f : α → β) : tree α → tree β
| map_tree nil :  tree empty {}
| map_tree bin (a : α) (l r : α) := map_tree (tree.bin a l r)
-- | (k + 2) := even₂ k


lemma map_tree_id {α : Type} :
∀t : tree α, map_tree (λx : α, x) t = t:=
sorry


end LoVe