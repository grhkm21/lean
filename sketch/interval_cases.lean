import tactic

open expr interactive tactic

-- Here is an attempt to "fix" `interval_cases`, which is quite slow

namespace tactic
namespace interactive

setup_tactic_parser

meta def interval_cases_aux' : expr → expr → expr → ℤ → tactic unit
| v l h d := do
  if 0 < d then (do
    trace $ "-> " ++ (to_string l),
    pf ← to_expr ``(nat.le_succ %%l),
    nm ← get_unused_name v.local_pp_name,
    trace nm,
    trace pf,
    -- TODO: Instead of adding a new goal, somehow create a new subgoal and reduce the other goals
    note "h" none pf,
    succ_l ← (to_expr ``(nat.succ %%l)),
    interval_cases_aux' v succ_l h (d - 1)
  ) else skip

meta def interval_cases' (bounds : parse (prod.mk <$> ident <*> ident)) :
  tactic unit :=
do
  [l1, l2] ← [bounds.1, bounds.2].mmap get_local,
  `(%%l ≤ %%v1) ← infer_type l1,
  `(%%v2 < %%h) ← infer_type l2,
  guard (v1 = v2),
  match (l.to_int, h.to_int) with
  | (some l', some h') := interval_cases_aux' v1 l h (h' - l')
  | _ := fail "not integers?"
  end

-- Create a tactic that splits goal
meta def split_prop : tactic unit :=
do {
  [c] ← target >>= get_constructors_for,
  mk_const c >>= tactic.apply,
  all_goals split_prop
} <|> skip

example {n : ℕ} (h : 1 ≤ n) (h' : n < 10) : true :=
begin
  interval_cases' h h',
  trivial,
end

example {n : ℕ} (h : 1 ≤ n) (h' : n < 5) : true :=
begin
  show_term { interval_cases using h h' };
  trivial,
end

example {A B C : Prop} : B ∧ C ∧ (A ∨ B ∨ C) ∧ (B ∨ C) :=
by split_prop

end interactive
end tactic

---------------------------------------------------------

-- If goal is a ≤ x ∧ a ≠ x, change it to a < x
meta def change1 : tactic unit :=
do
  `(%%a1 ≤ %%x1 ∧ %%a2 ≠ %%x2) ← target,
  guard (a1 = a2 ∧ x1 = x2),
  -- applyc `lt_iff_le_and_ne,
  to_expr ``(lt_iff_le_and_ne.1) >>= apply,
  trace target

example (a x : ℕ) : a ≤ x ∧ a ≠ x := by change1
example (a x : ℕ) : a ≤ x ∧ a ≠ x := by rw ← lt_iff_le_and_ne

-- If goal is 1 ≤ n ∧ n < 10, change it to
-- (n = 1) ∨ (n ≠ 1 ∧ 1 ≤ n ∧ n < 10)
-- (n = 1) ∨ (2 ≤ n ∧ n < 10)
lemma lem {a b n : ℕ} (h : a < b) : (a ≤ n ∧ n < b) ↔ (a = n) ∨ (a.succ ≤ n ∧ n < b) := by omega

meta def change : tactic unit :=
do
  `(%%a1 ≤ %%x1 ∧ %%a2 ≠ %%x2) ← target,
  guard (a1 = a2 ∧ x1 = x2)

example (a b x : ℕ) (h : a < b) : a ≤ x ∧ x < b := by sorry
example (a b x : ℕ) (h : a < b) : a ≤ x ∧ x < b := by rw lem

example {A B C D : Prop} (hp : A ∧ B) (h : A ∧ B → C) (h' : D) : C ∧ D :=
by conv_lhs {}