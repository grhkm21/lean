import data.stream.defs
import data.bool.all_any
import data.lazy_list
import tactic

open expr tactic widget

meta def ft : tactic unit :=
trace "f" >> trace "t"

meta def st : tactic unit :=
fail "st"

meta def ot : tactic unit :=
st <|> ft

meta def trace_goal : tactic unit :=
target >>= trace

meta def trace_goal_is_eq : tactic unit :=
do t ← target,
  match t with
  | `(%%l = %%r) := trace $ "hmm " ++ (to_string l) ++ " ?= " ++ (to_string r)
  | _ := trace "goal is not ="
end

meta def list_types : tactic unit :=
do
  l ← local_context,
  trace l,
  l.mmap' (λ h, infer_type h >>= trace)

#eval ft
#eval st
#eval ot
#eval trace_goal
#eval trace_goal_is_eq

#eval trace $ to_raw_fmt $ (`(λ x : ℕ, x) : expr)
#eval trace $ succ_fn `(λ x : ℤ, 2 * x)

example : true :=
begin
  trace_goal,
  trace_goal_is_eq,
  have : 1 = 2,
  {
    trace_goal,
    trace_goal_is_eq,
    sorry,
  },
  let l := [1, 2, 3, 4],
  list_types,
end

/-
Below are examples that deal with *raw* expr.
These are context-unaware and is not ideal for manipulation.
-/

-- helper function instead of `expr.mk_app`
meta def mk_app (e1 e2 : expr) : expr := app e1 e2

-- function that takes a function `f` and returns essentially `f + 1`
meta def succ_fn : expr → option expr
| (lam var_name bi var_type body) :=
  let new_body := mk_app `(nat.succ) body in
  lam var_name bi var_type new_body
| _ := none

/-
Below, we use `tactic` that allows context-aware metaprogramming
Tutorial: https://www.youtube.com/watch?v=qsmnBNXgZgc
-/

meta def inspect_dump : tactic unit :=
do t ← target,
  trace t,
  a_expr ← get_local `a <|> return `(0),
  trace (to_raw_fmt a_expr),
  a_type ← infer_type a_expr,
  trace a_type,
  ctx ← local_context,
  trace ctx,
  -- new_nat ← 40 won't work since 40 is not a tactic
  -- Either use `new_nat ← return 40` or
  let new_nat := 40,
  trace new_nat

example (a b c : ℤ) : a = b := by do inspect_dump
example (b c : ℤ) : b = c := by do inspect_dump

/-
Now we implement the `assumption` tactic, which looks through local context
and look for a hypothesis that closes the current goal.
-/

meta def map_over_lc (tgt : expr) : list expr → tactic unit
| [] := fail "assump failed."
| (f :: fs) := exact f <|> map_over_lc fs

meta def assump : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   map_over_lc tgt ctx

-- This pattern is common and has been implemented already
meta def assump' : tactic unit :=
local_context >>= list.mfirst (λ e, exact e)

example {A B C : Prop} (ha : A) (hb : B) (hc : C) : C := by assump
example {A B C : Prop} (ha : A) (hb : B) (hc : C) : C := by assump'
example {n : ℕ} (hn : n + 0 = 5) : n = 5 := by assump'

/-
More ad-hoc tactic practices
-/

#check interactive.dec_trivial

meta def add_refl_hyp (e : expr) : tactic unit :=
do tp ← infer_type e,
   guard (tp = `(ℕ)),
  --  pf ← mk_app `eq.refl [e],
   pf ← to_expr ``(not_lt_of_ge (ge_of_eq (eq.refl %%e))),
   nm ← get_unused_name,
   note nm none pf,
   return ()

meta def add_refl : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   trace ctx,
   ctx.mmap' (λ e, try (add_refl_hyp e)),
   return ()

example {a b c : ℕ} (ha : a = b) : true := by do add_refl