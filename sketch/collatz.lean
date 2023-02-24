import data.stream.defs
import data.bool.all_any
import data.lazy_list
import tactic

open expr tactic widget

def collatz_one_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else 3 * n + 1

def collatz : ℕ → stream ℕ
  | n 0 := n
  | n (k + 1) := collatz_one_step (collatz n k)

variable (n : ℕ)

def collatz_conjecture : Prop := ∃ k : ℕ, collatz n k = 1

-----------------------------------------------------------------

meta def prove_even_aux : ℕ → tactic unit
| n :=
do {
  `(even %%p) ← target,
  tp ← infer_type p,
  guard (tp = `(ℕ)),
  to_expr ``(%%(reflect n)) >>= existsi,
  exact_dec_trivial,
  trace $ (to_string n) ++ " works!" }
<|> (do
  trace $ (to_string n) ++ " doesn't work.",
  (prove_even_aux n.succ)
)

meta def prove_even : tactic unit := prove_even_aux 4

-----------------------------------------------------------------

meta def prove_collatz_aux : Π n : ℕ, tactic unit
| n :=
do {
  `(collatz_conjecture %%p) ← target,
  tp ← infer_type p,
  guard (tp = `(ℕ)),
  to_expr ``(%%(reflect n)) >>= existsi,
  exact_dec_trivial,
  trace $ (to_string n) ++ " works!!"
}
<|> (do
  trace $ (to_string n) ++ " doesn't work.",
  (prove_collatz_aux n.succ)
)

meta def prove_collatz : tactic unit := prove_collatz_aux 0

example : even 8 := by prove_even
example : even 8 := by use 4
example : even 8 := Exists.intro 4 (id (eq.refl 8))

example : collatz_conjecture 13 := by prove_collatz
example : collatz_conjecture 13 := by { use 9, dsimp [collatz, collatz_one_step], norm_num, }

set_option profiler true

theorem small_collatz : ∀ n (h : 1 ≤ n ∧ n ≤ 10), collatz_conjecture n :=
begin
  rintro n ⟨ln, hn⟩,
  replace hn := nat.lt_succ_of_le hn,
  interval_cases using ln hn;
  -- prove_collatz,
end

-- This requires 110 iterations, won't work -- it literally times out
theorem collatz_27 : collatz_conjecture 27 := by prove_collatz

-- However, if I compute the collatz list directly, it works?
#eval (collatz 27).take 112
#eval ((list.range 501).filter (λ n, collatz 27 n = 1)).nth 0

-- The following takes 238 iterations
#eval (collatz 3711).take 238
#eval ((list.range 500).filter (λ n, collatz 3711 n = 1)).nth 0

-- Large numbers (1242 iterations)
def N := 128202387348288784730229060763884567453
#eval (collatz N).nth 5
#eval ((list.range 2000).filter (λ n, collatz N n = 1)).nth 0