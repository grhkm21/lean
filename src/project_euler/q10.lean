import data.bool.all_any
import data.list.intervals
import data.nat.digits
import data.seq.seq
import data.set.prod
import data.nat.prime
import data.nat.prime_norm_num
import tactic

def filter (s : list ℕ) (p : ℕ) := s.filter (λ n, n % p ≠ 0)

def filter' : list ℕ → list ℕ → list ℕ
| s [] := s
| s (p :: ps) := filter' (s.filter (λ n, n = p ∨ n % p ≠ 0)) ps

def final_filter : list ℕ → ℕ → list ℕ
| [] _ := []
| s n :=
  if h : s.length * s.length ≤ n + 1 then
    s
  else
    have h1 : (filter s.tail s.head).length ≤ s.tail.length,
    { rw [filter, ← list.countp_eq_length_filter], apply list.countp_le_length, },
    have h2 : (filter s.tail s.head).length - (n + 1) < s.length - n,
    { push_neg at h,
      rw nat.lt_iff_add_one_le at h,
      apply lt_of_le_of_lt ((nat.sub_le_sub_iff_right _).2 h1);
      { simp, sorry, }, },
    s.head :: final_filter (filter s.tail s.head) (n + 1)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, s.1.length - s.2)⟩] }

meta def final_filter' : list ℕ → list ℕ
| [] := []
| s := s.head :: final_filter' (filter s.tail s.head)

meta def prime_sum : list ℕ → ℕ → ℕ
| [] s := s
| (l :: ls) s := prime_sum (filter ls l) (s + l)

meta def prime_sum' : list ℕ → ℕ
| [] := 0
| (l :: ls) := l + prime_sum' (filter ls l)

-- set_option profiler true

-- First filter primes under 2000
def small_primes := final_filter (list.Ico 2 1500) 2
-- #eval small_primes

def segment_prime_sum : ℕ → ℕ → ℕ
| l h := do
  if l ≤ 1 then
    (filter' (list.Ico 2 h) (final_filter (list.Ico 2 (nat.sqrt h + 1)) 2)).sum
  else
    (filter' (list.Ico l h) (final_filter (list.Ico 2 (nat.sqrt h + 1)) 2)).sum

-- Then naive filter with these primes
-- #eval (filter' (list.Ico 2 2000000) [2, 3, 5]).sum
-- #eval (filter' (list.Ico 2 2000000) (small_primes.take 100)).sum

-- #eval (filter' (list.Ico 2 500000) small_primes).sum
#eval (list.Ico 0 5).map (λ n, segment_prime_sum (n * 100000) ((n + 1) * 100000))
#eval (list.Ico 5 10).map (λ n, segment_prime_sum (n * 100000) ((n + 1) * 100000))
#eval (list.Ico 10 15).map (λ n, segment_prime_sum (n * 100000) ((n + 1) * 100000))
#eval (list.Ico 15 20).map (λ n, segment_prime_sum (n * 100000) ((n + 1) * 100000))

/-
[454396538, 1255204276, 1999906301, 2749394417, 3455334664]
[4157590150, 4838459967, 5555377126, 6223668827, 6861069758]
[7575351672, 8307652436, 8854589641, 9593260875, 10193186609]
[10804148932, 11572366516, 12130179143, 12870295635, 13462395440]
Answer: 142913828922
-/

-- #eval (filter' (list.Ico 500000 600000) small_primes).sum
-- #eval (final_filter (list.Ico 2 30000) 2).sum
-- #eval (final_filter' (list.Ico 2 30000)).sum
-- #eval (prime_sum (list.Ico 2 30000) 0)
-- #eval (prime_sum' (list.Ico 2 30000))