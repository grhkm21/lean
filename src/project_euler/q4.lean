import data.bool.all_any
import data.list.intervals
import data.nat.digits
import data.seq.seq
import data.set.prod
import data.nat.prime
import tactic

noncomputable theory

def palindromes := (finset.range (10 ^ 6 + 1)).filter (λ n, (nat.digits 10 n).palindrome)

def three_digits := finset.Ico 100 1000

def is_prod (n : ℕ) (s : finset ℕ) := s.filter (λ k, n % k = 0 ∧ n / k ∈ s)

def filtered := palindromes.filter (λ k, (is_prod k three_digits).card ≠ 0)

-- 906609
-- #eval filtered.max

set_option profiler true