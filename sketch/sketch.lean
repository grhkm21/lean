import data.nat.basic
import data.nat.prime
import data.nat.prime_norm_num
import tactic

example {a b : ℕ} (h : a < b) : a + 1 ≤ b :=
begin
  library_search!,
end

example : ¬ nat.prime 0 :=
begin
  exact nat.not_prime_zero,
end

example : nat.prime 17 :=
begin
  norm_num,
end
