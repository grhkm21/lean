import tactic

def fib : ℕ -> ℤ
| 0 := 0
| 1 := 1
| (x+2) := fib (x) + fib (x+1)

lemma fib_rule (n : ℕ) : fib(n + 2) = fib(n) + fib(n + 1) := rfl

theorem strong_induction {P : ℕ → Prop} {H : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n} (n : ℕ) : P n := sorry, -- this is already proven

lemma fib_rule' (n : ℕ) (h : 0 < n) : fib (n + 1) = fib n + fib (n - 1) := sorry

theorem fib_add (m n : ℕ) (hm : 0 < m) : fib(m + n) = fib(n + 1) * fib(m) + fib(n) * fib(m - 1) :=
begin
  apply strong_induction n,
  -- use `intros` instead of `intro`
  intros k h,
  -- using by_cases instead of cases for... my eyes
  cases k,
  { simp [fib], },
  { cases k,
    { -- see how `fib_rule'` takes arguments, so i supply them? in `fib_rule' m hm`
      simp [fib, fib_rule' m hm],
    },
    { simp only [nat.succ_eq_add_one, add_assoc],
      norm_num,
      -- we "massage" things into the right form, then expand everything
      rw [← add_assoc, fib, nat.succ_eq_add_one, add_assoc m k 1],
      rw [h k _, h (k + 1) _],
      rw [fib_rule (k + 1), fib_rule k],
      -- and then ring gets rid of everything
      ring,
      exact nat.lt_succ_self _,
      exact lt_trans (nat.lt_succ_self _) (nat.lt_succ_self _),
    },
  },
end


example (m n : ℕ) (hm : m > 0) (h : m ∣ n): fib(m) ∣ fib(n) :=
begin
  rcases h with ⟨k, rfl⟩,
  induction k with k hk,
  { simp only [fib, mul_zero, dvd_zero], },
  { rw [nat.succ_eq_add_one, mul_add, add_comm, mul_one, fib_add m _ hm],
    simp only [dvd_add, dvd_mul_left, dvd_mul_of_dvd_left hk], },
end