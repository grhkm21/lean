import tactic

open_locale big_operators

example {f : ℚ → ℚ}
(h : ∀ x, ∀ y, f (x + y) = f x + f y) : ∀ x, f x = x * f 1 :=
begin
  have f_zero : f 0 = 0,
  { specialize h 0 0, simpa using h, },
  have f_nat_mul : ∀ n : ℕ, ∀ x, f (n * x) = n * f x,
  { intros n x,
    induction n with k hk,
    { simp only [nat.cast_zero, zero_mul, f_zero], },
    { simp only [nat.succ_eq_add_one, nat.cast_add_one, add_mul, one_mul, h, hk], },
  },
  have f_nat : ∀ n : ℕ, f n = n * f 1,
  { intro n, rw [← f_nat_mul n 1, mul_one], },
  have f_neg : ∀ x, f (-x) = -(f x),
  { intro x, rw [eq_neg_iff_add_eq_zero, ← h, neg_add_self, f_zero], },
  have f_int_mul : ∀ n : ℤ, ∀ x, f (n * x) = n * f x,
  { intros n x,
    cases n,
    { rw [int.of_nat_eq_coe, ← coe_coe, f_nat_mul], },
    { simp only [int.neg_succ_of_nat_eq, int.cast_neg, neg_mul, f_neg, neg_mul, neg_inj,
                 int.cast_add, ← coe_coe, int.cast_one, add_mul, one_mul, h, f_nat_mul], },
  },
  have f_one_div : ∀ n : ℕ, n ≠ 0 → f ((1 : ℚ) / n) = (f 1) / n,
  { intros n hn,
    rw [eq_div_iff, mul_comm, ← f_nat_mul _ _, mul_one_div_cancel],
    repeat { rwa nat.cast_ne_zero, } },
    
  intro q,
  rw ← rat.num_div_denom q,
  rcases q with ⟨m, n⟩,
  dsimp,
  rw [div_eq_mul_inv, f_int_mul, inv_eq_one_div, f_one_div, div_eq_mul_one_div],
  ring,
  linarith,
end