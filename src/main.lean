/-
TODO: Add copyright information
TODO: Add proper documentations
TODO: Decide where to put this file
-/

import algebra.geom_sum
import data.finset.basic
import data.nat.prime
import number_theory.arithmetic_function
import number_theory.divisors
import number_theory.lucas_lehmer
import tactic

namespace nat

open finset
open nat.arithmetic_function
open_locale arithmetic_function
open_locale big_operators

variable X : ℤ

/-
Below are results leading up to Euclid-Euler Theorem
-/

-- Thank you to Kevin Buzzard, Niels Voss and Yaël Dillies for helping with this!
theorem mersenne_div {m n : ℕ} (h : m ∣ n) : mersenne m ∣ mersenne n :=
begin
  rcases h with ⟨k, rfl⟩,
  simpa only [mersenne, pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 _,
end

-- 2^n - 1 is Mersenne prime implies n is prime
theorem mersenne_theorem {n : ℕ} (h : nat.prime (mersenne n)) : nat.prime n :=
begin
  -- Auxillary lemma
  have two_le_n : 2 ≤ n,
  {
    by_contradiction h',
    push_neg at h',

    -- TODO: Simplify this, seems repetitive
    cases nat.lt_succ_iff.1 h' with _ h',
    { simp [mersenne, nat.not_prime_one] at h, exact h, },
    { simp [mersenne, nat.eq_zero_of_le_zero h', nat.not_prime_zero] at h, exact h, }
  },

  -- Assume n is composite
  by_contradiction n_comp,
  rcases nat.exists_dvd_of_not_prime _ n_comp with ⟨d, d_div, d_ne_one, d_ne_n⟩,

  -- TODO: Remove these...
  have d_ne_zero : d ≠ 0,
  { by_contradiction, rw h at d_div, rw zero_dvd_iff at d_div, linarith, },
  have one_le_pow_two_d : 1 ≤ 2 ^ d,
  { apply nat.one_le_pow, omega, },
  have two_le_d : 2 ≤ d,
  { cases d, omega, cases d; omega,},
  have four_sub_one_le_pow_two_sub_one: 4 - 1 ≤ 2 ^ d - 1,
  {
    change 2 ^ 2 - 1 ≤ 2 ^ d - 1,
    rw nat.sub_le_sub_iff_right,
    exact pow_le_pow (by linarith) two_le_d,
    exact nat.one_le_pow d 2 zero_lt_two,
  },

  -- Then mersenne n is not prime
  rcases mersenne_div d_div with ⟨md, hmd⟩,
  have : ¬nat.prime (mersenne n),
  {
    apply nat.not_prime_mul' hmd.symm,
    {
      unfold mersenne,

      -- TODO: Remove this...
      calc
      1 < 4 - 1 : by simp
      ... ≤ 2 ^ d - 1 : by { simp [four_sub_one_le_pow_two_sub_one] },
    },
    {
      -- Ruling out cases where (mersenne n / mersenne d) <= 2
      by_contradiction H,
      push_neg at H,
      cases md,
      { simp [hmd] at h, exact nat.not_prime_zero h, },
      {
        unfold mersenne at hmd,
        rw [nat.succ_le_iff, nat.lt_one_iff] at H,
        simp [H] at hmd,
        -- TODO: Here I am proving 2 ^ n - 1 = 2 ^ d - 1 => n = d ... Is there better way?
        rw [tsub_left_inj (nat.one_le_pow n 2 zero_lt_two) one_le_pow_two_d, eq_comm] at hmd,
        exact d_ne_n (nat.pow_right_injective rfl.ge hmd),
      }
    }
  },

  exact this h,
  exact two_le_n,
end

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 :=
begin
  simp [sigma_one_apply, nat.prime_two, ← geom_sum_mul_add 1 (k+1)],
end

-- Euclid-Euler Theorem
theorem euclid_euler {n : ℕ} :
nat.perfect n ∧ even n ↔
(∃ (p : ℕ), nat.prime (2 ^ p - 1) ∧ n = 2 ^ (p - 1) * (2 ^ p - 1)) :=
begin
  split,

  -- If n is perfect and even, then
  -- n = 2^(p - 1) (2^p - 1) and (2^p - 1) is prime
  {
    contrapose!,
    intro h,
    contrapose!,
    intro n_even,
    sorry
  },
  {
    -- If (2^p - 1) is prime, then n = 2^(p - 1) (2^p - 1) is perfect and even
    rintros ⟨p, hp, hn⟩,
    let n₁ := 2 ^ (p - 1),
    let n₂ := 2 ^ p - 1,
    have n₂_pos : 1 ≤ 2 ^ p, { exact nat.one_le_two_pow p, },
    have hpr : nat.prime p, { exact mersenne_theorem hp, },

    split,
    {
      have h₂ : n₁.coprime n₂, { sorry },
      have h : σ 1 n = σ 1 n₁ * σ 1 n₂,
      { rw [hn, is_multiplicative.map_mul_of_coprime is_multiplicative_sigma h₂], },
      have hσ₁ : ∀ (n : ℕ), σ 1 (2 ^ n) = 2 ^ (n + 1) - 1,
      {
        intro n,
        simp [sigma_one_apply, nat.prime_two, ← geom_sum_mul_add 1 (n + 1)],
      },
      have hσ₂ : ∀ (p : ℕ), nat.prime p → σ 1 p = 1 + p,
      {
        intros p hpr,
        simp [sigma_one_apply, hpr, add_comm],
      },
      rw nat.perfect_iff_sum_divisors_eq_two_mul,

      -- I plan to make evaluating arithmetic functions easier
      rw [← sigma_one_apply, h, hσ₁ (p - 1), nat.sub_add_cancel (nat.prime.pos hpr)],
      simp [hσ₂ n₂ hp, n₂, ← nat.add_sub_assoc n₂_pos, hn, ← nat.pow_div (nat.prime.pos hpr)],
      rw [← nat.mul_assoc, nat.mul_div_cancel', mul_comm],
      apply nat.dvd_of_pow_dvd (nat.prime.pos hpr) (dvd_refl _),

      -- Prove n > 0
      simp [hn],
      apply nat.le_self_pow (nat.prime.ne_zero hpr) 2,
    },
    {
      -- If (2^p - 1) is prime, then n = 2^(p - 1) (2^p - 1) is even
      simp [hn, n₁, n₂] with parity_simps,
      left,
      exact nat.prime.two_le hpr,
    },
  },
end

end nat