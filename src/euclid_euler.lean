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

/-
Below are results leading up to Euclid-Euler Theorem
-/

open finset
open nat.arithmetic_function
open_locale arithmetic_function
open_locale big_operators

-- Lemma that allows us to cast mersenne numbers to integers
lemma coe_mersenne {n : ℕ} : (mersenne n : ℤ) = (2 : ℤ) ^ n - 1 :=
begin
  simp [mersenne],
end

lemma mersenne_inc {m n : ℕ} (h : m < n) : mersenne m < mersenne n :=
begin
  suffices : (mersenne m : ℤ) < mersenne n,
  { exact_mod_cast this, },
  simp [coe_mersenne],
  exact pow_lt_pow one_lt_two h,
end

-- Thank you to Kevin Buzzard, Niels Voss and Yaël Dillies for helping with this!
lemma mersenne_div {m n : ℕ} (h : m ∣ n) : mersenne m ∣ mersenne n :=
begin
  rcases h with ⟨k, rfl⟩,
  simpa only [mersenne, pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 _,
end

-- set_option pp.all true

-- 2^n - 1 is Mersenne prime implies n is prime
theorem mersenne_theorem {n : ℕ} (h : nat.prime (mersenne n)) : nat.prime n :=
begin
  -- Auxillary lemma
  have two_le_n : 2 ≤ n,
  {
    by_contradiction h',
    push_neg at h',

    cases nat.lt_succ_iff.1 h' with _ h',
    { simp [mersenne, nat.not_prime_one] at h, exact h, },
    { simp [mersenne, nat.eq_zero_of_le_zero h', nat.not_prime_zero] at h, exact h, }
  },

  -- Assume n is composite
  by_contradiction n_comp,
  rcases nat.exists_dvd_of_not_prime two_le_n n_comp with ⟨d, d_dvd, d_ne_one, d_ne_n⟩,

  have d_pos : 0 < d,
  { by_contradiction, simp at h, rw h at d_dvd, rw zero_dvd_iff at d_dvd, linarith, },
  have two_le_d : 2 ≤ d,
  { cases d, omega, cases d; omega,},

  -- Then mersenne n is not prime
  rcases mersenne_div d_dvd with ⟨md, hmd⟩,
  suffices : ¬nat.prime (mersenne n),
  { exact this h, },

  -- We cast to int for easier life
  apply nat.not_prime_mul' hmd.symm,
  {
    have : (2 : ℤ) ^ 1 < 2 ^ d,
    { exact pow_lt_pow one_lt_two two_le_d, },
    have : (1 : ℤ) < (mersenne d : ℤ),
    { simp [coe_mersenne], linarith, },
    exact_mod_cast this,
  },
  {
    have : mersenne d < mersenne n,
    { apply mersenne_inc, exact lt_iff_le_and_ne.2 ⟨nat.le_of_dvd (by linarith) d_dvd, d_ne_n⟩, },
    simp [hmd] at this,
    exact (lt_mul_iff_one_lt_right (mersenne_pos d_pos)).1 this,
  }
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