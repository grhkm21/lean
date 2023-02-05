import analysis.normed_space.exponential
import analysis.specific_limits.normed
import analysis.special_functions.exponential
import data.complex.exponential
import probability.probability_mass_function.basic

namespace pmf

noncomputable theory

open nat
open_locale classical big_operators nnreal ennreal

def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : pmf bool :=
⟨λ b, cond b p (1 - p), by simp [summable.has_sum_iff, tsum_bool, add_comm, h]⟩

example (f : ℝ → ℝ) (h : ∀ a, 0 ≤ f a) (h' : summable (λ (a : ℝ), f a)):
∑' (a : ℝ), ennreal.of_real (f a) = ennreal.of_real ∑' (a : ℝ), f a :=
begin
  exact (ennreal.of_real_tsum_of_nonneg h h').symm,
end

example {l : ℝ} : ∑' (n : ℕ), l ^ n / ↑(n.factorial) = real.exp l :=
begin
  rw [real.exp_eq_exp_ℝ, exp_eq_tsum_div],
end

def poisson (l : ℝ) (h : 0 < l) : pmf ℕ :=
⟨ λ k, ennreal.of_real $ (real.exp $ -l) * ((l : ℝ) ^ k) / factorial k,
  by { simp [summable.has_sum_iff],
    rw ← ennreal.of_real_tsum_of_nonneg,
    { rw [show 1 = ennreal.of_real (real.exp (-l) * real.exp l),
          by rw [real.exp_eq_exp_ℝ, ← exp_add, neg_add_self, exp_zero, ennreal.of_real_one]],
      congr,
      suffices : ∑' (n : ℕ), (λ k, l ^ k / ↑(factorial k)) n * real.exp (-l)
                 = real.exp (-l) * real.exp l,
      { rw ← this, congr, funext, ring_nf, },
      rw [mul_comm],
      simp_rw [← smul_eq_mul],
      rw [tsum_smul_const, real.exp_eq_exp_ℝ, exp_eq_tsum_div],
      exact exp_series_div_summable ℝ l, },
    { intro n,
      apply div_nonneg,
      apply mul_nonneg,
      exact le_of_lt (real.exp_pos _),
      exact pow_nonneg (le_of_lt h) n,
      rw ← cast_zero,
      exact cast_le.2 (le_of_lt (factorial_pos n)), },
    { have : summable (λ (n : ℕ), real.exp (-l) • (λ i, l ^ i / ↑(factorial i)) n),
      { apply summable.const_smul, simp [real.summable_pow_div_factorial l], },
      simp at this,
      simp_rw [← mul_div, this], }, }⟩

end pmf