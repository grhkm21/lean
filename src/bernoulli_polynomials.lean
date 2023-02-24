import tactic
import tactic.induction
import number_theory.bernoulli
import number_theory.bernoulli_polynomials

open_locale big_operators
open_locale nat polynomial

open nat finset power_series

namespace polynomial

lemma eq_C_iff_eval_and_derivative_eq_zero {R : Type*} [semiring R] [no_zero_smul_divisors ℕ R] {c : R} {f : R[X]} :
f = C c ↔ (∃ r, f.eval r = c) ∧ f.derivative = 0 :=
begin
  split ; intro h,
  {
    split,
    use 0,
    { rw [h, eval_C] },
    { rw [h, derivative_C] },
  },
  {
    rcases h with ⟨⟨r, hr⟩, h⟩,
    let this := eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_derivative_eq_zero h),
    rw [this, eval_C] at hr,
    rwa hr at this,
  }
end

/-
theorem bernoulli_generating_function (t : A) :
  mk (λ n, aeval t ((1 / n! : ℚ) • bernoulli n)) * (exp A - 1) =
    power_series.X * rescale t (exp A) :=
-/

theorem bernoulli_eval_one_div_two {n : ℕ} :
(bernoulli n).eval (1 / 2) = (2 ^ (1 - n : ℤ) - 1) * _root_.bernoulli n :=
begin
  suffices : mk (λ n, (1 / n! : ℚ) * (bernoulli n).eval (1 / 2))
    = mk (λ n, (1 / n! : ℚ) * (2 ^ (1 - n : ℤ) - 1) * _root_.bernoulli n),
  { let h := (power_series.ext_iff.1 this) n,
    rwa [coeff_mk, coeff_mk] at h, },
  -- line 1
  simp_rw [sub_mul, one_mul],
  simp_rw [show (mk (λ n : ℕ, 2 ^ (1 - n : ℤ) * _root_.bernoulli n - _root_.bernoulli n)
    = mk (λ n, 2 ^ (1 - n : ℤ) * _root_.bernoulli n) - mk _root_.bernoulli), by exact rfl],
  -- line 2
  -- conv_rhs {
    -- congr,congr,funext,rw zpow_sub₀,
  -- },
  simp_rw [@zpow_sub₀ ℚ _ 2 two_ne_zero 1 _, zpow_one],
end

example {f g : ℕ → ℚ} : mk (f - g) = mk f - mk g :=
begin
  exact rfl,
end

theorem bernoulli_eval_one_neg {n : ℕ} {x : ℚ} :
(bernoulli n).eval x = (-1) ^ n * (bernoulli n).eval (1 - x) :=
begin
  -- We prove a more general result that the difference of both sides is 0
  let En := λ n, polynomial.C ((-1) ^ n) * (bernoulli n).comp (1 - (X : ℚ[X])) - bernoulli n,
  suffices : En n = 0,
  { have : eval x (En n) = 0,
    { rw [this, eval_zero] },
    rw [eval_sub, eval_mul, eval_C, sub_eq_zero, eval_comp, eval_sub, eval_one, eval_X] at this,
    exact this.symm, },
  -- We do so by induction
  induction n with k hk ; dsimp only [En],
  { rw [pow_zero, bernoulli_zero, C_1, one_mul, one_comp, sub_self] },
  -- And proving En(0) = 0 and En'(x) = 0
  { rw [← C_0, eq_C_iff_eval_and_derivative_eq_zero],
    split,
    { use 0,
      rw [pow_succ, succ_eq_add_one, eval_sub, eval_mul, eval_comp, eval_C, eval_sub,
          eval_one, eval_X, sub_zero, bernoulli_eval_zero, bernoulli_eval_one,
          bernoulli'_eq_bernoulli, ← pow_succ, ← mul_assoc, ← mul_pow, mul_neg_one, neg_neg,
          one_pow, one_mul, sub_self] },
    { rw [pow_succ, succ_eq_add_one, derivative_sub, derivative_mul, derivative_C, zero_mul, 
          zero_add, derivative_comp, derivative_sub, derivative_one, derivative_X, zero_sub,
          derivative_bernoulli_add_one],
      suffices : (↑k + 1) * (C ((-1) ^ k) * (bernoulli k).comp (1 - X) - bernoulli k) = 0,
      { rw [mul_sub, ← mul_assoc] at this,
        rwa [C_mul, C_neg, C_1, ← mul_assoc, mul_right_comm _ _ (-1 : ℚ[X]), mul_neg_one, neg_neg,
            mul_comp, add_comp, one_comp, nat_cast_comp, ← mul_assoc, one_mul,
            mul_comm _ (k + 1 : ℚ[X])], },
      dsimp only [En] at hk,
      rw [hk, mul_zero] } }
end



end polynomial