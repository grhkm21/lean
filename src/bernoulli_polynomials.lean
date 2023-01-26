import tactic
import tactic.induction
import number_theory.bernoulli
import number_theory.bernoulli_polynomials

open_locale big_operators
open_locale nat polynomial

open nat finset

namespace polynomial

lemma lemma1 {R : Type*} [semiring R] [no_zero_smul_divisors ℕ R] {f : R[X]} :
f = 0 ↔ f.eval 0 = 0 ∧ f.derivative = 0 :=
begin
  split ; intro h,
  {
    rw [h, eval_zero, derivative_zero],
    split ; refl,
  },
  {
    cases h with h₀ h₁,
    rw [← C_0, ← h₀, ← coeff_zero_eq_eval_zero],
    apply eq_C_of_derivative_eq_zero h₁,
  }
end

theorem real_theorem {n : ℕ} {x : ℚ} :
(bernoulli n).eval x = (-1) ^ n * (bernoulli n).eval (1 - x) :=
begin
  -- We prove a more general result that the difference of both sides is 0
  let En := λ n, polynomial.C ((-1) ^ n) * (bernoulli n).comp (1 - (X : ℚ[X])) - bernoulli n,
  suffices : En n = 0,
  {
    have : eval x (En n) = 0,
    { rw [this, eval_zero], },
    rw [eval_sub, eval_mul, eval_C, sub_eq_zero, eval_comp, eval_sub, eval_one, eval_X] at this,
    exact this.symm,
  },
  -- We do so by induction
  induction n with k hk ; dsimp only [En],
  { rw [pow_zero, bernoulli_zero, C_1, one_mul, one_comp, sub_self], },
  {
    -- And proving En(0) = 0 and En'(x) = 0
    rw lemma1,
    split,
    {
      rw [pow_succ, succ_eq_add_one, eval_sub, eval_mul, eval_comp, eval_C, eval_sub,
          eval_one, eval_X, sub_zero, bernoulli_eval_zero, bernoulli_eval_one,
          bernoulli'_eq_bernoulli, ← pow_succ, ← mul_assoc, ← mul_pow, mul_neg_one, neg_neg,
          one_pow, one_mul, sub_self],
    },
    {
      rw [pow_succ, succ_eq_add_one, derivative_sub, derivative_mul, derivative_C, zero_mul, 
      zero_add, derivative_comp, derivative_sub, derivative_one, derivative_X, zero_sub,
      derivative_bernoulli_add_one],
      suffices : (↑k + 1) * (C ((-1) ^ k) * (bernoulli k).comp (1 - X) - bernoulli k) = 0,
      {
        rw [mul_sub, ← mul_assoc] at this,
        rwa [C_mul, C_neg, C_1, ← mul_assoc, mul_right_comm _ _ (-1 : ℚ[X]), mul_neg_one, neg_neg,
            mul_comp, add_comp, one_comp, nat_cast_comp, ← mul_assoc, one_mul,
            mul_comm _ (k + 1 : ℚ[X])],
      },
      dsimp only [En] at hk,
      rw [hk, mul_zero],
    }
  }
end

end polynomial