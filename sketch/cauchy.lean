import data.nat.basic
import data.real.basic
import data.polynomial.basic
import linear_algebra.basis
import number_theory.liouville.liouville_constant
import tactic

open_locale big_operators
open_locale nat polynomial

open nat finset

example {f : ℚ → ℚ} (h : ∀ x, ∀ y, f (x + y) = f x + f y) : ∀ x, f x = x * f 1 :=
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

example : ∃ f : ℝ → ℝ, (∀ x y, f (x + y) = f x + f y) ∧ (∃ x : ℝ, f x ≠ x * f 1) :=
begin
  let real_basis := basis.of_vector_space ℚ ℝ,
  let real_index_set : set ℝ := basis.of_vector_space_index ℚ ℝ,

  -- we prove that the set is nonempty
  have real_index_set_nonempty : real_index_set.nonempty,
  { rw ← set.nonempty_coe_sort, exact real_basis.index_nonempty, },
  let real_basis_vec₁ := set.nonempty.some real_index_set_nonempty,

  -- we prove that the set is infinite
  have real_index_set_infinite : real_index_set.infinite,
  { sorry, },
  
  -- then we can choose some basis vectors
  let real_index_nat_embedding := set.infinite.nat_embedding real_index_set real_index_set_infinite,
  let real_basis_vec₀ := real_index_nat_embedding 0,
  let real_basis_vec₁ := real_index_nat_embedding 1,

  -- they are not equal
  have real_basis_vec₀_ne_real_basis_vec₁: real_basis_vec₀ ≠ real_basis_vec₁,
  {
    by_contradiction,
    linarith [real_index_nat_embedding.injective h],
  },

  let f_map : real_index_set → ℝ := λ index,
  if index = real_basis_vec₀
  then
    real_basis real_basis_vec₁
  else
    real_basis real_basis_vec₀,

  let f : ℝ → ℝ := real_basis.constr ℝ f_map,

  -- now we verify that the two basis vectors map to different values
  let x₀ : ℝ := real_basis real_basis_vec₀,
  let x₁ : ℝ := real_basis real_basis_vec₁,
  have : f x₀ ≠ f x₁,
  {
    simp only [f, x₀, x₁],
    dsimp [basis.constr],
    -- simp only [f, basis.constr, x₀, x₁],
    simp only [basis.repr_self, finsupp.map_domain_single, finsupp.total_single, one_smul, id,
               f_map],
    simp [set_coe.ext_iff],
  }
end

---------------------------------

example : true :=
begin
  -- We construct a transcendental (over Q) number x
  let x : ℝ := liouville.liouville_number 3,

  -- Then construct the set {1, x, x^2, ...}
  let ι := ℕ,
  let v : ι → ℝ := λ n, x ^ n,
  
  -- Then prove it is linearly independent over Q
  have : linear_independent ℚ v,
  {
    let h := liouville.is_transcendental (show 2 ≤ 3, by omega),
    simp only [transcendental, is_algebraic] at h,
    push_neg at h,
    rw linear_independent_iff,
    intro l,
    simp [finsupp.total, v],
    have h' : ∀ (p : ℚ[X]), p ≠ 0 → (polynomial.aeval (liouville.liouville_number ↑3)) p ≠ 0,
    {
      intros p hp,
      -- Somehow "clear the denominators"
      -- Look at `data.polynomial.denoms_clearable`
    }
  }
end


