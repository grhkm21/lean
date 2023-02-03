import data.nat.basic
import data.real.basic
import data.polynomial.basic
import linear_algebra.basis
import number_theory.liouville.liouville_constant
import tactic

open_locale big_operators
open_locale nat polynomial

open nat finset

-- Slow proof
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

-- Quicker proof
example {f : ℚ → ℚ} (h : ∀ x, ∀ y, f (x + y) = f x + f y) : ∀ x, f x = x * f 1 :=
begin
  -- Setup f as linear_map from ℚ to ℚ
  let f_lin : ℚ →+ ℚ := add_monoid_hom.mk' f h,
  let f_hom : ℚ →ₗ[ℚ] ℚ := add_monoid_hom.to_rat_linear_map f_lin,

  -- The rest is straightforward
  intro x,
  simpa using f_hom.map_smul' x 1,
end

---------------------------------------------------------------------------------------------

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
  },
end

---------------------------------

namespace polynomial

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
      simp [polynomial.aeval, polynomial.eval₂_ring_hom', polynomial.eval₂, polynomial.sum] at h,
      simp [polynomial.aeval, polynomial.eval₂_ring_hom', polynomial.eval₂, polynomial.sum],
      -- Somehow "clear the denominators"
      -- Look at `data.polynomial.denoms_clearable`
    }
  }
end

lemma nice_lemma {q : ℚ} {n : ℤ} (h : n ≠ 0) : (q * n).denom = 1 ↔ ↑q.denom ∣ n :=
begin
  replace hn : (n : ℚ) ≠ 0, by rwa [ne.def, ← int.cast_zero, rat.coe_int_inj],
  split; intros h,
  { rw [← rat.num_div_denom q, div_eq_mul_inv, mul_assoc, mul_comm _ ↑n, ← mul_assoc,
        ← div_eq_mul_inv, ← int.cast_mul, show (q.denom : ℚ) = ↑(q.denom : ℤ), by exact rfl,
        rat.denom_div_cast_eq_one_iff] at h,
    { exact int.dvd_of_dvd_mul_right_of_gcd_one h (coprime.symm q.cop), },
    { norm_cast, exact rat.denom_ne_zero q, }, },
  { rw [← rat.num_div_denom q, div_eq_mul_inv, mul_assoc, mul_comm _ ↑n, ← mul_assoc,
        ← div_eq_mul_inv, ← int.cast_mul, show (q.denom : ℚ) = ↑(q.denom : ℤ), by exact rfl,
        rat.denom_div_cast_eq_one_iff],
    { apply dvd_mul_of_dvd_right h, },
    { norm_cast, exact rat.denom_ne_zero q, }, },
end

lemma nice_lemma' {q : ℚ} {n : ℕ} (h : n ≠ 0) : (q * n).denom = 1 ↔ q.denom ∣ n :=
by exact_mod_cast (@nice_lemma _ n $ by exact_mod_cast h)

lemma denoms_clear (l : list ℚ) : ∃ N : ℕ, N ≠ 0 ∧ ∀ q ∈ l, (q * (N : ℚ)).denom = 1 :=
begin
  induction l with l hl l_ih,
  { use 1, simp, },
  { rcases l_ih with ⟨N, ⟨hN, h⟩⟩,
    { use (N.lcm l.denom),
      split,
      { apply lcm_ne_zero hN (rat.denom_ne_zero l), },
      { intros q h',
        rw list.mem_cons_eq at h',
        change (q * ↑((N : ℕ).lcm l.denom)).denom = 1,
        cases h',
        { rw [h', nice_lemma'],
          { exact nat.dvd_lcm_right _ _, },
          { apply lcm_ne_zero hN (rat.denom_ne_zero l), }, },
        { specialize h q h',
          rw nice_lemma' at *,
          { exact dvd_trans h (nat.dvd_lcm_left _ _), },
          { apply lcm_ne_zero hN (rat.denom_ne_zero l), },
          { exact hN, }, }, }, }, }
end

example {a : ℕ} (h : a ∉ ({0, 2} : finset ℕ)) : a ≠ 0 :=
begin
  by_contradiction h', apply h, simp [h'],
end

example {p : ℚ[X]} (h : p = C (3 / 2) * X ^ 2 + C 1) : p.support = {0, 2} :=
begin
  rw [finset.ext_iff, h],
  intro a,
  rw polynomial.mem_support_iff,
  by_cases h' : a ∈ ({0, 2} : finset ℕ),
  { fin_cases h',
    { simp [C_mul_X_pow_eq_monomial, coeff_monomial], },
    { rw [coeff_add, C_mul_X_pow_eq_monomial, ← monomial_zero_left, coeff_monomial,
          coeff_monomial],
      norm_num, }, },
  { rw [coeff_add, coeff_C, C_mul_X_pow_eq_monomial, coeff_monomial],
    apply iff.symm (iff.trans (iff.trans not_not.symm (not_iff_not_of_iff _)) not_not),
    push_neg,
    rw [iff_true_intro h', true_iff],
    simp [show a ≠ 0, { by_contradiction h'', apply h', simp [h''], },
          (show a ≠ 2, { by_contradiction h'', apply h', simp [h''], }).symm], },
end

example : false :=
begin
  let p : ℚ[X] := (3 / 2) * X + 1,
  let s := p.support,
  let s' := p.to_finsupp.support,
  -- construct 3 * X + 2
  let new_coeff_hom : ℕ →₀ ℚ := {
    support := p.support,
    to_fun := λ n, 2 * p.coeff n,
    mem_support_to_fun := by simp,
  },
  let new_p : ℚ[X] := polynomial.of_finsupp new_coeff_hom,
end

example {x : ℝ} {p : ℚ[X]} (h : polynomial.aeval x p ≠ 0) :
∃ (p' : ℤ[X]), polynomial.aeval x p' ≠ 0 :=
begin
  -- get N
end

end polynomial