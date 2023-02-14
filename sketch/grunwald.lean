import analysis.special_functions.pow
import data.finset.basic
import data.nat.modeq
import data.nat.prime_norm_num
import data.rat.basic
import number_theory.padics.padic_integers
import tactic

open finset nat int padic padic_int
open_locale nat classical

/-
Lemmas for numeric evaluations
-/

lemma Zp_norm_remainder_nat {n p r : ℕ} [hp : fact (nat.prime p)] (h : r % p ≠ 0) :
‖(↑(n * p + r) : ℤ_[p])‖ = 1 :=
begin
  rw [padic_int.norm_def, coe_nat_cast,
      show (↑(n * p + r) : ℚ_[p]) = (↑(↑(n * p + r) : ℚ) : ℚ_[p]), by trivial,
      padic_norm_e.eq_padic_norm, show (1 : ℝ) = ↑(1 : ℚ), by rw algebra_map.coe_one],
  congr,
  rw padic_norm.nat_eq_one_iff,
  by_contradiction h',
  exact h (nat.dvd_iff_mod_eq_zero.1 $ (nat.dvd_add_right $ dvd_mul_left _ _).1 h'),
end

lemma Zp_norm_remainder_int {n r : ℤ} {p : ℕ} [hp : fact (nat.prime p)] (h : r % p ≠ 0) :
‖(↑(n * p + r) : ℤ_[p])‖ = 1 :=
begin
  rw [padic_int.norm_def, coe_int_cast,
      show (↑(n * p + r) : ℚ_[p]) = (↑(↑(n * p + r) : ℚ) : ℚ_[p]), by trivial,
      padic_norm_e.eq_padic_norm, show (1 : ℝ) = ↑(1 : ℚ), by rw algebra_map.coe_one],
  congr,
  rw padic_norm.int_eq_one_iff,
  by_contradiction h',
  exact h ((int.dvd_iff_mod_eq_zero _ _).1 $ (dvd_add_right $ dvd_mul_left ↑p n).1 h'),
end

example {q : ℚ} {k : ℕ} : (↑q ^ (-↑k : ℤ) : ℝ) = ↑(q ^ (-↑k : ℤ) : ℚ) :=
begin
  norm_num,
end

example {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) :=
begin
  show_term { simp [h], },
end

lemma Zp_norm_remainder_Zp {p k : ℕ} [hp : fact (nat.prime p)] {n r : ℤ_[p]}
(h : ↑p ^ (-k : ℤ) < ‖r‖) : ‖n * p ^ k + r‖ = ‖r‖ :=
begin
  rw [padic_int.norm_def, algebra_map.coe_add, algebra_map.coe_mul, algebra_map.coe_pow,
      coe_nat_cast],
  have h' : @padic_norm_e p _ (↑n * ↑p ^ k : ℚ_[p]) ≠ @padic_norm_e p _ ↑r,
  by { sorry, },
  have h'' : @padic_norm_e p _ (↑n * ↑p ^ k : ℚ_[p]) ≤ p ^ (-k : ℤ),
  by { sorry, },
  simp_rw [norm] at *,
  rw [show (↑p ^ (-k : ℤ) : ℝ) = ↑(p ^ (-k : ℤ) : ℚ), by { push_cast, }] at *,
  rw padic_norm_e.add_eq_max_of_ne' h',
  congr,
  rw max_eq_right_iff,
  exact le_of_lt (lt_of_le_of_lt h'' $ rat.cast_lt.1 h),
end

@[simp] lemma Z2_norm_zero : ‖(↑0 : ℤ_[2])‖ = 0 := by rw [algebra_map.coe_zero, norm_zero]

@[simp] lemma Z2_norm_one : ‖(↑1 : ℤ_[2])‖ = 1 := by rw [algebra_map.coe_one, norm_one]

-- @[norm_num] lemma {p : ℕ} [hp : nat.prime p] 
@[simp] lemma Z2_norm_bit0_nat {n : ℕ} (h : 0 < n) : ‖(↑(bit0 n) : ℤ_[2])‖ = ‖(↑n : ℤ_[2])‖ * 2⁻¹ :=
begin
  conv_lhs { simp only [bit0, nat.cast_add], },
  rw [← mul_two, padic_int.norm_mul, show (2 : ℤ_[2]) = ↑(2 : ℕ), by norm_cast, norm_p],
  norm_cast,
end

@[simp] lemma Z2_norm_bit1_nat {n : ℕ} (h : 0 < n) : ‖(↑(bit1 n) : ℤ_[2])‖ = 1 :=
begin
  conv_lhs { rw bit1, simp only [bit0], rw ← mul_two, },
  apply Zp_norm_remainder_nat,
  omega,
end

@[simp] lemma Z2_norm_bit0_int {n : ℤ} (h : 0 ≠ n) : ‖(↑(bit0 n) : ℤ_[2])‖ = ‖(↑n : ℤ_[2])‖ * 2⁻¹ :=
begin
  conv_lhs { simp only [bit0, int.cast_add], },
  rw [← mul_two, padic_int.norm_mul, show (2 : ℤ_[2]) = ↑(2 : ℕ), by norm_cast, norm_p],
  norm_cast,
end

@[simp] lemma Z2_norm_bit1_int {n : ℤ} (h : 0 ≠ n) : ‖(↑(bit1 n) : ℤ_[2])‖ = 1 :=
begin
  conv_lhs { rw bit1, simp only [bit0], rw ← mul_two, },
  apply Zp_norm_remainder_int,
  omega,
end

@[simp] lemma Z2_norm_bit0_Z2 {n : ℤ_[2]} (h : 0 ≠ n) : ‖bit0 n‖ = ‖(↑n : ℤ_[2])‖ * 2⁻¹ :=
begin
  conv_lhs { simp only [bit0, nat.cast_add], },
  rw [← mul_two, padic_int.norm_mul, show (2 : ℤ_[2]) = ↑(2 : ℕ), by norm_cast, norm_p],
  norm_cast,
end

@[simp] lemma Z2_norm_bit1_Z2 {n : ℤ_[2]} (h : 0 ≠ n) : ‖bit1 n‖ = 1 :=
begin
  conv_lhs { rw bit1, simp only [bit0], rw ← mul_two, },
  
end

-- Just proving Wang's counterexamples to Grunwald's wrong result
-- Main tool is to use p-adic valuations to disprove results

-- 16 is not an 8th power over the integers
lemma part1 : ¬∃ n : ℤ, n ^ 8 = 16 :=
begin
  -- suffices : ¬∃ n : ℕ, n ^ 8 = 16,
  -- { contrapose! this,
  --   cases this with n h,
  --   exact ⟨n.nat_abs, by { zify, simpa only [pow_abs, h] }⟩, },
  -- by_contradiction,
  -- cases h with n hn,
  -- by_cases hn' : n = 0,
  -- { rw hn' at hn, linarith, },
  -- have h : padic_val_nat 2 (n ^ 8) = padic_val_nat 2 16,
  -- { rw hn, },
  -- rw [show 16 = 2 ^ 4, by norm_num,
  --     @padic_val_nat.pow _ _ nat.fact_prime_two 4 _, padic_val_nat.self] at h;
  --   try { simp, },
  -- { rw padic_val_nat.pow at h,
  --   have h' : 8 ∣ 8 * padic_val_nat 2 n,
  --   { exact dvd_mul_right _ _, },
  --   norm_num [h] at h',
  --   exact hn', },
  sorry,
end

-- 16 is not an 8th power over Z₂
lemma part2 : ¬∃ n : ℤ_[2], n ^ 8 = 16 :=
begin
  push_neg,
  intro n,
  by_contradiction,
  have : ‖n ^ 8‖ = ‖(16 : ℤ_[2])‖,
  { rw h, },
  rw [Z2_norm_bit0 _] at this,
end