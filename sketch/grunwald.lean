import algebra.order.group.with_top
import analysis.special_functions.pow
import data.finset.basic
import data.nat.modeq
import data.nat.prime
import data.nat.prime_norm_num
import data.rat.basic
import number_theory.padics.padic_integers
import tactic

open finset nat int
open_locale nat classical

variables {p : ℕ} [hp : fact (nat.prime p)]
include hp

namespace padic

@[simp] lemma valuation_neg_one : (-1 : ℚ_[p]).valuation = 0 :=
begin
  -- We transfer to `padic.add_valuation`, which is an actual valuation and use their results
  have h : padic.add_valuation (-1 : ℚ_[p]) = padic.add_valuation (1 : ℚ_[p]),
  { exact add_valuation.map_neg padic.add_valuation (1 : ℚ_[p]), },
  rw [padic.add_valuation.apply, padic.add_valuation.apply] at h,
  simp only [with_top.coe_eq_coe.1 h, padic.valuation_one],
  simp only [ne.def, one_ne_zero, not_false_iff],
  simp only [ne.def, neg_eq_zero, one_ne_zero, not_false_iff],
end

@[simp] lemma valuation_neg {n : ℚ_[p]} : (-n).valuation = n.valuation :=
begin
  by_cases h : n = 0,
  { rw [h, neg_zero], },
  { rw [← mul_neg_one, padic.valuation_map_mul h (neg_ne_zero.2 one_ne_zero), valuation_neg_one, 
        add_zero], },
end

end padic

namespace padic_int

theorem coe_inj {n : ℤ_[p]} (h : n ≠ 0) : (n : ℚ_[p]) ≠ 0 := begin
  cases n,
  simp only [subtype.coe_mk, ne.def],
  intro h',
  simp_rw [h', padic_int.mk_zero] at h,
  exact h (eq.refl 0),
end

theorem image {n : ℤ_[p]} : n ≠ 0 → (∃ k : ℕ, ‖n‖ = (↑p ^ -(k : ℤ))) :=
begin
  intro hn,
  cases @padic_norm_e.image' p _ ↑n (coe_inj hn) with k hk,
  have k_nonneg : 0 ≤ k,
  { sorry, },
  use k.to_nat,
  rw [to_nat_of_nonneg k_nonneg, norm_def, ← rat.cast_coe_nat, ← rat.cast_zpow, ← hk,
      padic_norm_e.is_norm],
end

@[simp] theorem valuation_neg {n : ℤ_[p]} : (-n).valuation = n.valuation := padic.valuation_neg

theorem valuation_map_add {m n : ℤ_[p]} (hmn : m + n ≠ 0) :
min m.valuation n.valuation ≤ (m + n).valuation :=
begin
  apply padic.valuation_map_add,
  rwa [← coe_add, ne.def, coe_eq_zero],
end

theorem norm_add_eq_max_of_ne' {q r : ℤ_[p]} (h : ‖q‖ < ‖r‖) : ‖q + r‖ = ‖r‖ :=
begin
rw [norm_add_eq_max_of_ne (ne_of_lt h), max_eq_right_iff.2 (le_of_lt h)],
end

theorem valuation_p_pow_mul_add (n : ℕ) (c r : ℤ_[p]) (hn : 0 < n) (hc : c ≠ 0) (hr : r ≠ 0)
(h : r.valuation < n) : (↑p ^ n * c + r).valuation = r.valuation :=
begin
  let hp : nat.prime p := fact_iff.1 hp,
  suffices : ‖↑p ^ n * c + r‖ = ‖r‖,
  { rwa [norm_eq_pow_val, norm_eq_pow_val hr, zpow_inj, neg_inj] at this;
    simp only [nat.cast_pos, ne.def, zpow_neg, inv_inj] at *,
    -- Just fixing all the ... ≠ 0 requirements
    { exact prime.pos hp, },
    { by_contradiction hp',
      rw [← nat.cast_one, nat.cast_inj] at hp',
      exact nat.prime.ne_one hp hp', },
    { by_contradiction,
      rw add_eq_zero_iff_eq_neg at h,
      have h' : ↑n + c.valuation = r.valuation,
      { rwa [← valuation_p_pow_mul, ← @valuation_neg p _ r, h], },
      have : ↑n ≤ r.valuation,
      { rw [← h'], exact int.le_add_of_nonneg_right (valuation_nonneg _), },
      linarith, }, },
  apply norm_add_eq_max_of_ne',
  cases @image p _ c hc with k hk,
  rw [norm_mul, norm_p_pow, norm_eq_pow_val hr, hk, ← zpow_add'],
  { sorry, },
  { left, rw [ne.def, nat.cast_eq_zero], exact nat.prime.ne_zero hp, },
end

end padic_int

-- Just proving Wang's counterexamples to Grunwald's wrong result
-- Main tool is to use p-adic valuations to disprove results

-- 16 is not an 8th power over the integers
lemma part1 : ¬∃ n : ℤ, n ^ 8 = 16 :=
begin
  suffices : ¬∃ n : ℕ, n ^ 8 = 16,
  { contrapose! this,
    cases this with n h,
    exact ⟨n.nat_abs, by { zify, simpa only [pow_abs, h] }⟩, },
  by_contradiction,
  cases h with n hn,
  by_cases hn' : n = 0,
  { rw hn' at hn, linarith, },
  have h : padic_val_nat 2 (n ^ 8) = padic_val_nat 2 16,
  { rw hn, },
  rw [show 16 = 2 ^ 4, by norm_num,
      @padic_val_nat.pow _ _ nat.fact_prime_two 4 _, padic_val_nat.self] at h;
    try { simp, },
  { rw padic_val_nat.pow at h,
    have h' : 8 ∣ 8 * padic_val_nat 2 n,
    { exact dvd_mul_right _ _, },
    norm_num [h] at h',
    exact hn', },
end

-- 16 is not an 8th power over Z₂
lemma part2 : ¬∃ n : ℤ_[2], n ^ 8 = 16 :=
begin
  push_neg,
  intro n,
  by_contradiction,
  have : (n ^ 8).valuation = (2 ^ 4 : ℤ_[2]).valuation,
  { norm_num, rw h, },
  
end