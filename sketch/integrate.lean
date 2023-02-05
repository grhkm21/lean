import data.nat.basic
import data.real.basic
import data.list.intervals
import number_theory.von_mangoldt
import measure_theory.integral.interval_integral
import tactic

open real finset measure_theory interval_integral nat.arithmetic_function
open_locale nat big_operators

/-
Exercise 1.1.25
Author: Gareth
-/

lemma aux_div {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) (hm : 1 < m): n / m < n :=
begin
  cases h with k hk,
  have hk' : k ≠ 0,
  { by_contradiction, simp [h] at hk, exact hn hk, },
  have hm' : m ≠ 0,
  { by_contradiction, simp only [h, zero_mul] at hk, exact hn hk, },
  rw [hk, nat.mul_div_cancel_left k (zero_lt_iff.2 hm')],
  conv_lhs { rw ← one_mul k, },
  exact nat.mul_lt_mul_of_pos_right hm (zero_lt_iff.2 hk'),
end

/- Induction on prime powers -/
lemma exists_prime_power_factor {n : ℕ} (h : 2 ≤ n) :
  ∃ p k : ℕ, p.prime ∧ 0 < k ∧ p ^ k ∣ n ∧ ¬p ∣ (n / p ^ k) :=
begin
  have h₀ : n ≠ 0, by linarith,
  have h₁ : n ≠ 1, by linarith,
  use n.min_fac,
  use (n.factorization n.min_fac),
  exact ⟨nat.min_fac_prime h₁,
         nat.prime.factorization_pos_of_dvd (nat.min_fac_prime h₁) h₀ (nat.min_fac_dvd n),
         nat.ord_proj_dvd n _,
         nat.not_dvd_ord_compl (nat.min_fac_prime h₁) h₀⟩,
end

lemma induction_on_prime_powers {P : ℕ → Prop} (p₀ : P 0) (p₁ : P 1)
  (h : ∀ p k a : ℕ, p.prime → ¬p ∣ a → P a → P (p ^ k * a)) (n : ℕ) : P n :=
begin
  induction n using nat.strong_induction_on with n h',
  by_cases h₀ : n = 0, { simp only [h₀, p₀], },
  by_cases h₁ : n = 1, { simp only [h₁, p₁], },
  rcases exists_prime_power_factor (show 2 ≤ n, by omega) with ⟨p, ⟨k, hp, hk, hn, ha⟩⟩,
  specialize h p k (n / p ^ k) hp ha,
  rw [← nat.mul_div_assoc _ hn, nat.mul_div_cancel_left _ (pow_pos (nat.prime.pos hp) k)] at h,
  apply h,
  apply h',
  refine nat.div_lt_self (by omega) _,
  rw ← one_pow k, apply nat.pow_lt_pow_of_lt_left (nat.prime.one_lt hp) hk,
end

/- Auxillary bounds on polynomials and integrals -/
lemma aux_bound1 {x : ℝ} (h : 0 ≤ x) (h' : x ≤ 1) : 0 ≤ x * (1 - x) := mul_nonneg h (by linarith)

lemma aux_bound2 {x : ℝ} (h : 0 ≤ x) (h' : x ≤ 1) : x * (1 - x) ≤ 1 / 4 :=
begin
  calc  x * (1 - x)
      = -(x - 1 / 2) ^ 2 + (1 / 2) ^ 2 : by ring
  ... ≤ 1 / 4                          : by norm_num [sq_nonneg (x - 1 / 2)]
end

lemma aux_bound {x : ℝ} (h : 0 ≤ x) (h' : x ≤ 1) {n : ℕ} : x ^ n * (1 - x) ^ n ≤ 1 / 4 ^ n :=
begin
  rw [← one_pow n]  { occs := occurrences.pos [2] },
  rw [← div_pow, ← mul_pow],
  exact pow_le_pow_of_le_left (aux_bound1 h h') (aux_bound2 h h') n,
end

example {n : ℕ} : interval_integrable (λ x, x ^ n) volume 0 1 :=
continuous.interval_integrable (continuous_pow n) _ _

example {f g : ℝ → ℝ} (h : continuous f) (h' : continuous g) : continuous (f * g) :=
continuous.mul h h'

example {n : ℕ} : ∫ x : ℝ in 0..1, x ^ n * (1 - x) ^ n ≤ 1 / 4 ^ n :=
begin
  rw [show 1 / 4 ^ n = ∫ x : ℝ in 0..1, (1 : ℝ) / 4 ^ n, by simp],
  apply integral_mono_on zero_le_one _ _,
  { intros x hx, cases hx with h h', exact aux_bound h h', },
  apply continuous.interval_integrable,
  continuity,
  simp,
end

lemma nat.Icc_succ_right {n : ℕ} : Icc 1 n.succ = has_insert.insert n.succ (Icc 1 n) :=
begin
  ext,
  simp_rw [mem_insert, mem_Icc],
  rw [show a ≤ n.succ = (a ≤ n ∨ a = n.succ), by rw nat.le_add_one_iff, and_or_distrib_left],
  have : (1 ≤ a ∧ a = n.succ) = (a = n.succ),
  { rw [eq_iff_iff],
    split,
    rintros ⟨h₁, h₂⟩, exact h₂,
    intro h₁,
    simp only [h₁, nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le',
               eq_self_iff_true, and_self], },
  rw [this, or_comm],
end

lemma nat.pow_max {b m n: ℕ} (hb : 0 < b) : b ^ max m n = max (b ^ m) (b ^ n) :=
begin
  by_cases h : m ≤ n,
  { rw [max_eq_right h, max_eq_right (nat.pow_le_pow_of_le_right hb h)], },
  { push_neg at h,
    rw [max_eq_left_of_lt h,
        max_eq_left (nat.pow_le_pow_of_le_right hb (show n ≤ m, by linarith [h]))], },
end

lemma nat.pow_log_succ_upper {b n : ℕ} (h : 1 < b ∧ n ≠ 0) : n < b ^ (nat.log b n + 1) :=
and.right ((nat.log_eq_iff (show _, by { right, exact h })).1 $ refl _)

lemma nat.pow_log_succ_lower {b n : ℕ} (h : 1 < b ∧ n ≠ 0) : b ^ (nat.log b n) ≤ n :=
and.left ((nat.log_eq_iff (show _, by { right, exact h })).1 $ refl _)

lemma nat.pow_log_power_sub_one {p k n : ℕ} (hp : nat.prime p) (hk : k ≠ 0) (hn : n.succ = p ^ k):
nat.log p n = k - 1 :=
begin
  rw nat.log_eq_iff,
  split,
  { apply nat.le_of_lt_succ,
    rw hn,
    apply nat.pow_right_strict_mono (nat.prime.two_le hp),
    exact nat.sub_lt (zero_lt_iff.2 hk) zero_lt_one, },
  { rw [nat.sub_add_cancel (nat.one_le_iff_ne_zero.2 hk), ← hn], exact nat.lt_succ_self n, },
  { right,
    refine ⟨nat.prime.two_le hp, _⟩,
    rw [← nat.succ_ne_succ, hn],
    apply ne_of_gt,
    apply nat.one_lt_pow,
    exact zero_lt_iff.2 hk,
    exact nat.prime.two_le hp, }
end

lemma nat.log_succ {p n : ℕ} (hp : nat.prime p) (hn : 0 < n) :
nat.log p n.succ = max (nat.log p n) (n.succ.factorization p) :=
begin
  rw nat.log_eq_iff,
  { split,
    { rw [nat.pow_max, max_le_iff],
      split,
      exact nat.pow_log_le_add_one _ _,
      exact nat.ord_proj_le _ (nat.succ_ne_zero _),
      exact nat.prime.pos hp, },
    { rw [pow_add, pow_one],
      by_cases h : nat.log p n < n.succ.factorization p,
      -- case 1
      { rw max_eq_right_of_lt h,
        rw [← pow_one p] { occs := occurrences.pos [3] },
        rw [← pow_add],
        -- lemmas
        let h' := nat.pow_log_succ_upper ⟨nat.prime.two_le hp, ne_of_gt hn⟩,
        replace h' := lt_of_lt_of_le h' ((nat.pow_le_iff_le_right $ nat.prime.two_le hp).2 h),
        let h'' := nat.ord_proj_le p (nat.succ_ne_zero n),
        have hn' : n.succ = p ^ (n.succ.factorization p),
        { apply eq.symm,
          by_contradiction hn,
          replace hn := lt_of_lt_of_le h' (nat.lt_succ_iff.1 (lt_iff_le_and_ne.2 ⟨h'', hn⟩)),
          linarith, },
        have hp': n.succ.factorization p ≠ 0,
        { by_contradiction, rw [← nat.succ_sub_one n, hn'] at hn, linarith, },
        -- not important lemma
        have h''' : n.succ ≤ n * p,
        { calc n.succ = n + 1 : by refl
                  ... ≤ n * 2 : by linarith
                  ... ≤ n * p : nat.mul_le_mul_of_nonneg_left (nat.prime.two_le hp) },
        -- important lemma 1
        have lemma1 : nat.log p n + 1 = n.succ.factorization p,
        { replace h := nat.succ_le_iff.2 h,
          rw nat.succ_eq_add_one at h,
          suffices : p ^ (nat.log p n + 1) = p ^ (n.succ.factorization p),
          { apply nat.pow_right_injective (nat.prime.two_le hp), simp only [this], },
          rw [← hn', nat.pow_log_power_sub_one hp hp' hn',
              nat.sub_add_cancel (nat.one_le_iff_ne_zero.2 hp'), ← hn'], },
        -- clean up
        rw [← lemma1, pow_add, pow_one],
        apply lt_of_le_of_lt h''',
        apply nat.mul_lt_mul_of_pos_right _ (nat.prime.pos hp),
        apply nat.pow_log_succ_upper ⟨nat.prime.two_le hp, ne_of_gt hn⟩, },
      { sorry } }, },
  { right, exact ⟨nat.prime.two_le hp, nat.succ_ne_zero n⟩, }
end

lemma nat.lcm_Icc_ne_zero {n : ℕ} : (Icc 1 n).lcm id ≠ 0 :=
begin
  induction n with k hk,
  { rw Icc_eq_empty, simp only [lcm_empty], exact one_ne_zero, linarith, },
  { simp only [hk, id.def, nat.Icc_succ_right, lcm_insert, ne.def, _root_.lcm_eq_zero_iff,
               nat.succ_ne_zero, or_self, not_false_iff], }
end

lemma nat.factorization_lcm_Icc_prime {p n : ℕ} (hp : prime p) (hn : 0 < n) :
nat.factorization ((Icc 1 n).lcm id) p = nat.log p n :=
begin
  induction n with k hk,
  { exfalso, exact (lt_self_iff_false 0).1 hn, },
  induction k with k hk',
  { simp only [Icc_self, lcm_singleton, id.def, normalize_eq, nat.factorization_one,
               finsupp.coe_zero, pi.zero_apply, nat.log_one_right], },
  { rw nat.Icc_succ_right,
    simp only [nat.succ_eq_add_one, add_assoc, one_add_one_eq_two] at *,
    rw finset.lcm_insert,
    specialize hk (nat.cast_add_one_pos k),
    rw [id.def, lcm_eq_nat_lcm, nat.factorization_lcm _ nat.lcm_Icc_ne_zero],
    { rw [finsupp.sup_apply, hk, sup_eq_max], sorry },
    simp only [ne.def, add_eq_zero_iff, two_ne_zero, and_false, not_false_iff], },
end

-- let's not touch this for now...
-- lemma aux_log_lcm_eq_von {n : ℕ} : real.log ↑(finset.Icc 1 n).lcm = von_mangoldt n :=
-- begin
--   induction n using induction_on_prime_powers with p k a hp ha ih,
--   { simp [multiset.Icc], },
--   { simp [multiset.Icc], },
--   {
    
--   }
-- end