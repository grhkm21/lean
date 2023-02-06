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

lemma aux_integral_bound {n : ℕ} : ∫ x : ℝ in 0..1, x ^ n * (1 - x) ^ n ≤ 1 / 4 ^ n :=
begin
  rw [show 1 / 4 ^ n = ∫ x : ℝ in 0..1, (1 : ℝ) / 4 ^ n, by simp],
  apply integral_mono_on zero_le_one _ _,
  { intros x hx, cases hx with h h', exact aux_bound h h', },
  apply continuous.interval_integrable,
  continuity,
  simp,
end

lemma multiset.map_ite {P : Prop} [decidable P] {f : ℕ → ℝ} {s s₁ s₂ : multiset ℕ} :
multiset.map f (ite P s₁ s₂) = ite P (multiset.map f s₁) (multiset.map f s₂) :=
by { by_cases P ; simp [h] }

lemma multiset.sum_add_sub_map {s : multiset ℕ} (f g : ℕ → ℝ) :
(multiset.map f s).sum = (multiset.map g s).sum + (multiset.map (f - g) s).sum :=
begin
  simp only [pi.sub_apply, multiset.sum_map_sub], ring,
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

lemma nat.succ_not_mem_Icc (m n : ℕ) : n.succ ∉ Icc m n := by { rw [mem_Icc, not_and, not_le], intro h, exact nat.lt_succ_self n }

lemma nat.pow_max {b m n: ℕ} (hb : 0 < b) : b ^ max m n = max (b ^ m) (b ^ n) :=
begin
  by_cases h : m ≤ n,
  { rw [max_eq_right h, max_eq_right (nat.pow_le_pow_of_le_right hb h)], },
  { push_neg at h,
    rw [max_eq_left_of_lt h,
        max_eq_left (nat.pow_le_pow_of_le_right hb (show n ≤ m, by linarith [h]))], },
end

-- lower bound: `nat.lt_pow_succ_log_self`
lemma nat.pow_log_self_le_self {b n : ℕ} (h : 1 < b ∧ n ≠ 0) : b ^ (nat.log b n) ≤ n :=
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

-- TODO: Generalise these for non-primes
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
      -- case 1, hard case
      { rw max_eq_right_of_lt h,
        rw [← pow_one p] { occs := occurrences.pos [3] },
        rw [← pow_add],
        -- lemmas
        let h' := nat.lt_pow_succ_log_self (nat.prime.two_le hp) n,
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
        apply nat.lt_pow_succ_log_self (nat.prime.two_le hp) n, },
      -- case 2, easy case
      { push_neg at h,
        rw max_eq_left h,
        rw [← pow_one p] { occs := occurrences.pos [3] },
        rw [← pow_add],
        let h' := nat.lt_pow_succ_log_self (nat.prime.two_le hp) n,
        rw [← nat.succ_le_iff, le_iff_lt_or_eq] at h',
        cases h',
        { exact h' },
        -- somehow i broke this
        { sorry }, } }, },
  { right, exact ⟨nat.prime.two_le hp, nat.succ_ne_zero n⟩, }
end

lemma nat.log_succ_ne_log_self {p n : ℕ} (hp : nat.prime p) (hn : 0 < n) :
nat.log p n.succ ≠ nat.log p n ↔ n.succ = p ^ (n.succ.factorization p) :=
begin
  split,
  { rw nat.log_succ hp hn,
    intro h,
    simp only [ne.def, max_eq_left_iff, not_le, nat.lt_iff_add_one_le] at h,
    let h₁ := nat.pow_le_pow_of_le_right (nat.prime.pos hp) h,
    let h₃ := nat.ord_proj_le p (nat.succ_ne_zero n),
    let h₄ := nat.lt_iff_add_one_le.1 (nat.lt_pow_succ_log_self (nat.prime.two_le hp) n),
    let h₅ := le_trans h₄ h₁,
    exact omega.nat.le_and_le_iff_eq.1 ⟨h₅, h₃⟩, },
  { intro h,
    by_contradiction h',
    rw [h, nat.log_pow (nat.prime.two_le hp)] at h',
    let h'' := nat.pow_log_le_self p (ne_of_gt hn),
    rw [← h', ← h] at h'',
    exact (nat.not_succ_le_self n) h'', }
end

lemma nat.lcm_Icc_ne_zero {n : ℕ} : (Icc 1 n).lcm id ≠ 0 :=
begin
  induction n with k hk,
  { rw Icc_eq_empty, simp only [lcm_empty], exact one_ne_zero, linarith, },
  { simp only [hk, id.def, nat.Icc_succ_right, lcm_insert, ne.def, _root_.lcm_eq_zero_iff,
               nat.succ_ne_zero, or_self, not_false_iff], }
end

lemma nat.factorization_lcm_Icc_prime {p n : ℕ} (hp : nat.prime p) (hn : 0 < n) :
nat.factorization ((Icc 1 n).lcm id) p = nat.log p n :=
begin
  let P := λ n, nat.factorization ((Icc 1 n).lcm id) p = nat.log p n,
  have hP₁ : P 1,
  { norm_num [P, Icc_self 1, lcm_singleton], },
  apply nat.le_induction hP₁ _ n,
  { apply hn, },
  { dsimp [P],
    intros n hn hP,
    rw nat.Icc_succ_right,
    simp only [nat.succ_eq_add_one, add_assoc, one_add_one_eq_two] at *,
    rw [lcm_insert, id.def, lcm_eq_nat_lcm, nat.factorization_lcm (nat.succ_ne_zero n)
        nat.lcm_Icc_ne_zero, finsupp.sup_apply, hP, sup_eq_max, nat.log_succ hp hn, max_comm], },
end

lemma nat.prime_dvd_lcm_Icc {p n : ℕ} (hp : nat.prime p) (hn : 0 < n) :
p ∣ (Icc 1 n).lcm id ↔ p ≤ n :=
begin
  rw [nat.prime.dvd_iff_one_le_factorization hp nat.lcm_Icc_ne_zero,
      nat.factorization_lcm_Icc_prime hp hn,
      ← nat.pow_le_iff_le_log (nat.prime.two_le hp) (ne_of_gt hn), pow_one],
end

lemma nat.lcm_Icc_factorization_support_eq_primes_le {n : ℕ} (hn : 0 < n) :
((Icc 1 n).lcm id).factorization.support = (filter nat.prime (Icc 1 n)) :=
begin
  ext,
  rw [nat.factor_iff_mem_factorization, nat.mem_factors nat.lcm_Icc_ne_zero, mem_filter],
  split ; rintros ⟨ha, ha'⟩,
  { simp only [mem_Icc],
    exact ⟨⟨by linarith [nat.prime.two_le ha], (nat.prime_dvd_lcm_Icc ha hn).1 ha'⟩, ha⟩, },
  { exact ⟨ha', (nat.prime_dvd_lcm_Icc ha' hn).2 (mem_Icc.1 ha).2⟩, },
end

lemma nat.factorization_lcm_Icc_sum {n : ℕ} {f : ℕ → ℕ → ℝ} (hn : 0 < n):
(nat.factorization ((Icc 1 n).lcm id)).sum f
  = (filter nat.prime (Icc 1 n)).sum (λ p, f p (nat.log p n)) :=
begin
  rwa [finsupp.sum, nat.lcm_Icc_factorization_support_eq_primes_le hn, finset.sum_congr],
  refl,
  intros a ha,
  rw mem_filter at ha,
  congr,
  exact nat.factorization_lcm_Icc_prime ha.right hn,
end

lemma aux_log_lcm_eq_sum_von {n : ℕ} (hn : 0 < n) :
real.log ↑((Icc 1 n).lcm id) = (Icc 1 n).sum von_mangoldt :=
begin
  -- manipulation
  -- rw [real.log_nat_eq_sum_factorization, nat.factorization_lcm_Icc_sum hn],
  -- dsimp [von_mangoldt],
  -- simp_rw [← sum_filter, ← nsmul_eq_mul],
  -- simp only [sum_eq_multiset_sum, filter_val, ← multiset.Icc],
  -- we consider taking difference of P(n + 1) - P(n)

  -- Everything after isn't really working
  let P := λ n, (multiset.map (λ (x : ℕ), nat.log x n • real.log ↑x) (multiset.filter nat.prime (Icc 1 n).val)).sum - (multiset.map (λ (x : ℕ), real.log ↑(x.min_fac)) (multiset.filter is_prime_pow (Icc 1 n).val)).sum = 0,

  suffices : P n, { sorry },

  have P₁ : P 1,
  -- { simp_rw P,
  --   simp only [Icc_self 1, singleton_val, multiset.filter_singleton],
  --   norm_num [not_is_prime_pow_one], },
  sorry,

  apply nat.le_induction P₁ _ n,
  apply hn,
  { intros n hn' Pₙ,
    simp_rw P,
    -- mess with prime map
    simp_rw [nat.Icc_succ_right, insert_val_of_not_mem (nat.succ_not_mem_Icc 1 n),
             multiset.filter_cons, multiset.map_add, multiset.sum_add, ← sub_sub],
    rw [multiset.map_ite, multiset.map_ite],
    simp_rw [multiset.map_zero, multiset.map_singleton],
    rw multiset.sum_add_sub_map (λ x : ℕ, nat.log x (n + 1) • real.log x)
                                (λ x : ℕ, nat.log x n • real.log x),
    rw [← add_assoc, sub_sub],
    rw [add_comm] { occs := occurrences.pos [1] },
    -- mess with is_prime_pow map
    rw add_sub_right_comm,
    rw ← add_sub,
    simp only [P n],
  }
  rw ← sum_multiset_count,
end

example {a b c : ℝ} : a + b - c = b - c + a := by rw [← add_sub, add_comm a (b - c)]