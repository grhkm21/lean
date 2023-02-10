import analysis.special_functions.integrals
import data.nat.basic
import data.nat.prime
import data.nat.prime_norm_num
import data.real.basic
import data.matrix.basic
import measure_theory.measure.measure_space
import measure_theory.integral.interval_integral
import number_theory.bernoulli
import number_theory.bernoulli_polynomials
import number_theory.von_mangoldt
import number_theory.well_approximable
import probability.probability_mass_function.basic
import tactic

open nat real ennreal finset measure_theory interval_integral nat.arithmetic_function
open_locale nat ennreal interval measure_theory polynomial big_operators arithmetic_function

example {a b : ℕ} (h : a < b) : a + 1 ≤ b :=
begin
  library_search!,
end

example : ¬ nat.prime 0 :=
begin
  exact nat.not_prime_zero,
end

example : nat.prime 17 :=
begin
  norm_num,
end

namespace polynomial

example {Y : ℚ[X]} : (Y + 1).aeval ((X : ℚ[X]) ^ 2) = Y ^ 2 + 2 * Y + 1 :=
begin
  simp,
  ring_nf,
end

example {x : ℚ} : eval x (1 - (X : ℚ[X])) = 1 - x :=
begin
  rw [eval_sub, eval_one, eval_X],
end

example {x : ℚ} {n : ℕ}: eval x ((-1 : ℚ[X])^n) = (-1) ^ n :=
begin
  show_term {simp,},
end
  
example {n : ℕ} : ((-1 : ℤ) ^ n) * ((-1) ^ n) = 1 :=
begin
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow],
end

example {n : ℚ} : n - n = 0 :=
begin
  library_search!,
end

-- f(g(x))
example {f g : ℚ[X]} : aeval g f = f.comp g :=
begin
  simp [aeval, comp, eval₂_ring_hom'],
  exact rfl,
end

example {f g : ℚ[X]} : aeval g f = f.comp g :=
begin
  exact rfl,
end

example {f g : ℚ[X]} : (aeval g f).derivative = (aeval g f.derivative) * g.derivative :=
begin
  change (f.comp g).derivative = f.derivative.comp g * g.derivative,
  rw [derivative_comp, mul_comm],
end

example {a b c d : ℚ[X]} : a * b * (c * d) = a * b * c * d :=
begin
  ring,
end

example {A B C D : Type} (f : A → B → C → D) (g : A → B) (x : A) (z : C) : D :=
begin
  exact f x (g x) z,
end

example {n : ℕ} {q : ℚ} : (-1) ^ n * (bernoulli n).eval 0 = (bernoulli n).eval 1 :=
begin
  simp, -- (-1) ^ n * bernoulli n = bernoulli' n, but as numbers, not polynomials
  rw [_root_.bernoulli, ← mul_assoc, ← mul_pow, mul_neg_one, neg_neg, one_pow, one_mul],
end

example {a b c : ℚ[X]} : a * b * c = b * a * c :=
begin
  show_term {simp},
end

example {n : ℕ} : n = (2 ^ 2000) + 1 :=
begin
  norm_num,
end

example {q : ℚ} : q = q.num * (1 / q.denom) :=
begin
  rcases q with ⟨m, n, n_pos, mn_coprime⟩,
  simp,
  rw [eq_comm, mul_inv_eq_iff_eq_mul₀, rat.mul_denom_eq_num],
  -- hint,
end

example {α : Type*} {x y : α} : x = y ↔ y = x :=
begin
  library_search!,
end

example {x y : ℚ} (h : -x = -y) : x = y :=
begin
  library_search!,
end

example : true :=
begin
  let real_basis := basis.of_vector_space ℚ ℝ,
  let real_index_set : set ℝ := basis.of_vector_space_index ℚ ℝ,

  -- we prove that the set is nonempty
  have real_index_set_nonempty : real_index_set.nonempty,
  { rw ← set.nonempty_coe_sort, exact real_basis.index_nonempty, },
  let real_basis_vec₁ := set.nonempty.some real_index_set_nonempty,

  -- we prove that the set is infinite
  have real_index_set_infinite : real_index_set.infinite,
  {
    -- TODO: Add proof by showing that for a transcendental x,
    -- 1, x, x^2, ... are linearly independent, so any basis is infinite
    sorry,
  },
  
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

  let f_map : real_index_set → ℝ := λ index, real_basis_vec₁,
  let f := real_basis.constr ℝ f_map,

  -- verifies cauchy's
  have : ∀ x y, f (x + y) = f x + f y,
  { intros x y, apply f.map_add', },
  
  -- verifies non-linear
  let x₀ : ℝ := real_basis real_basis_vec₀,
  let x₁ : ℝ := real_basis real_basis_vec₁,
  have : ∃ x, f x ≠ x * f 1,
  {
    by_contradiction,
    push_neg at h,
    have h₀ := h x₀,
    have h₁ := h x₁,
    conv_lhs at h₀ { simp only [f, x₀, basis.constr_basis, f_map] },
    conv_lhs at h₁ { simp only [f, x₀, basis.constr_basis, f_map] },
    rw [h₁, mul_eq_mul_right_iff] at h₀,
    cases h₀,
    {
      simp only [x₀, x₁] at h₀,
      exact real_basis_vec₀_ne_real_basis_vec₁.symm (real_basis.injective h₀),
    },
    {
      rw linear_map.map_eq_zero_iff at h₀,
      linarith,
    }
  }
end

example {a b b' c : ℝ} (hc : c ≠ 0) (h : a = b * c) (h' : a = b' * c) : b = b' :=
begin
  rw [h, mul_eq_mul_right_iff] at h',
  exact (or_iff_left hc).1 h',
end

example {P Q : Prop} (h : P ∨ Q) (h' : ¬Q) : P :=
begin
  library_search!,
end

example : ite (1 = 1) 2 3 = 2 :=
begin
  dec_trivial,
end

example : ↑(↑(3 : ℤ) / ↑(2 : ℤ) : ℚ).denom = (2 : ℤ) :=
begin
  rw rat.denom_div_eq_of_coprime; norm_num,
end

example {a b c : ℚ} : a / b * c = a * c / b :=
begin
  simp only [div_eq_mul_inv, mul_assoc, mul_comm b⁻¹ c],
end

example {q : ℚ} {c : ℤ}
  (h : ↑q.denom ∣ q.num * c)
  (h' : coprime q.denom q.num.nat_abs)
: ↑q.denom ∣ c :=
begin
  exact int.dvd_of_dvd_mul_right_of_gcd_one h h',
end

example {a b : ℤ} : (a : ℚ) * (b : ℚ) = ↑(a * b) :=
begin
  rw int.cast_mul,
end

example {a b c : ℤ} (h : a ∣ c) : a ∣ b * c :=
begin
  exact dvd_mul_of_dvd_right h b,
end

example {a b c : ℕ} (h : a ∣ b) : a ∣ b.lcm c :=
begin
  exact dvd_trans h (nat.dvd_lcm_left _ _),
end

example {P Q : Prop} (h : ¬P ↔ ¬Q) : P ↔ Q :=
iff.trans (iff.trans not_not.symm (not_iff_not_of_iff h)) not_not

example {P Q : Prop} (h : P ↔ Q) (h' : Q) : P := (iff.symm h).1 h'

example {P Q : Prop} (h': P) : P ↔ Q :=
begin
  rw [iff_true_intro h', true_iff],
end

example {α : Type*} [non_assoc_ring α] (m n : ℤ) : ((m * n : ℤ) : α) = m * n :=
begin
  refine int.induction_on' m 0 _ _ _,
  { simp },
  { intros _ ih, simp [add_mul, ih] },
  { intros _ ih, simp [sub_mul, ih] },
end

example {α : Type*} [division_ring α] [char_zero α] (q : ℚ) :
(q : α) = ↑q.num / ↑q.denom :=
begin
  conv_lhs { rw ← rat.num_div_denom q },
  rw [rat.cast_div, rat.cast_coe_int, rat.cast_coe_nat],
end

example {f : ℕ+ → ℚ} (h : summable f): summable (λ n : ℕ+, f n * n / n) :=
begin
  -- simp_rw looks inside binders like λ
  -- You have to provide the full statement, hence the `show ∀ ...` then `_`
  simp_rw [← mul_div, div_self ((show ∀ n : ℕ+, (n : ℚ) ≠ 0, by simp) _), mul_one, h],
end

end polynomial

example {n : ℕ} {S : finset ℕ} (h : S = filter nat.prime (Icc 1 n)):
S.sum (λ p, ite (nat.prime p) 1 0) = S.sum (λ p, 1) :=
begin
  -- rw finset.sum_congr,
  simp,
  -- show_term { squeeze_simp [h] },
end

-- Approach 1, using `conv`
example {n : ℕ} : ∫ x : ℝ in 0..1, (-x) ^ n = (-1) ^ n * 1 / (n + 1) :=
begin
  conv {
    to_lhs,
    congr,
    funext,
    rw [neg_pow, mul_comm],
  },
  norm_num [mul_div, mul_comm],
end

-- Approach 2, using `conv` but smarter
example {n : ℕ} : ∫ x : ℝ in 0..1, (-x) ^ n = (-1) ^ n * 1 / (n + 1) :=
begin
  conv in (_ ^ _) { rw neg_pow, },
  norm_num [mul_div],
end

-- Approach 3, using `simp only` with `ctx`
example {n : ℕ} : ∫ x : ℝ in 0..1, (-x) ^ n = (-1) ^ n * 1 / (n + 1) :=
begin
  simp only [neg_pow] { single_pass := tt },
  norm_num [mul_div],
end

example {n : ℕ} : ∑ x in range (n + 1), (↑(n - x) : ℝ) = ∑ x in range (n + 1), (↑n - ↑x) :=
begin
  -- I want to cast ↑(n - x) into ↑n - ↑x, using the assumption that x ∈ range (n + 1)
  -- But this isn't really possible, so I have to use sum_congr
  apply sum_congr rfl,
  intros x hx,
  -- And then extract the condition here
  rw mem_range_succ_iff at hx,
  rw nat.cast_sub hx,
end

example {n : ℕ} : ∃ (N : ℕ), (N : ℝ) = (Icc 1 (n * 2 + 1)).lcm coe * ∑ (x : ℕ) in range (n + 1), (n.choose x) * (-1) ^ (n - x) / (↑(n - x) + ↑n + 1) :=
begin
  -- Key: use `apply_congr` instead of plain `congr` to include "local information"
  conv in (finset.sum _ _) {
    apply_congr,
    skip,
    rw [nat.cast_sub (mem_range_succ_iff.1 H), ← add_sub_right_comm],
  },
  sorry,
end

#eval ((nat.prime 3) : bool)
#eval ((nat.prime (2^32 + 15)) : bool)

example {n : ℕ} : ∃ N : ℕ, ↑N = (n : ℝ) :=
begin
  squeeze_simp,
end

example {n : ℕ} : even n ∨ odd n :=
begin
  -- strong induction on n
  induction n using nat.strong_induction_on with k hk,
  -- handle n = 0
  by_cases h₀ : k = 0,
  { left, use 0, rwa add_zero, },
  -- handle n = 1
  by_cases h₁ : k = 1,
  { right, use 0, rwa [mul_zero, zero_add], },
  { -- first use induction hypothesis on (n - 2)
    -- by proving 2 ≤ n
    have h : 2 ≤ k,
    { omega, },
    -- and prove n - 2 < n, i.e. we can use strong induction
    have h' : k - 2 < k,
    { omega, },
    -- that way we can subtract
    specialize hk (k - 2) h',
    -- now depending on whether (k - 2) is even or odd
    -- we split into cases
    cases hk,
    -- even case, meaning k - 2 = 2k'
    { cases hk with k' hk', left, use k' + 1, linarith, },
    -- odd case, meaning k - 2 = 2k' + 1
    { cases hk with k' hk', right, use k' + 1, linarith, },
  }
end

example {k : ℕ} (h : k ≠ 0) (h' : k ≠ 1) : 2 ≤ k :=
begin
  rcases k with _|_|_;
  simpa <|> simp [nat.succ_le_succ_iff],
end

example {k : ℕ} : volume {x : ℝ | 0 ≤ x ∧ x ≤ 1} = 1 :=
begin
  rwa [← set.Icc, volume_Icc, tsub_zero, ennreal.of_real_one],
end

-- lim (x → ∞) (1 / x) = 0
example {f : ℝ → ℝ} (h : f = λ x, 1 / x) : filter.tendsto f filter.at_top (nhds 0) :=
begin
  rw [h, filter.tendsto_at_top'],
  intros s hs,
  -- Rephrase nhds as open ball
  rw _root_.mem_nhds_iff at hs,
  -- Get an instance of open ball
  rcases hs with ⟨t, ⟨H, ⟨ht, ht'⟩⟩⟩,
  -- t ∈ nhds 0
  replace ht := is_open_iff_mem_nhds.1 ht 0 ht',
  -- find (-ε, ε) within t
  rcases mem_nhds_iff_exists_Ioo_subset.1 ht with ⟨l, ⟨r, ⟨h₁, h₂⟩⟩⟩,
  -- prove that 0 < r
  rw [set.Ioo, set.mem_set_of_eq] at h₁,
  -- finish proof that ∀ b ≥ 2 / r, 1 / b < r
  use 2 / r,
  intros b hb,
  rw ge_iff_le at hb,
  have b_pos : 0 < b,
  { exact lt_of_lt_of_le (div_pos zero_lt_two h₁.2) hb, },
  rw [div_le_iff h₁.2, mul_comm, ← div_le_iff b_pos] at hb,
  have h' : 1 / b < r,
  { have : 1 / b ≤ r / 2, by { simpa [le_div_iff (zero_lt_two' ℝ), mul_comm, ← mul_div_assoc], },
    linarith, },
  calc 1 / b ∈ set.Ioo 0 r : by { rw [set.Ioo, set.mem_set_of_eq], split,
                                  exact div_pos zero_lt_one b_pos, linarith, }
         ... ⊆ set.Ioo l r : by { apply set.Ioo_subset_Ioo_left, linarith [h₁.1], }
         ... ⊆ t           : h₂
         ... ⊆ s           : H,
end

-- Proof by Kevin Buzzard
example {f : ℝ → ℝ} (h : f = λ x, 1 / x) : filter.tendsto f filter.at_top (nhds 0) :=
begin
  rw [h, filter.tendsto_at_top'],
  intros s hs,
  -- Rephrase nhds as open ball
  rw _root_.mem_nhds_iff at hs,
  -- Get an instance of open ball
  rcases hs with ⟨t, ⟨H, ⟨ht, ht'⟩⟩⟩,
  -- Then there is an open interval inside
  rcases is_open.exists_Ioo_subset ht (by {use 0, exact ht'}) with ⟨l, ⟨h, ⟨hlh, hlh'⟩⟩⟩,
  -- ???
  rw is_open_iff_mem_nhds at ht,
  specialize ht _ ht',
  rw metric.mem_nhds_iff at ht,
  rcases ht with ⟨ε, hεpos, hε⟩,
  use 1 / ε + 37,
  intros b hb,
  replace hb := lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num)) hb,
  have hbpos : 0 < b := lt_trans (one_div_pos.2 hεpos) hb,
  rw one_div_lt hεpos at hb,
  apply H,
  apply hε,
  rw [mem_ball_zero_iff, real.norm_eq_abs],
  rwa abs_eq_self.2,
  all_goals {positivity},
end