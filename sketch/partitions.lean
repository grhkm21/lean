import ring_theory.power_series.basic
import combinatorics.partition
import data.nat.parity
import data.finset.nat_antidiagonal
import data.fin.tuple.nat_antidiagonal
import tactic.interval_cases
import tactic.apply_fun
import tactic.congrm

open power_series
noncomputable theory

variables {α : Type*}

open finset
open_locale big_operators
open_locale classical

def partial_odd_gf (m : ℕ) [field α] := ∏ i in range m, (1 - (X : power_series α)^(2*i+1))⁻¹

def partial_distinct_gf (m : ℕ) [comm_semiring α] :=
∏ i in range m, (1 + (X : power_series α)^(i+1))

/--
Functions defined only on `s`, which sum to `n`. In other words, a partition of `n` indexed by `s`.
Every function in here is finitely supported, and the support is a subset of `s`.
This should be thought of as a generalisation of `finset.nat.antidiagonal_tuple` where
`antidiagonal_tuple k n` is the same thing as `cut (s : finset.univ (fin k)) n`.
-/
def cut {ι : Type*} (s : finset ι) (n : ℕ) : finset (ι → ℕ) :=
finset.filter (λ f, s.sum f = n) ((s.pi (λ _, range (n+1))).map
  ⟨λ f i, if h : i ∈ s then f i h else 0,
   λ f g h, by { ext i hi, simpa [dif_pos hi] using congr_fun h i }⟩)

lemma mem_cut {ι : Type*} (s : finset ι) (n : ℕ) (f : ι → ℕ) :
  f ∈ cut s n ↔ s.sum f = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [cut, mem_filter, and_comm, and_congr_right],
  intro h,
  simp only [mem_map, exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_range, nat.lt_succ_iff, ← h],
      apply single_le_sum _ hi,
      simp },
    { ext,
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm],
      exact hf x } }
end

lemma cut_equiv_antidiag (n : ℕ) :
  equiv.finset_congr (equiv.bool_arrow_equiv_prod _) (cut univ n) = nat.antidiagonal n :=
begin
  ext ⟨x₁, x₂⟩,
  simp_rw [equiv.finset_congr_apply, mem_map, equiv.to_embedding, function.embedding.coe_fn_mk,
           ←equiv.eq_symm_apply],
  simp [mem_cut, add_comm],
end

lemma cut_univ_fin_eq_antidiagonal_tuple (n : ℕ) (k : ℕ) :
  cut univ n = nat.antidiagonal_tuple k n :=
by { ext, simp [nat.mem_antidiagonal_tuple, mem_cut] }

/-- There is only one `cut` of 0. -/
@[simp]
lemma cut_zero {ι : Type*} (s : finset ι) :
  cut s 0 = {0} :=
begin
  -- In general it's nice to prove things using `mem_cut` but in this case it's easier to just
  -- use the definition.
  rw [cut, range_one, pi_const_singleton, map_singleton, function.embedding.coe_fn_mk,
      filter_singleton, if_pos, singleton_inj],
  { ext, split_ifs; refl },
  rw sum_eq_zero_iff,
  intros x hx,
  apply dif_pos hx,
end

@[simp]
lemma cut_empty_succ {ι : Type*} (n : ℕ) :
  cut (∅ : finset ι) (n+1) = ∅ :=
begin
  apply eq_empty_of_forall_not_mem,
  intros x hx,
  rw [mem_cut, sum_empty] at hx,
  cases hx.1,
end

lemma cut_insert {ι : Type*} (n : ℕ) (a : ι) (s : finset ι) (h : a ∉ s) :
  cut (insert a s) n =
  (nat.antidiagonal n).bUnion
    (λ (p : ℕ × ℕ), (cut s p.snd).map
      ⟨λ f, f + λ t, if t = a then p.fst else 0, add_left_injective _⟩) :=
begin
  ext f,
  rw [mem_cut, mem_bUnion, sum_insert h],
  split,
  { rintro ⟨rfl, h₁⟩,
    simp only [exists_prop, function.embedding.coe_fn_mk, mem_map,
               nat.mem_antidiagonal, prod.exists],
    refine ⟨f a, s.sum f, rfl, λ i, if i = a then 0 else f i, _, _⟩,
    { rw [mem_cut],
      refine ⟨_, _⟩,
      { rw [sum_ite],
        have : (filter (λ x, x ≠ a) s) = s,
        { apply filter_true_of_mem,
          rintro i hi rfl,
          apply h hi },
        simp [this] },
      { intros i hi,
        rw ite_eq_left_iff,
        intro hne,
        apply h₁,
        simp [not_or_distrib, hne, hi] } },
    { ext,
      obtain rfl|h := eq_or_ne x a,
      { simp },
      { simp [if_neg h] } } },
  { simp only [mem_insert, function.embedding.coe_fn_mk, mem_map, nat.mem_antidiagonal, prod.exists,
               exists_prop, mem_cut, not_or_distrib],
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩,
    refine ⟨_, _⟩,
    { simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm] },
    { rintro i ⟨h₁, h₂⟩,
      simp [if_neg h₁, hg₂ _ h₂] } }
end

lemma coeff_prod_range
  [comm_semiring α] {ι : Type*} (s : finset ι) (f : ι → power_series α) (n : ℕ) :
  coeff α n (∏ j in s, f j) = ∑ l in cut s n, ∏ i in s, coeff α (l i) (f i) :=
begin
  revert n,
  apply finset.induction_on s,
  { rintro ⟨_ | n⟩,
    { simp },
    simp [cut_empty_succ, if_neg (nat.succ_ne_zero _)] },
  intros a s hi ih n,
  rw [cut_insert _ _ _ hi, prod_insert hi, coeff_mul, sum_bUnion],
  { congrm finset.sum _ (λ i, _),
    simp only [sum_map, pi.add_apply, function.embedding.coe_fn_mk, prod_insert hi, if_pos rfl, ih,
      mul_sum],
    apply sum_congr rfl _,
    intros x hx,
    rw mem_cut at hx,
    rw [hx.2 a hi, zero_add],
    congrm _ * _,
    apply prod_congr rfl,
    intros k hk,
    rw [if_neg, add_zero],
    exact ne_of_mem_of_not_mem hk hi },
  { simp only [set.pairwise_disjoint, set.pairwise, prod.forall, not_and, ne.def,
      nat.mem_antidiagonal, disjoint_left, mem_map, exists_prop, function.embedding.coe_fn_mk,
      exists_imp_distrib, not_exists, finset.mem_coe, function.on_fun, mem_cut, and_imp],
    rintro p₁ q₁ rfl p₂ q₂ h t x p hp hp2 hp3 q hq hq2 hq3,
    have z := hp3.trans hq3.symm,
    have := sum_congr (eq.refl s) (λ x _, function.funext_iff.1 z x),
    obtain rfl : q₁ = q₂,
    { simpa [sum_add_distrib, hp, hq, if_neg hi] using this },
    obtain rfl : p₂ = p₁,
    { simpa using h },
    exact (t rfl).elim }
end

/-- A convenience constructor for the power series whose coefficients indicate a subset. -/
def indicator_series (α : Type*) [semiring α] (s : set ℕ) : power_series α :=
power_series.mk (λ n, if n ∈ s then 1 else 0)

lemma coeff_indicator (s : set ℕ) [semiring α] (n : ℕ) :
  coeff α n (indicator_series _ s) = if n ∈ s then 1 else 0 :=
coeff_mk _ _
lemma coeff_indicator_pos (s : set ℕ) [semiring α] (n : ℕ) (h : n ∈ s):
  coeff α n (indicator_series _ s) = 1 :=
by rw [coeff_indicator, if_pos h]
lemma coeff_indicator_neg (s : set ℕ) [semiring α] (n : ℕ) (h : n ∉ s):
  coeff α n (indicator_series _ s) = 0 :=
by rw [coeff_indicator, if_neg h]
lemma constant_coeff_indicator (s : set ℕ) [semiring α] :
  constant_coeff α (indicator_series _ s) = if 0 ∈ s then 1 else 0 :=
rfl

lemma two_series (i : ℕ) [semiring α] :
  (1 + (X : power_series α)^i.succ) = indicator_series α {0, i.succ} :=
begin
  ext,
  simp only [coeff_indicator, coeff_one, coeff_X_pow, set.mem_insert_iff, set.mem_singleton_iff,
    map_add],
  cases n with d,
  { simp [(nat.succ_ne_zero i).symm] },
  { simp [nat.succ_ne_zero d], },
end

lemma num_series' [field α] (i : ℕ) :
  (1 - (X : power_series α)^(i+1))⁻¹ = indicator_series α { k | i + 1 ∣ k } :=
begin
  rw power_series.inv_eq_iff_mul_eq_one,
  { ext,
    cases n,
    { simp [mul_sub, zero_pow, constant_coeff_indicator] },
    { simp only [coeff_one, if_neg n.succ_ne_zero, mul_sub, mul_one,
                 coeff_indicator, linear_map.map_sub],
      simp_rw [coeff_mul, coeff_X_pow, coeff_indicator, boole_mul, sum_ite, filter_filter,
               sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one, sub_eq_iff_eq_add,
               zero_add, filter_congr_decidable],
      symmetry,
      split_ifs,
      { suffices :
        ((nat.antidiagonal n.succ).filter (λ (a : ℕ × ℕ), i + 1 ∣ a.fst ∧ a.snd = i + 1)).card = 1,
        { simp only [set.mem_set_of_eq], rw this, norm_cast },
        rw card_eq_one,
        cases h with p hp,
        refine ⟨((i+1) * (p-1), i+1), _⟩,
        ext ⟨a₁, a₂⟩,
        simp only [mem_filter, prod.mk.inj_iff, nat.mem_antidiagonal, mem_singleton],
        split,
        { rintro ⟨a_left, ⟨a, rfl⟩, rfl⟩,
          refine ⟨_, rfl⟩,
          rw [nat.mul_sub_left_distrib, ← hp, ← a_left, mul_one, nat.add_sub_cancel] },
        { rintro ⟨rfl, rfl⟩,
          cases p,
          { rw mul_zero at hp, cases hp },
          rw hp,
          simp [nat.succ_eq_add_one, mul_add] } },
      { suffices :
        (filter (λ (a : ℕ × ℕ), i + 1 ∣ a.fst ∧ a.snd = i + 1) (nat.antidiagonal n.succ)).card = 0,
        { simp only [set.mem_set_of_eq], rw this, norm_cast },
        rw card_eq_zero,
        apply eq_empty_of_forall_not_mem,
        simp only [prod.forall, mem_filter, not_and, nat.mem_antidiagonal],
        rintro _ h₁ h₂ ⟨a, rfl⟩ rfl,
        apply h,
        simp [← h₂] } } },
  { simp [zero_pow] },
end

def mk_odd : ℕ ↪ ℕ := ⟨λ i, 2 * i + 1, λ x y h, by linarith⟩

-- The main workhorse of the partition theorem proof.
lemma partial_gf_prop
  (α : Type*) [comm_semiring α] (n : ℕ) (s : finset ℕ)
  (hs : ∀ i ∈ s, 0 < i) (c : ℕ → set ℕ) (hc : ∀ i ∉ s, 0 ∈ c i) :
  (finset.card
    ((univ : finset (nat.partition n)).filter
      (λ p, (∀ j, p.parts.count j ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s)) : α) =
        (coeff α n) (∏ (i : ℕ) in s, indicator_series α ((* i) '' c i)) :=
begin
  simp_rw [coeff_prod_range, coeff_indicator, prod_boole, sum_boole],
  congr' 1,
  refine finset.card_congr (λ p _ i, multiset.count i p.parts • i) _ _ _,
  { simp only [mem_filter, mem_cut, mem_univ, true_and, exists_prop, and_assoc, and_imp,
               smul_eq_zero, function.embedding.coe_fn_mk, exists_imp_distrib],
    rintro ⟨p, hp₁, hp₂⟩ hp₃ hp₄,
    dsimp only at *,
    refine ⟨_, _, _⟩,
    { rw [←hp₂, ←sum_multiset_count_of_subset p s (λ x hx, hp₄ _ (multiset.mem_to_finset.mp hx))] },
    { intros i hi,
      left,
      exact multiset.count_eq_zero_of_not_mem (mt (hp₄ i) hi) },
    { exact λ i hi, ⟨_, hp₃ i, rfl⟩ } },
  { intros p₁ p₂ hp₁ hp₂ h,
    apply nat.partition.ext,
    simp only [true_and, mem_univ, mem_filter] at hp₁ hp₂,
    ext i,
    rw function.funext_iff at h,
    specialize h i,
    cases i,
    { rw multiset.count_eq_zero_of_not_mem,
      rw multiset.count_eq_zero_of_not_mem,
      intro a, exact nat.lt_irrefl 0 (hs 0 (hp₂.2 0 a)),
      intro a, exact nat.lt_irrefl 0 (hs 0 (hp₁.2 0 a)) },
    { rwa [nat.nsmul_eq_mul, nat.nsmul_eq_mul, mul_left_inj' i.succ_ne_zero] at h } },
  { simp only [mem_filter, mem_cut, mem_univ, exists_prop, true_and, and_assoc],
    rintros f ⟨hf₁, hf₂, hf₃⟩,
    refine ⟨⟨∑ i in s, multiset.replicate (f i / i) i, _, _⟩, _, _, _⟩,
    { intros i hi,
      simp only [exists_prop, mem_sum, mem_map, function.embedding.coe_fn_mk] at hi,
      rcases hi with ⟨t, ht, z⟩,
      apply hs,
      rwa multiset.eq_of_mem_replicate z },
    { simp_rw [multiset.sum_sum, multiset.sum_replicate, nat.nsmul_eq_mul, ←hf₁],
      refine sum_congr rfl (λ i hi, nat.div_mul_cancel _),
      rcases hf₃ i hi with ⟨w, hw, hw₂⟩,
      rw ← hw₂,
      exact dvd_mul_left _ _ },
    { intro i,
      simp_rw [multiset.count_sum', multiset.count_replicate, sum_ite_eq],
      split_ifs with h h,
      { rcases hf₃ i h with ⟨w, hw₁, hw₂⟩,
        rwa [← hw₂, nat.mul_div_cancel _ (hs i h)] },
      { exact hc _ h } },
    { intros i hi,
      rw mem_sum at hi,
      rcases hi with ⟨j, hj₁, hj₂⟩,
      rwa multiset.eq_of_mem_replicate hj₂ },
    { ext i,
      simp_rw [multiset.count_sum', multiset.count_replicate, sum_ite_eq],
      split_ifs,
      { apply nat.div_mul_cancel,
        rcases hf₃ i h with ⟨w, hw, hw₂⟩,
        apply dvd.intro_left _ hw₂ },
      { rw [zero_smul, hf₂ i h] } } },
end

lemma partial_partition_gf_prop [field α] (n m : ℕ) :
  (finset.card ((univ : finset (nat.partition n)).filter
    (λ p, ∀ j ∈ p.parts, j ∈ (range m).map mk_odd)) : α) = coeff α n (partial_odd_gf m) :=
begin
  rw partial_odd_gf,
  convert partial_gf_prop α n ((range m).map mk_odd) _ (λ _, set.univ) (λ _ _, trivial) using 2,
  { congrm card (filter (λ p, _) _),
    simp only [true_and, forall_const, set.mem_univ] },
  { rw finset.prod_map,
    simp_rw num_series',
    congrm finset.prod _ (λ x, indicator_series α _),
    ext k,
    split,
    { rintro ⟨p, rfl⟩,
      refine ⟨p, ⟨⟩, _⟩,
      apply mul_comm },
    rintro ⟨a_w, -, rfl⟩,
    apply dvd.intro_left a_w rfl },
  { intro i,
    rw mem_map,
    rintro ⟨a, -, rfl⟩,
    exact nat.succ_pos _ },
end

/--  If m is big enough, the partial product's coefficient counts the number of odd partitions -/
theorem partition_gf_prop [field α] (n m : ℕ) (h : n < m * 2) :
  (finset.card (finset (nat.partition n)) : α) = coeff α n (partial_odd_gf m) :=
begin
  rw [← partial_odd_gf_prop],
  congrm card (filter (λ p,  (_ : Prop)) _),
  apply ball_congr,
  intros i hi,
  have hin : i ≤ n,
  { simpa [p.parts_sum] using multiset.single_le_sum (λ _ _, nat.zero_le _) _ hi },
  simp only [mk_odd, exists_prop, mem_range, function.embedding.coe_fn_mk, mem_map],
  split,
  { intro hi₂,
    have := nat.mod_add_div i 2,
    rw nat.not_even_iff at hi₂,
    rw [hi₂, add_comm] at this,
    refine ⟨i / 2, _, this⟩,
    rw nat.div_lt_iff_lt_mul zero_lt_two,
    exact lt_of_le_of_lt hin h },
  { rintro ⟨a, -, rfl⟩,
    rw even_iff_two_dvd,
    apply nat.two_not_dvd_two_mul_add_one },
end
