import data.nat.lattice
import data.nat.prime
import data.nat.prime_fin
import data.finset.basic
import tactic

open finset nat set
noncomputable

-- A098550 The Yellowstone permutation

def s : ℕ → ℕ
| 0       := 0
| 1       := 1
| 2       := 2
| 3       := 3
| (n + 4) := Inf { k : ℕ | 0 < k ∧ ∀ m < n + 4, s m ≠ k ∧ nat.coprime k (s (n + 3)) ∧
                   1 < nat.gcd k (s (n + 2)) }

@[simp]
lemma s0 : s 0 = 0 := by rw s
@[simp]
lemma s1 : s 1 = 1 := by rw s
@[simp]
lemma s2 : s 2 = 2 := by rw s
@[simp]
lemma s3 : s 3 = 3 := by rw s

-- Proof by ericr
lemma s_four : s 4 = 4 :=
begin
  rw s,
  have key : _ := _,
  rw nat.Inf_def ⟨4, key⟩,
  swap,
  { norm_num,
    intros m hm,
    interval_cases m; simp, },
  apply le_antisymm,
  { apply nat.find_min',
    exact key, },
  { rw le_find_iff,
    intros m hm,
    interval_cases m;
    simp [show ∃ x : ℕ, x < 4, by exact ⟨3, by simp⟩],
    exact ⟨2, by simp⟩, },
end

lemma s_nonempty {n : ℕ} : set.nonempty
{ k : ℕ | 0 < k ∧ ∀ m < n + 4, s m ≠ k ∧ nat.coprime k (s (n + 3)) ∧ 1 < nat.gcd k (s (n + 2)) } :=
begin
  induction n with k hk,
  { use 4, norm_num, intros m hm, interval_cases m; simp, },
  { -- construct prime larger than every value before
    have big_prime : ∃ p, nat.prime p ∧ ∀ m < k.succ + 4, s m < p,
    {  -- set of previous values
      let prev_values : finset ℕ := (finset.image s (finset.range (k.succ + 4))),
      let ub : ℕ := prev_values.sup id,
      -- use infinitude of primes
      rcases infinite.exists_nat_lt infinite_set_of_prime ub with ⟨p, ⟨hp, hp'⟩⟩,
      use p,
      split,
      { rw mem_set_of_eq at hp, exact hp, },
      { intros m hm,
        apply lt_of_le_of_lt _ hp',
        dsimp [ub],
        rw ← id.def (s m),
        apply le_sup,
        rw finset.mem_image,
        use m,
        simp [hm], }, },
    -- use s (k.succ + 2) * big_prime
    sorry, }
end

/-

Kept here for historical reasons + I want to laugh at myself forever at this

-- Maybe I should quit Lean...
lemma s_four : s 4 = 4 :=
begin
  rw s,
  apply le_antisymm,
  { apply nat.Inf_le,
    simp_rw [mem_set_of_eq, s, coprime],
    norm_num,
    intros m hm,
    rcases m with _|_|_|_|_,
    { simp, },
    { simp, },
    { simp, },
    { simp, },
    { exfalso,
      simp_rw [succ_lt_succ_iff] at hm, linarith, }, },
  { simp_rw [s, coprime],
    rw Inf_def,
    swap,
    { use 4,
      rw mem_set_of_eq,
      norm_num,
      intros m hm,
      rcases m with _|_|_|_|_,
      { simp, },
      { simp, },
      { simp, },
      { simp, },
      { exfalso,
        simp_rw [succ_lt_succ_iff] at hm, linarith, }, },
    rw nat.le_find_iff,
    norm_num,
    intros m hm,
    rcases m with _|_|_|_|_,
    { simp, },
    { simp, use 2, simp [s], },
    { simp, use 2, simp [s], },
    { simp, use 2, simp [s], },
    { simp_rw [succ_lt_succ_iff] at hm, linarith, }, },
end

-/