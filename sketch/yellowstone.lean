import data.nat.lattice
import data.nat.prime
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
    { norm_num [s], },
    { norm_num [s], },
    { norm_num [s], },
    { norm_num [s], },
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
      { norm_num [s], },
      { norm_num [s], },
      { norm_num [s], },
      { norm_num [s], },
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