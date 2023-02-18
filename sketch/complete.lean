import order.succ_pred.basic
import tactic

open finset
open_locale big_operators

---------------------------------------------------
-- Missing lemmas (`sketch/integrate.lean`)
lemma nat.Icc_succ_right {m n : ℕ} (h : m ≤ n): Icc m n.succ = has_insert.insert n.succ (Icc m n) :=
begin
  ext,
  have : (m ≤ a ∧ a = n.succ) = (a = n.succ),
  { rw eq_iff_iff,
    split,
    { exact and.right, },
    { intro h₁, rw h₁, exact ⟨nat.le_succ_of_le h, eq.refl n.succ⟩, }, },
  simp_rw [mem_insert, mem_Icc, nat.le_add_one_iff, and_or_distrib_left, this, or.comm],
end
---------------------------------------------------

-- Elementary definitions of subset sums
namespace set

variable (A : set ℕ)

-- Property indicating a number which is the sum of distinct elements of A
def summable (x : ℕ) : Prop := ∃ (S : finset ℕ) (hS : ↑S ⊆ A), (∑ s in S, id s) = x

-- The set of subset sums is numbers which is the sum of distinct elements of A
-- Obviously we can just take finite sets
def subset_sums : set ℕ := { x : ℕ | summable A x }

-- complete sequences: if eventually every number is a sum of distinct elements of A
def complete : Prop := ∃ (N : ℕ), ∀ (n : ℕ) (hn : N ≤ n), summable A n

-- entire complete sqeuences: if every number is a sum of distinct elements of A
def entirely_complete : Prop := ∀ (n : ℕ), summable A n

theorem summable_zero : summable A 0 := ⟨∅, ⟨empty_subset A, sum_empty⟩⟩

-- entire completeness implies completeness
theorem complete_of_entirely_complete : entirely_complete A → complete A :=
begin
  intro h,
  use 0,
  simp_rw [zero_le', forall_true_left],
  exact h,
end

end set

-- Alternative definitions with sequences
namespace seq

variables (f : ℕ → ℕ)

-- Property indicating a number which is the sum of subsequence of f
def summable (x : ℕ) : Prop := ∃ S, (∑ s in S, f s) = x

-- The set of subset sums is numbers which is the sum of subsequence of f
def subset_sums : set ℕ := { x : ℕ | summable f x }

-- Complete sequences: if eventually every number is a sum of subsequence of f
def complete : Prop := ∃ (N : ℕ), ∀ (n : ℕ) (hn : N ≤ n), summable f n

-- Entirely complete sqeuences: if every number is a sum of distinct elements of A
-- Zero is the sum of empty set
def entirely_complete : Prop := ∀ (n : ℕ), summable f n

theorem summable_zero : summable f 0 := ⟨∅, sum_empty⟩

-- Entire completeness implies completeness
theorem complete_of_entirely_complete : entirely_complete f → complete f :=
begin
  intro h,
  use 0,
  simp_rw [zero_le', forall_true_left],
  exact h,
end

-- For a monotone sequence, this is a necessary and sufficient condition to be entirely complete
theorem entirely_complete_iff (f : ℕ → ℕ) (hf : monotone f) :
entirely_complete f ↔ summable f 1 ∧ ∀ n : ℕ, f (n + 1) ≤ 1 + ∑ i in Icc 0 n, f i :=
begin
  split,
  {
    intro h,
    split,
    { exact h 1, },
    { by_contradiction h',
      push_neg at h',
      cases h' with k hk,
      apply imp_false.2 _ h,
      simp_rw [entirely_complete, summable],
      push_neg,
      use 1 + ∑ i in Icc 0 k, f i,
      -- Prove that 1 + ∑ i in Icc 0 k, f i is not sum of distinct elements
      sorry,
    },
  },
  {
    intro h,
    -- By induction, prove that f 0 to f k covers [0, 1 + ∑ i in Icc 0 k, f i]
    -- Then adding f (k + 1) shifts the interval
    sorry,
  }
end

-- Basic examples
namespace examples

-- 2^n is entirely complete
example : entirely_complete (pow 2) :=
begin
  rw entirely_complete_iff (pow 2) (pow_mono one_le_two),
  split,
  { use {0}, rw [sum_singleton, pow_zero], },
  { intro n,
    induction n with k hk,
    { simp, },
    { rw [nat.Icc_succ_right k.zero_le, sum_insert, ← add_assoc, pow_add, pow_one, mul_two,
          add_comm 1 _, add_assoc],
      apply nat.add_le_add_left hk,
      simp only [mem_Icc, zero_le', true_and, not_le, nat.lt_succ_self k], }, },
end

end examples

end seq
-- characterises complete sequences