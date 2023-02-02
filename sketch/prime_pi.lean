import tactic
import data.nat.prime_norm_num
import number_theory.prime_counting

namespace nat
open_locale nat

example : prime 3 :=
begin
  norm_num,
end

example : list.filter prime [0,1,2,3,4,5,6,7,8,9,10] = [2,3,5,7] :=
begin
  unfold list.filter,
  norm_num,
end

example : list.filter prime [2,4] = [2,4] :=
begin
  unfold list.filter,
  norm_num,
end

example : list.countp prime [2,3,5,7] = 4 :=
begin
  unfold list.countp,
end

lemma adjoin_range {n : ℕ} : ∀ l, list.range_core n l = (list.range_core n list.nil) ++ l :=
begin
  induction n with k hk; intros a,
  { refl, },
  { dsimp [list.range_core],
    rw [hk [k], hk (k :: a), list.append_assoc, list.append_right_inj, list.singleton_append], },
end

lemma countp_singleton {α : Type} {p : α → Prop} [decidable_eq α] [decidable_pred p] (a : α) :
list.countp p [a] = ite (p a) 1 0 := rfl

lemma countp_range {n : ℕ} {p : ℕ → Prop} [decidable_pred p] :
list.countp p (list.range n.succ) = (ite (p n) 1 0) + list.countp p (list.range n) :=
begin
  dsimp [list.range],
  simp only [list.range_core, adjoin_range [n], list.countp_append, add_comm, add_left_cancel_iff],
  refl,
end

-- Benchmark: 14.2s, very slow
set_option profiler true
example {n : ℕ} : π 200 = 46 :=
begin
  rw [prime_counting, prime_counting', count],
  repeat { rw countp_range, norm_num1, simp only [if_false, if_true, zero_add], },
  rw [list.range_zero, list.countp_nil],
end

-- Benchmark: 949ms, quite fast
example {n : ℕ} : π 200 = 46 :=
begin
  rw [prime_counting, prime_counting', count],
  dsimp [list.range, list.range_core, list.countp],
  norm_num,
end

-- Benchmark: 949ms, quite fast
example {n : ℕ} : π 1000 = 168 :=
begin
  rw [prime_counting, prime_counting', count],
  dsimp [list.range, list.range_core, list.countp],
  norm_num,
end

end nat