import data.nat.basic
import data.nat.prime
import data.nat.prime_norm_num
import data.real.basic
import tactic
import data.matrix.basic
import number_theory.bernoulli
import number_theory.bernoulli_polynomials
import number_theory.liouville.liouville_constant

open_locale big_operators
open_locale nat polynomial

open nat finset

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
  -- We construct a transcendental number x
  let x := liouville.liouville_number 1,

  -- Then construct the set {1, x, x^2, ...}
  
  -- Then prove it is linearly independent
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

end polynomial