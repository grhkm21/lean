import data.nat.basic
import data.nat.prime
import data.nat.prime_norm_num
import tactic
import data.matrix.basic
import number_theory.bernoulli
import number_theory.bernoulli_polynomials

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
  library_search,
end

end polynomial