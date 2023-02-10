import geometry.euclidean.angle.sphere
import linear_algebra.affine_space.finite_dimensional

open affine affine_map affine_subspace euclidean_geometry finite_dimensional set
open_locale affine big_operators classical euclidean_geometry real

-- https://www.wikiwand.com/en/Sylvester-Gallai_theorem
-- Note that this can be generalised to arbitrary metric spaces
-- See "The Sylvester–Chvatal Theorem" by Xiaomin Chen

namespace generic_space

variables (k : Type*) {V : Type*} {P : Type*}
variables [add_comm_group V] [affine_space V P]
include V

-- 3 points are either collinear, or one point doesn't lie on the the line through the other two
lemma lemma1 [division_ring k] [module k V] {p1 p2 p3 : P} :
(collinear k ({p1, p2, p3} : set P)) ∨ (p1 ∉ line[k, p2, p3]) :=
begin
  apply imp_iff_or_not.1,
  intro h,
  -- p1 ∈ line[k, p2, p3] ↔ ∃ a, a • (p2 -ᵥ p3) = p1 -ᵥ p3
  rw [← vsub_right_mem_direction_iff_mem (mem_affine_span k
      (set.mem_insert_of_mem p2 (mem_singleton p3))), direction_affine_span, vector_span_pair, 
      submodule.mem_span_singleton] at h,
  cases h with a ha,
  -- collinear {p1, p2, p3} ↔ ∀ (p : P), p ∈ {p1, p2, p3} → ∃ (r : k), p = r • (p2 -ᵥ p3) +ᵥ p3
  rw [collinear_iff_of_mem (show p3 ∈ {p1, p2, p3}, by simp)],
  use (p2 -ᵥ p3),
  intros p hp,
  -- cases on p ∈ {p1, p2, p3}
  cases hp,
  { use a, rwa [ha, vsub_vadd], },
  cases hp,
  { use 1, rwa [one_smul, vsub_vadd], },
  { rw mem_singleton_iff at hp, use 0, rwa [zero_smul, zero_vadd], },
end

-- For a finite set of points S, a line connecting points in S is *ordinary* if it passes through
-- exactly two points in S.
def ordinary_line [ring k] [module k V] (s : finset P) (p1 p2 : P) (h1 : p1 ∈ s) (h2 : p2 ∈ s) :=
∀ p ∈ s, p = p1 ∨ p = p2 ∨ p ∉ line[k, p1, p2]

end generic_space

---------------------------------------------------------------------------------------------------

namespace real_space

open metric emetric ennreal nnreal

-- Specify on the real plane
noncomputable theory

-- variables {V : Type*} {P : Type*}
-- variables [add_comm_group V] [module ℝ V] [affine_space V P] [metric_space P]
-- include V

variables (V : Type*) {Pt : Type*} [inner_product_space ℝ V] [metric_space Pt]
variables [normed_add_torsor V Pt] [finite_dimensional ℝ V] [hd2 : fact (finrank ℝ V = 2)]
include hd2

-- Perpendicular distance from p3 to p1 p2, which doesn't seem to be defined in mathlib
def perp_dist (p1 p2 p3 : Pt) : ℝ := metric.inf_dist p3 line[ℝ, p1, p2]

-- (Practice lemmas)
-- The perpendicular distance from p1 to p1 p2 is 0
lemma lemma1 {p1 p2 : Pt} : perp_dist V p1 p2 p1 = 0 :=
begin
  simp only [perp_dist, coe_affine_span, inf_dist,
             inf_edist_zero_of_mem (mem_span_points ℝ p1 _ (mem_insert p1 _)), zero_to_real],
end

-- The shortest distance from p3 to any point on p1 p2 is perpendicular distance
lemma lemma2 {p1 p2 p3 : Pt} :
(⨅ x ∈ line[ℝ, p1, p2], edist x p3).to_real = perp_dist V p1 p2 p3 :=
begin
  rw perp_dist,
  rw coe_affine_span,
  rw [inf_dist, inf_edist],
  simp_rw [edist_dist, dist_comm],
  exact rfl,
end

-- The Sylvester-Gallai Theorem, this formulation doesn't work
theorem sylvester_gallai {s : finset Pt} (h : ¬(collinear ℝ (s : set Pt))):
∃ p1 (hp1 : p1 ∈ s) p2 (hp2 : p2 ∈ s), generic_space.ordinary_line ℝ s p1 p2 hp1 hp2 :=
begin

end

end real_space