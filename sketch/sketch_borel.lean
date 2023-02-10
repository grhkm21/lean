import topology.filter
import measure_theory.measure.null_measurable
import measure_theory.measurable_space
import measure_theory.measure.measure_space
import number_theory.well_approximable
import topology.algebra.order.liminf_limsup

open set filter (hiding map) function measurable_space topological_space (second_countable_topology)
open_locale classical big_operators filter ennreal nnreal interval measure_theory

namespace measure_theory

variables {α : Type*} {m : measurable_space α} {μ : measure α}

/-
Want to state using `well_approximate`:
For a function ψ : ℕ → ℝ≥0 such that ∑ q, (φ q * ψ q) / q < ∞, μ W = 0
-/

/- Gallagher's Ergodic Theorem -/
example {T : ℝ} [hT : fact (0 < T)] (δ : ℕ → ℝ) (hδ : tendsto δ at_top (nhds 0)) :
(∀ᵐ (x : add_circle T), ¬add_well_approximable (add_circle T) δ x) ∨
 ∀ᵐ (x : add_circle T), add_well_approximable (add_circle T) δ x := sorry

/- Borel-Cantelli Theorem -/
example {p : ℕ → α → Prop} (hp : ∑' i, μ {x | p i x} ≠ ∞) : μ {x | ∃ᶠ n in at_top, p n x} = 0 := 
sorry

/- Duffin-Schaeffer Theorem (Implication) -/
example (α : ℝ) (ψ : ℕ → ℝ≥0) (h : {q : ℚ | |α - q| ≤ ψ (q.denom) / q.denom}.infinite) : _ := sorry

end measure_theory