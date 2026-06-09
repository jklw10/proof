import entropy.DTCproof
import entropy.GaussianBase
import entropy.GaussianEntropy
import entropy.GaussianDecay

open Filter
open Topology
noncomputable section
open Real
open MeasureTheory
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-- The unified convergence theorem specialized to the emergent Gaussian process. -/
theorem Gaussian_predictability_entropy_convergence :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let P := fun (i : ℤ) => standard_normal_pdf (i * Δx) * Δx
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      let H_discrete := - ∑ i ∈ s, P i * log (P i)
      H_discrete + log Δx)
    atTop
    (nhds ((1/2) * log (2 * Real.pi * exp 1))) := by
  -- Apply the specialized convergence theorem directly (no arguments needed)
  have h_lim := discrete_to_continuous_gaussian_entropy_convergence
  rw [continuous_standard_normal_entropy] at h_lim
  exact h_lim
