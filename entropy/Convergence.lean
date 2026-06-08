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

/-- The standard normal PDF is globally differentiable. -/
lemma standard_normal_differentiable : Differentiable ℝ standard_normal_pdf := by
  intro x
  exact (standard_normal_deriv x).differentiableAt

/-- The entropy integrand f(x) * log (f(x)) is integrable. -/
lemma integrable_standard_normal_entropy :
    Integrable (fun x => standard_normal_pdf x * log (standard_normal_pdf x)) := by
  -- Reuse the exact algebraic expansion you verified in `continuous_standard_normal_entropy`
  have h_eq : (fun x : ℝ => standard_normal_pdf x * log (standard_normal_pdf x)) =
              (fun x : ℝ => - (1/2) * log (2 * Real.pi) * standard_normal_pdf x - (1/2) * (x^2 * standard_normal_pdf x)) := by
    ext x
    rw [log_standard_normal_pdf x]
    ring
  rw [h_eq]
  apply Integrable.sub
  · apply Integrable.const_mul
    exact integrable_standard_normal_pdf
  · apply Integrable.const_mul
    exact integrable_x_sq_mul_standard_normal_pdf

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
  -- Apply the main convergence theorem using standard normal parameters
  have h_lim := discrete_to_continuous_entropy_convergence_proven standard_normal_pdf
    standard_normal_continuous
    standard_normal_pos
    integrable_standard_normal_pdf
    standard_normal_integral_eq_one
    integrable_standard_normal_entropy
    standard_normal_pdf_decay
    standard_normal_differentiable
    standard_normal_deriv_decay
  rw [continuous_standard_normal_entropy] at h_lim
  exact h_lim
