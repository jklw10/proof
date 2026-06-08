import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import entropy.common

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real

-- =========================================================================
-- PART 1: The Lorentzian Spectral Density
-- =========================================================================

/-- The spectral density S(k) of the continuous spatial process.
    This is the Fourier transform of the continuous covariance R(r) = C0 * exp(-|r|/ξ). -/
def spectral_density (C0 ξ k : ℝ) : ℝ :=
  (2 * C0 * ξ) / (1 + ξ^2 * k^2)

/-- Definition: Δk is the Half-Width at Half-Maximum (HWHM) of the spectral density.
    This means S(Δk) is exactly half of the maximum spectral density S(0). -/
def IsHWHM (C0 ξ Δk : ℝ) : Prop :=
  spectral_density C0 ξ Δk = (spectral_density C0 ξ 0) / 2

-- =========================================================================
-- PART 2: Derivation of the Conjugate Uncertainty Relation
-- =========================================================================

/-- Theorem: The Conjugate Uncertainty Relation for Entropic Diffusion.
    If the spatial process has variance C0 > 0 and correlation length ξ > 0,
    the spatial correlation length ξ and the spectral/momentum bandwidth Δk > 0
    satisfy the exact conjugate relation: ξ * Δk = 1. -/
theorem entropic_uncertainty_relation (C0 ξ Δk : ℝ)
    (hC0 : 0 < C0) (hξ : 0 < ξ) (hΔk : 0 < Δk)
    (h_hwhm : IsHWHM C0 ξ Δk) :
    ξ * Δk = 1 := by
  -- 1. Simplify the right-hand side of the HWHM equation: S(0) / 2
  have h_eq : (2 * C0 * ξ) / (1 + ξ^2 * Δk^2) = (2 * C0 * ξ) / 2 := by
    unfold IsHWHM spectral_density at h_hwhm
    have h_zero : 1 + ξ^2 * 0^2 = 1 := by ring
    rw [h_zero, div_one] at h_hwhm
    exact h_hwhm

  -- 2. Cancel the common factor (2 * C0 * ξ) on both sides
  have h_factor : 2 * C0 * ξ ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h2 (ne_of_gt hC0)) (ne_of_gt hξ)

  have h_frac_eq : 1 / (1 + ξ^2 * Δk^2) = 1 / 2 := by
    have h_div : (2 * C0 * ξ) / (1 + ξ^2 * Δk^2) = (2 * C0 * ξ) * (1 / (1 + ξ^2 * Δk^2)) := by ring
    have h_div2 : (2 * C0 * ξ) / 2 = (2 * C0 * ξ) * (1 / 2) := by ring
    rw [h_div, h_div2] at h_eq
    exact mul_left_cancel₀ h_factor h_eq

  -- 3. Clear denominators using field_simp
  have h_inv : 1 + ξ^2 * Δk^2 = 2 := by
    have h_denom_ne : 1 + ξ^2 * Δk^2 ≠ 0 := by
      have h_sq_nonneg : 0 ≤ ξ^2 * Δk^2 := by
        exact mul_nonneg (sq_nonneg ξ) (sq_nonneg Δk)
      linarith
    have h_two_ne : (2 : ℝ) ≠ 0 := by norm_num
    have h_cleared := h_frac_eq
    field_simp [h_denom_ne, h_two_ne] at h_cleared
    linarith

  -- 4. Solve for (ξ * Δk)^2
  have h_sq_eq : ξ^2 * Δk^2 = 1 := by linarith
  have h_prod_sq : (ξ * Δk)^2 = 1 := by
    calc (ξ * Δk)^2 = ξ^2 * Δk^2 := by ring
    _ = 1 := h_sq_eq

  -- 5. Take the square root to obtain the conjugate relation ξ * Δk = 1
  have h_prod_pos : 0 < ξ * Δk := mul_pos hξ hΔk
  have h_sqrt : ξ * Δk = Real.sqrt 1 := by
    rw [← h_prod_sq]
    exact (Real.sqrt_sq (le_of_lt h_prod_pos)).symm
  rw [Real.sqrt_one] at h_sqrt
  exact h_sqrt

-- =========================================================================
-- PART 3: Uncertainty Grounded in the Unified Models
-- =========================================================================

/-- Theorem: Grounding the Uncertainty Relation in the Legacy Process Model.
    If we evaluate the uncertainty relation using the physical predictability
    correlation length ξ defined in common.lean, the conjugate relationship holds. -/
theorem process_uncertainty_relation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess ℝ E) (Δk : ℝ) (hΔk : 0 < Δk)
    (h_hwhm : IsHWHM P.C0 (xi P.z) Δk) :
    (xi P.z) * Δk = 1 := by
  have hξ : 0 < xi P.z := xi_pos P.z P.hz0 P.hz1
  exact entropic_uncertainty_relation P.C0 (xi P.z) Δk P.hC0 hξ hΔk h_hwhm

/-- Theorem: Grounding the Uncertainty Relation in the Generalized Process Model.
    If we analyze the generalized process's spectrum via its characteristic scale ξ > 0
    and a Lorentzian-like spectral density peak, the conjugate relationship strictly holds. -/
theorem generalized_process_uncertainty_relation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : GeneralizedCovarianceProcess ℝ E) (ξ : ℝ) (hξ : 0 < ξ) (Δk : ℝ) (hΔk : 0 < Δk)
    (h_hwhm : IsHWHM P.C0 ξ Δk) :
    ξ * Δk = 1 := by
  exact entropic_uncertainty_relation P.C0 ξ Δk P.hC0 hξ hΔk h_hwhm

#print axioms process_uncertainty_relation
#print axioms generalized_process_uncertainty_relation
