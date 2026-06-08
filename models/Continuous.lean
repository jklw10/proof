import Mathlib.Analysis.SpecialFunctions.Pow.Real
import entropy.common

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real
open RealInnerProductSpace

-- =========================================================================
-- PART 1: Instantiating the Continuous Process Specializations
-- =========================================================================

section ContinuousSetup

/-- Helper function: Maps a continuous process u: ℝ → E satisfying the continuous
    exponential decay model with variance C0 and decay z to the unified framework. -/
def continuous_to_unified {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℝ → E) (C0 z : ℝ) (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * z ^ |x - y|)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) : ExponentialCovarianceProcess ℝ E where
  u := u
  C0 := C0
  z := z
  hC0 := hC0
  hz0 := hz0
  hz1 := hz1
  cov := by
    intro x y
    rw [Real.dist_eq, h_cov x y]

/-- Helper function: Maps a continuous process u: ℝ → E with any arbitrary radial covariance kernel K
    to the generalized unified framework. -/
def continuous_to_generalized_unified {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℝ → E) (C0 : ℝ) (K : ℝ → ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * K |x - y|)
    (hC0 : 0 < C0) (hK0 : K 0 = 1) : GeneralizedCovarianceProcess ℝ E where
  u := u
  C0 := C0
  K := K
  hC0 := hC0
  hK0 := hK0
  cov := by
    intro x y
    rw [Real.dist_eq, h_cov x y]

end ContinuousSetup

-- =========================================================================
-- PART 2: Continuous Unilateral Horizon Limit (Specialized)
-- =========================================================================

section ContinuousUnilateral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: Link to the physical predictability scale ξ_abs* defined in common.lean.
    The absolute MSE is bounded by δ if and only if the continuous distance r satisfies r ≤ ξ_abs*.
    Now proven as a direct specialization of the unified unilateral optimal MSE. -/
theorem continuous_unilateral_horizon_limit (u : ℝ → E) (C0 z δ r : ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * z ^ |x - y|)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) (hδ0 : 0 < δ) (hδ : δ < C0) (hr : 0 ≤ r) :
    let P := continuous_to_unified u C0 z h_cov hC0 hz0 hz1
    ‖P.u r - (P.z ^ r) • P.u 0‖^2 ≤ δ ↔ r ≤ xi_abs_star C0 z δ := by
  intro P
  have h_dist : dist r 0 = r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hr]
  have h_mse := ExponentialCovarianceProcess.unilateral_optimal_mse P r 0 r h_dist
  dsimp [P, continuous_to_unified] at h_mse ⊢
  rw [h_mse]
  have h_exp_eq : z ^ (2 * r) = exp (2 * r * log z) := by
    rw [Real.rpow_def_of_pos hz0]
    congr 1
    ring
  rw [h_exp_eq]
  exact unilateral_horizon_equivalence C0 z δ r hC0 hz0 hz1 hδ0 hδ

/-- Theorem: Specialized continuous unilateral optimal MSE for arbitrary covariance kernel K. -/
theorem generalized_continuous_unilateral_optimal_mse (u : ℝ → E) (C0 : ℝ) (K : ℝ → ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * K |x - y|)
    (hC0 : 0 < C0) (hK0 : K 0 = 1) (r : ℝ) (hr : 0 ≤ r) :
    let P := continuous_to_generalized_unified u C0 K h_cov hC0 hK0
    ‖P.u r - (P.K r) • P.u 0‖^2 = C0 * (1 - (K r)^2) := by
  intro P
  have h_dist : dist r 0 = r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hr]
  have h_mse := GeneralizedCovarianceProcess.generalized_unilateral_optimal_mse P r 0 r h_dist
  dsimp [P, continuous_to_generalized_unified] at h_mse ⊢
  rw [h_mse]

end ContinuousUnilateral

-- =========================================================================
-- PART 3: Continuous Bilateral Predictability (Specialized)
-- =========================================================================

section ContinuousBilateral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: Continuous Spatial Markov Orthogonality.
    Directly specializes the unified metric-space bilateral orthogonality theorem. -/
theorem continuous_bilateral_orthogonality (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * z ^ |x - y|) (hz0 : 0 < z) (hz1 : z < 1) (hC0 : 0 < C0)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) :
    let P := continuous_to_unified u C0 z h_cov hC0 hz0 hz1
    let d1 := x - a
    let d2 := b - x
    let d := b - a
    inner ℝ (P.u x - (((P.z ^ d1 - P.z ^ (d2 + d)) / (1 - P.z ^ (2 * d))) • P.u a +
             ((P.z ^ d2 - P.z ^ (d1 + d)) / (1 - P.z ^ (2 * d))) • P.u b)) (P.u a) = 0 ∧
    inner ℝ (P.u x - (((P.z ^ d1 - P.z ^ (d2 + d)) / (1 - P.z ^ (2 * d))) • P.u a +
             ((P.z ^ d2 - P.z ^ (d1 + d)) / (1 - P.z ^ (2 * d))) • P.u b)) (P.u b) = 0 := by
  intro P d1 d2 d
  have hd1 : dist a x = d1 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hax)]
  have hd2 : dist x b = d2 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
  have hd : dist a b = d := by
    have hab : a < b := lt_trans hax hxb
    rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]
  have h_sum : d1 + d2 = d := by ring
  have h_pos : 0 < d := sub_pos.mpr (lt_trans hax hxb)
  exact ExponentialCovarianceProcess.bilateral_orthogonality P a x b d1 d2 d hd1 hd2 hd h_sum h_pos

/-- Theorem: Continuous Spatial Projection Orthogonality for arbitrary covariance kernel K.
    Directly specializes the unified metric-space generalized bilateral orthogonality theorem. -/
theorem generalized_continuous_bilateral_orthogonality (u : ℝ → E) (C0 : ℝ) (K : ℝ → ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * K |x - y|) (hC0 : 0 < C0) (hK0 : K 0 = 1)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) (h_denom : 1 - (K (b - a))^2 ≠ 0) :
    let P := continuous_to_generalized_unified u C0 K h_cov hC0 hK0
    let d1 := x - a
    let d2 := b - x
    let d := b - a
    let denom := 1 - (P.K d)^2
    let β1 := (P.K d1 - P.K d2 * P.K d) / denom
    let β2 := (P.K d2 - P.K d1 * P.K d) / denom
    inner ℝ (P.u x - (β1 • P.u a + β2 • P.u b)) (P.u a) = 0 ∧
    inner ℝ (P.u x - (β1 • P.u a + β2 • P.u b)) (P.u b) = 0 := by
  intro P d1 d2 d denom β1 β2
  have hd1 : dist a x = d1 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hax)]
  have hd2 : dist x b = d2 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
  have hd : dist a b = d := by
    have hab : a < b := lt_trans hax hxb
    rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]
  exact GeneralizedCovarianceProcess.generalized_bilateral_orthogonality P a x b d1 d2 d hd1 hd2 hd h_denom

/-- Theorem: The minimum continuous Bilateral Prediction Error (conditional variance).
    Proven as a direct specialization of the unified bilateral optimal MSE theorem. -/
theorem continuous_bilateral_optimal_mse (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * z ^ |x - y|) (hz0 : 0 < z) (hz1 : z < 1) (hC0 : 0 < C0)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) :
    let P := continuous_to_unified u C0 z h_cov hC0 hz0 hz1
    ‖P.u x - (((P.z ^ (x - a) - P.z ^ ((b - x) + (b - a))) / (1 - P.z ^ (2 * (b - a)))) • P.u a +
             ((P.z ^ (b - x) - P.z ^ ((x - a) + (b - a))) / (1 - P.z ^ (2 * (b - a)))) • P.u b)‖^2 =
    P.C0 * ((1 - P.z ^ (2 * (x - a)) - P.z ^ (2 * (b - x)) + P.z ^ (2 * (b - a))) / (1 - P.z ^ (2 * (b - a)))) := by
  intro P
  let d1 := x - a
  let d2 := b - x
  let d := b - a
  have hd1 : dist a x = d1 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hax)]
  have hd2 : dist x b = d2 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
  have hd : dist a b = d := by
    have hab : a < b := lt_trans hax hxb
    rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]
  have h_sum : d1 + d2 = d := by ring
  have h_pos : 0 < d := sub_pos.mpr (lt_trans hax hxb)
  exact ExponentialCovarianceProcess.bilateral_optimal_mse P a x b d1 d2 d hd1 hd2 hd h_sum h_pos

/-- Theorem: Continuous Spatial Projection Optimal MSE for arbitrary covariance kernel K.
    Directly specializes the unified metric-space generalized bilateral optimal MSE theorem. -/
theorem generalized_continuous_bilateral_optimal_mse (u : ℝ → E) (C0 : ℝ) (K : ℝ → ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * K |x - y|) (hC0 : 0 < C0) (hK0 : K 0 = 1)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) (h_denom : 1 - (K (b - a))^2 ≠ 0) :
    let P := continuous_to_generalized_unified u C0 K h_cov hC0 hK0
    let d1 := x - a
    let d2 := b - x
    let d := b - a
    let denom := 1 - (P.K d)^2
    let β1 := (P.K d1 - P.K d2 * P.K d) / denom
    let β2 := (P.K d2 - P.K d1 * P.K d) / denom
    ‖P.u x - (β1 • P.u a + β2 • P.u b)‖^2 =
    C0 * ((1 - (K d)^2 - (K d1)^2 - (K d2)^2 + 2 * K d1 * K d2 * K d) / denom) := by
  intro P d1 d2 d denom β1 β2
  have hd1 : dist a x = d1 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hax)]
  have hd2 : dist x b = d2 := by rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
  have hd : dist a b = d := by
    have hab : a < b := lt_trans hax hxb
    rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]
  exact GeneralizedCovarianceProcess.generalized_bilateral_optimal_mse P a x b d1 d2 d hd1 hd2 hd h_denom

end ContinuousBilateral

#print axioms continuous_unilateral_horizon_limit
#print axioms continuous_bilateral_optimal_mse
#print axioms continuous_bilateral_orthogonality
#print axioms generalized_continuous_unilateral_optimal_mse
#print axioms generalized_continuous_bilateral_optimal_mse
#print axioms generalized_continuous_bilateral_orthogonality
