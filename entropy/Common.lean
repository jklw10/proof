import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real
open RealInnerProductSpace

-- =========================================================================
-- PART 1: The Unified Covariance Structure (Legacy Exponential)
-- =========================================================================

/-- A unified wide-sense stationary process with exponential covariance.
    T is any metric space (e.g., ℝ, ℤ, or a network graph).
    E is a Hilbert space representing the space of random variables. -/
structure ExponentialCovarianceProcess (T : Type*) [MetricSpace T]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  u : T → E
  C0 : ℝ
  z : ℝ
  hC0 : 0 < C0
  hz0 : 0 < z
  hz1 : z < 1
  cov : ∀ x y : T, inner ℝ (u x) (u y) = C0 * z ^ (dist x y)

namespace ExponentialCovarianceProcess

variable {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm squared of any node u(x) in the process is exactly C0. -/
lemma norm_sq_eq (P : ExponentialCovarianceProcess T E) (x : T) :
    ‖P.u x‖^2 = P.C0 := by
  have h_inner : ‖P.u x‖^2 = inner ℝ (P.u x) (P.u x) := by rw [sq, ← real_inner_self_eq_norm_mul_norm]
  rw [h_inner, P.cov x x, dist_self, Real.rpow_zero, mul_one]

/-- General algebraic expansion of a linear combination's norm in a Hilbert space. -/
lemma norm_sub_smul_sq_real (x y : E) (β : ℝ) :
    ‖y - β • x‖^2 = ‖y‖^2 - 2 * β * inner ℝ y x + β^2 * ‖x‖^2 := by
  have h_sq : ‖y - β • x‖^2 = inner ℝ (y - β • x) (y - β • x) := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  rw [h_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm, ← sq, ← sq]
  rw [real_inner_comm x y]
  ring

-- =========================================================================
-- PART 2: Legacy Unilateral Predictability
-- =========================================================================

/-- Theorem: Unified Unilateral Predictability.
    For any separation d = dist(x, y), the optimal linear predictor
    at distance d yields an MSE of exactly C0 * (1 - z^(2*d)). -/
theorem unilateral_optimal_mse (P : ExponentialCovarianceProcess T E) (x y : T) (d : ℝ) (hd : dist x y = d) :
    let β_opt := P.z ^ d
    ‖P.u x - β_opt • P.u y‖^2 = P.C0 * (1 - P.z ^ (2 * d)) := by
  intro β_opt
  rw [norm_sub_smul_sq_real, norm_sq_eq P x, norm_sq_eq P y]
  rw [P.cov x y, hd]
  unfold β_opt
  have h_rpow_mul : P.z ^ d * P.z ^ d = P.z ^ (2 * d) := by
    rw [← Real.rpow_add P.hz0]
    congr 1
    ring
  have h_rpow_sq : (P.z ^ d) ^ 2 = P.z ^ (2 * d) := by
    rw [sq, h_rpow_mul]
  have h_algebraic : P.C0 - 2 * P.z ^ d * (P.C0 * P.z ^ d) + (P.z ^ d) ^ 2 * P.C0 =
      P.C0 - 2 * P.C0 * (P.z ^ d * P.z ^ d) + P.C0 * (P.z ^ d) ^ 2 := by ring
  rw [h_algebraic, h_rpow_mul, h_rpow_sq]
  ring

-- =========================================================================
-- PART 3: Legacy Bilateral Predictability & Spatial Markov Orthogonality
-- =========================================================================

/-- Theorem: Unified Spatial Markov Orthogonality.
    Predicting u(x) from its boundary {u(a), u(b)} where x lies along a metric geodesic path. -/
theorem bilateral_orthogonality (P : ExponentialCovarianceProcess T E) (a x b : T)
    (d1 d2 d : ℝ) (hd1 : dist a x = d1) (hd2 : dist x b = d2) (hd : dist a b = d)
    (h_sum : d1 + d2 = d) (h_pos : 0 < d) :
    let denom := 1 - P.z ^ (2 * d)
    let β1 := (P.z ^ d1 - P.z ^ (d2 + d)) / denom
    let β2 := (P.z ^ d2 - P.z ^ (d1 + d)) / denom
    let Pred := β1 • P.u a + β2 • P.u b
    inner ℝ (P.u x - Pred) (P.u a) = 0 ∧ inner ℝ (P.u x - Pred) (P.u b) = 0 := by
  intro denom β1 β2 Pred

  have h_denom_ne : 1 - P.z ^ (2 * d) ≠ 0 := by
    have h_z_2d : P.z ^ (2 * d) < 1 := by
      rw [Real.rpow_def_of_pos P.hz0]
      have h_log_neg : log P.z < 0 := (log_neg_iff P.hz0).mpr P.hz1
      have : log P.z * (2 * d) < 0 := mul_neg_of_neg_of_pos h_log_neg (by linarith)
      exact exp_lt_one_iff.mpr this
    linarith

  have h_dist_xa : dist x a = d1 := by rw [dist_comm, hd1]
  have h_dist_xb : dist x b = d2 := hd2
  have h_dist_ab : dist a b = d := hd
  have h_dist_ba : dist b a = d := by rw [dist_comm, hd]

  constructor
  · simp only [Pred, inner_sub_left, inner_add_left, real_inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [P.cov x a, P.cov a a, P.cov b a]
    rw [h_dist_xa, dist_self, Real.rpow_zero, mul_one, h_dist_ba]
    have h_pow1 : P.z ^ d2 * P.z ^ d = P.z ^ (d2 + d) := by rw [← Real.rpow_add P.hz0]
    have h_pow2 : P.z ^ (d1 + d) * P.z ^ d = P.z ^ (d1 + d + d) := by rw [← Real.rpow_add P.hz0]
    have h_pow3 : P.z ^ (d1 + 2 * d) = P.z ^ d1 * P.z ^ (2 * d) := by rw [← Real.rpow_add P.hz0]
    have h_eq : d1 + d + d = d1 + 2 * d := by ring
    have h_algebraic : (P.z ^ d1 - P.z ^ (d2 + d)) * P.C0 + (P.z ^ d2 - P.z ^ (d1 + d)) * (P.C0 * P.z ^ d) =
        P.C0 * (P.z ^ d1 - P.z ^ (d2 + d) + P.z ^ d2 * P.z ^ d - P.z ^ (d1 + d) * P.z ^ d) := by ring
    have h_add : (P.z ^ d1 - P.z ^ (d2 + d)) * P.C0 + (P.z ^ d2 - P.z ^ (d1 + d)) * (P.C0 * P.z ^ d) =
        P.z ^ d1 * (1 - P.z ^ (2 * d)) * P.C0 := by
      rw [h_algebraic, h_pow1, h_pow2, h_eq, h_pow3]
      ring
    have h_sum_coeffs : β1 * P.C0 + β2 * (P.C0 * P.z ^ d) = P.C0 * P.z ^ d1 := by
      unfold β1 β2 denom
      have h_calc : (P.z ^ d1 - P.z ^ (d2 + d)) / (1 - P.z ^ (2 * d)) * P.C0 + (P.z ^ d2 - P.z ^ (d1 + d)) / (1 - P.z ^ (2 * d)) * (P.C0 * P.z ^ d) =
          ((P.z ^ d1 - P.z ^ (d2 + d)) * P.C0 + (P.z ^ d2 - P.z ^ (d1 + d)) * (P.C0 * P.z ^ d)) / (1 - P.z ^ (2 * d)) := by
        field_simp [h_denom_ne]
      rw [h_calc, h_add]
      field_simp [h_denom_ne]
    rw [h_sum_coeffs]
    ring

  · simp only [Pred, inner_sub_left, inner_add_left, real_inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [P.cov x b, P.cov a b, P.cov b b]
    rw [h_dist_xb, h_dist_ab, dist_self, Real.rpow_zero, mul_one]
    have h_pow1' : P.z ^ d1 * P.z ^ d = P.z ^ (d1 + d) := by rw [← Real.rpow_add P.hz0]
    have h_pow2' : P.z ^ (d2 + d) * P.z ^ d = P.z ^ (d2 + d + d) := by rw [← Real.rpow_add P.hz0]
    have h_pow3' : P.z ^ (d2 + 2 * d) = P.z ^ d2 * P.z ^ (2 * d) := by rw [← Real.rpow_add P.hz0]
    have h_eq' : d2 + d + d = d2 + 2 * d := by ring
    have h_algebraic' : (P.z ^ d1 - P.z ^ (d2 + d)) * (P.C0 * P.z ^ d) + (P.z ^ d2 - P.z ^ (d1 + d)) * P.C0 =
        P.C0 * (P.z ^ d1 * P.z ^ d - P.z ^ (d2 + d) * P.z ^ d + P.z ^ d2 - P.z ^ (d1 + d)) := by ring
    have h_add : (P.z ^ d1 - P.z ^ (d2 + d)) * (P.C0 * P.z ^ d) + (P.z ^ d2 - P.z ^ (d1 + d)) * P.C0 =
        P.z ^ d2 * (1 - P.z ^ (2 * d)) * P.C0 := by
      rw [h_algebraic', h_pow1', h_pow2', h_eq', h_pow3']
      ring
    have h_sum2 : β1 * (P.C0 * P.z ^ d) + β2 * P.C0 = P.C0 * P.z ^ d2 := by
      unfold β1 β2 denom
      have h_calc : (P.z ^ d1 - P.z ^ (d2 + d)) / (1 - P.z ^ (2 * d)) * (P.C0 * P.z ^ d) + (P.z ^ d2 - P.z ^ (d1 + d)) / (1 - P.z ^ (2 * d)) * P.C0 =
          ((P.z ^ d1 - P.z ^ (d2 + d)) * (P.C0 * P.z ^ d) + (P.z ^ d2 - P.z ^ (d1 + d)) * P.C0) / (1 - P.z ^ (2 * d)) := by
        field_simp [h_denom_ne]
      rw [h_calc, h_add]
      field_simp [h_denom_ne]
    rw [h_sum2]
    ring

/-- Helper Lemma: Simplifies the algebraic expansion of continuous bilateral power products. -/
lemma helper_power_relation (z d1 d2 d : ℝ) (hz0 : 0 < z) (h_sum : d1 + d2 = d) :
    z ^ d1 * (z ^ d1 - z ^ (d2 + d)) + z ^ d2 * (z ^ d2 - z ^ (d1 + d)) =
    z ^ (2 * d1) + z ^ (2 * d2) - 2 * z ^ (2 * d) := by
  have h_pow1 : z ^ d1 * z ^ d1 = z ^ (2 * d1) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have h_pow2 : z ^ d2 * z ^ d2 = z ^ (2 * d2) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have h_pow3 : z ^ d1 * z ^ (d2 + d) = z ^ (2 * d) := by
    rw [← Real.rpow_add hz0]
    congr 1
    linarith [h_sum]
  have h_pow4 : z ^ d2 * z ^ (d1 + d) = z ^ (2 * d) := by
    rw [← Real.rpow_add hz0]
    congr 1
    linarith [h_sum]
  have h_algebraic : z ^ d1 * (z ^ d1 - z ^ (d2 + d)) + z ^ d2 * (z ^ d2 - z ^ (d1 + d)) =
      (z ^ d1 * z ^ d1) - (z ^ d1 * z ^ (d2 + d)) + (z ^ d2 * z ^ d2) - (z ^ d2 * z ^ (d1 + d)) := by
    ring
  rw [h_algebraic, h_pow1, h_pow2, h_pow3, h_pow4]
  ring

/-- Theorem: Unified Bilateral Prediction Error. -/
theorem bilateral_optimal_mse (P : ExponentialCovarianceProcess T E) (a x b : T)
    (d1 d2 d : ℝ) (hd1 : dist a x = d1) (hd2 : dist x b = d2) (hd : dist a b = d)
    (h_sum : d1 + d2 = d) (h_pos : 0 < d) :
    let denom := 1 - P.z ^ (2 * d)
    let β1 := (P.z ^ d1 - P.z ^ (d2 + d)) / denom
    let β2 := (P.z ^ d2 - P.z ^ (d1 + d)) / denom
    let Pred := β1 • P.u a + β2 • P.u b
    ‖P.u x - Pred‖^2 = P.C0 * ((1 - P.z ^ (2 * d1) - P.z ^ (2 * d2) + P.z ^ (2 * d)) / denom) := by
  let denom := 1 - P.z ^ (2 * d)
  let β1 := (P.z ^ d1 - P.z ^ (d2 + d)) / denom
  let β2 := (P.z ^ d2 - P.z ^ (d1 + d)) / denom
  let Pred := β1 • P.u a + β2 • P.u b
  intro denom' β1' β2' Pred'
  change ‖P.u x - Pred‖^2 = P.C0 * ((1 - P.z ^ (2 * d1) - P.z ^ (2 * d2) + P.z ^ (2 * d)) / denom)

  have h_orth := bilateral_orthogonality P a x b d1 d2 d hd1 hd2 hd h_sum h_pos
  have h_orth_a : inner ℝ (P.u x - Pred) (P.u a) = 0 := h_orth.left
  have h_orth_b : inner ℝ (P.u x - Pred) (P.u b) = 0 := h_orth.right

  have h_orth_P : inner ℝ (P.u x - Pred) Pred = 0 := by
    unfold Pred
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    rw [h_orth_a, h_orth_b, mul_zero, mul_zero, add_zero]

  have h_norm_sq : ‖P.u x - Pred‖^2 = inner ℝ (P.u x - Pred) (P.u x - Pred) := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have h_split : inner ℝ (P.u x - Pred) (P.u x - Pred) = inner ℝ (P.u x - Pred) (P.u x) - inner ℝ (P.u x - Pred) Pred := by
    rw [inner_sub_right]
  rw [h_norm_sq, h_split, h_orth_P, sub_zero]

  have h_inner_ux : inner ℝ (P.u x - Pred) (P.u x) = inner ℝ (P.u x) (P.u x) - inner ℝ Pred (P.u x) := by
    rw [inner_sub_left]
  rw [h_inner_ux]

  have h_self : inner ℝ (P.u x) (P.u x) = P.C0 := by
    rw [real_inner_self_eq_norm_mul_norm, ← sq, norm_sq_eq P x]
  rw [h_self]

  have h_P_ux : inner ℝ Pred (P.u x) = β1 * inner ℝ (P.u a) (P.u x) + β2 * inner ℝ (P.u b) (P.u x) := by
    unfold Pred
    rw [inner_add_left, inner_smul_left, inner_smul_left, starRingEnd_apply, starRingEnd_apply, star_trivial, star_trivial]
  rw [h_P_ux]

  have h_abs_xa : dist a x = d1 := hd1
  have h_abs_xb : dist b x = d2 := by rw [dist_comm, hd2]
  rw [P.cov a x, P.cov b x, h_abs_xa, h_abs_xb]

  have h_denom_ne : 1 - P.z ^ (2 * d) ≠ 0 := by
    have h_z_2d : P.z ^ (2 * d) < 1 := by
      rw [Real.rpow_def_of_pos P.hz0]
      have h_log_neg : log P.z < 0 := (log_neg_iff P.hz0).mpr P.hz1
      have : log P.z * (2 * d) < 0 := mul_neg_of_neg_of_pos h_log_neg (by linarith)
      exact exp_lt_one_iff.mpr this
    linarith

  have h_goal_prep : P.C0 - (β1 * (P.C0 * P.z ^ d1) + β2 * (P.C0 * P.z ^ d2)) =
      P.C0 * (1 - (P.z ^ d1 * (P.z ^ d1 - P.z ^ (d2 + d)) + P.z ^ d2 * (P.z ^ d2 - P.z ^ (d1 + d))) / denom) := by
    unfold β1 β2 denom
    ring

  rw [h_goal_prep]
  rw [helper_power_relation P.z d1 d2 d P.hz0 h_sum]
  dsimp [denom]
  field_simp [h_denom_ne]
  ring

end ExponentialCovarianceProcess

-- =========================================================================
-- PART 4: The Generalized Covariance Process (GCP)
-- =========================================================================

/-- A generalized wide-sense stationary process with an arbitrary radial covariance kernel K.
    Does not require exponential or Markovian decay. -/
structure GeneralizedCovarianceProcess (T : Type*) [MetricSpace T]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  u : T → E
  C0 : ℝ
  K : ℝ → ℝ             -- The radial basis covariance kernel K(d)
  hC0 : 0 < C0
  hK0 : K 0 = 1         -- Normalization condition at dist = 0
  cov : ∀ x y : T, inner ℝ (u x) (u y) = C0 * K (dist x y)

namespace GeneralizedCovarianceProcess

variable {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm squared of any node in the generalized process is exactly C0. -/
lemma norm_sq_eq (P : GeneralizedCovarianceProcess T E) (x : T) :
    ‖P.u x‖^2 = P.C0 := by
  have h_inner : ‖P.u x‖^2 = inner ℝ (P.u x) (P.u x) := by rw [sq, ← real_inner_self_eq_norm_mul_norm]
  rw [h_inner, P.cov x x, dist_self, P.hK0, mul_one]

-- Reuse the general algebraic norm expansion helper
lemma norm_sub_smul_sq_real (x y : E) (β : ℝ) :
    ‖y - β • x‖^2 = ‖y‖^2 - 2 * β * inner ℝ y x + β^2 * ‖x‖^2 :=
  ExponentialCovarianceProcess.norm_sub_smul_sq_real x y β

-- =========================================================================
-- PART 5: Generalized Unilateral Predictability
-- =========================================================================

/-- Theorem: Generalized Unilateral Predictability.
    For any arbitrary radial covariance kernel K, the optimal predictor at distance d
    yields an MSE of exactly C0 * (1 - K(d)^2). -/
theorem generalized_unilateral_optimal_mse (P : GeneralizedCovarianceProcess T E) (x y : T) (d : ℝ) (hd : dist x y = d) :
    let β_opt := P.K d
    ‖P.u x - β_opt • P.u y‖^2 = P.C0 * (1 - (P.K d) ^ 2) := by
  intro β_opt
  rw [norm_sub_smul_sq_real, norm_sq_eq P x, norm_sq_eq P y]
  rw [P.cov x y, hd]
  unfold β_opt
  ring

-- =========================================================================
-- PART 6: Generalized Bilateral Predictability & Projection Orthogonality
-- =========================================================================

/-- Theorem: Generalized Bilateral Orthogonality.
    Predicting u(x) from its boundary {u(a), u(b)} for ANY general covariance kernel K.
    The projection coefficients β1 and β2 are derived by solving the 2x2 normal equations.
    The error is proved orthogonal to both boundary generators without Markovian assumptions. -/
theorem generalized_bilateral_orthogonality (P : GeneralizedCovarianceProcess T E) (a x b : T)
    (d1 d2 d : ℝ) (hd1 : dist a x = d1) (hd2 : dist x b = d2) (hd : dist a b = d)
    (h_denom : 1 - (P.K d)^2 ≠ 0) :
    let denom := 1 - (P.K d)^2
    let β1 := (P.K d1 - P.K d2 * P.K d) / denom
    let β2 := (P.K d2 - P.K d1 * P.K d) / denom
    let Pred := β1 • P.u a + β2 • P.u b
    inner ℝ (P.u x - Pred) (P.u a) = 0 ∧ inner ℝ (P.u x - Pred) (P.u b) = 0 := by
  intro denom β1 β2 Pred
  constructor
  · simp only [Pred, inner_sub_left, inner_add_left, real_inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [P.cov x a, P.cov a a, P.cov b a]
    rw [dist_comm x a, hd1, dist_self, P.hK0, mul_one, dist_comm b a, hd]
    have h_sum : β1 * P.C0 + β2 * (P.C0 * P.K d) = P.C0 * P.K d1 := by
      unfold β1 β2 denom
      have h_calc : (P.K d1 - P.K d2 * P.K d) / (1 - (P.K d)^2) * P.C0 + (P.K d2 - P.K d1 * P.K d) / (1 - (P.K d)^2) * (P.C0 * P.K d) =
          P.C0 * ((P.K d1 - P.K d2 * P.K d + (P.K d2 - P.K d1 * P.K d) * P.K d) / (1 - (P.K d)^2)) := by ring
      rw [h_calc]
      have h_simpl : P.K d1 - P.K d2 * P.K d + (P.K d2 - P.K d1 * P.K d) * P.K d = P.K d1 * (1 - (P.K d)^2) := by ring
      rw [h_simpl]
      rw [mul_div_cancel_right₀ _ h_denom]
    rw [h_sum]
    ring

  · simp only [Pred, inner_sub_left, inner_add_left, real_inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [P.cov x b, P.cov a b, P.cov b b]
    rw [hd2, hd, dist_self, P.hK0, mul_one]
    have h_sum2 : β1 * (P.C0 * P.K d) + β2 * P.C0 = P.C0 * P.K d2 := by
      unfold β1 β2 denom
      have h_calc : (P.K d1 - P.K d2 * P.K d) / (1 - (P.K d)^2) * (P.C0 * P.K d) + (P.K d2 - P.K d1 * P.K d) / (1 - (P.K d)^2) * P.C0 =
          P.C0 * (((P.K d1 - P.K d2 * P.K d) * P.K d + (P.K d2 - P.K d1 * P.K d)) / (1 - (P.K d)^2)) := by ring
      rw [h_calc]
      have h_simpl : (P.K d1 - P.K d2 * P.K d) * P.K d + (P.K d2 - P.K d1 * P.K d) = P.K d2 * (1 - (P.K d)^2) := by ring
      rw [h_simpl]
      rw [mul_div_cancel_right₀ _ h_denom]
    rw [h_sum2]
    ring
/-- Theorem: Generalized Bilateral Prediction Error (Conditional Variance).
    Evaluates the exact minimum prediction MSE under any arbitrary radial basis kernel K.
    Reduces precisely to the legacy Markovian form when K is exponential. -/
theorem generalized_bilateral_optimal_mse (P : GeneralizedCovarianceProcess T E) (a x b : T)
    (d1 d2 d : ℝ) (hd1 : dist a x = d1) (hd2 : dist x b = d2) (hd : dist a b = d)
    (h_denom : 1 - (P.K d)^2 ≠ 0) :
    let denom := 1 - (P.K d)^2
    let β1 := (P.K d1 - P.K d2 * P.K d) / denom
    let β2 := (P.K d2 - P.K d1 * P.K d) / denom
    let Pred := β1 • P.u a + β2 • P.u b
    ‖P.u x - Pred‖^2 = P.C0 * ((1 - (P.K d)^2 - (P.K d1)^2 - (P.K d2)^2 + 2 * P.K d1 * P.K d2 * P.K d) / denom) := by
  let denom := 1 - (P.K d)^2
  let β1 := (P.K d1 - P.K d2 * P.K d) / denom
  let β2 := (P.K d2 - P.K d1 * P.K d) / denom
  let Pred := β1 • P.u a + β2 • P.u b
  intro denom' β1' β2' Pred'
  change ‖P.u x - Pred‖^2 = P.C0 * ((1 - (P.K d)^2 - (P.K d1)^2 - (P.K d2)^2 + 2 * P.K d1 * P.K d2 * P.K d) / denom)

  have h_orth := generalized_bilateral_orthogonality P a x b d1 d2 d hd1 hd2 hd h_denom
  have h_orth_a : inner ℝ (P.u x - Pred) (P.u a) = 0 := h_orth.left
  have h_orth_b : inner ℝ (P.u x - Pred) (P.u b) = 0 := h_orth.right

  have h_orth_P : inner ℝ (P.u x - Pred) Pred = 0 := by
    unfold Pred
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    rw [h_orth_a, h_orth_b, mul_zero, mul_zero, add_zero]

  have h_norm_sq : ‖P.u x - Pred‖^2 = inner ℝ (P.u x - Pred) (P.u x - Pred) := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have h_split : inner ℝ (P.u x - Pred) (P.u x - Pred) = inner ℝ (P.u x - Pred) (P.u x) - inner ℝ (P.u x - Pred) Pred := by
    rw [inner_sub_right]
  rw [h_norm_sq, h_split, h_orth_P, sub_zero]

  have h_inner_ux : inner ℝ (P.u x - Pred) (P.u x) = inner ℝ (P.u x) (P.u x) - inner ℝ Pred (P.u x) := by
    rw [inner_sub_left]
  rw [h_inner_ux]

  have h_self : inner ℝ (P.u x) (P.u x) = P.C0 := by
    rw [real_inner_self_eq_norm_mul_norm, ← sq, norm_sq_eq P x]
  rw [h_self]

  have h_P_ux : inner ℝ Pred (P.u x) = β1 * inner ℝ (P.u a) (P.u x) + β2 * inner ℝ (P.u b) (P.u x) := by
    unfold Pred
    rw [inner_add_left, inner_smul_left, inner_smul_left, starRingEnd_apply, starRingEnd_apply, star_trivial, star_trivial]
  rw [h_P_ux]

  rw [P.cov a x, P.cov b x]
  rw [hd1, dist_comm b x, hd2]

  unfold β1 β2 denom
  field_simp [h_denom]
  ring
end GeneralizedCovarianceProcess

-- =========================================================================
-- PART 7: Scale Parameters (Exponential Horizon Equivalence)
-- =========================================================================

/-- Unilateral predictability scale parameter `xi`. -/
def xi (z : ℝ) : ℝ := -1 / Real.log z

/-- The unilateral predictability scale xi_abs*. -/
def xi_abs_star (C0 z δ : ℝ) : ℝ := xi z / 2 * Real.log (1 / (1 - δ / C0))

lemma xi_pos (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) : 0 < xi z := by
  have hz_lt : log z < 0 := (Real.log_neg_iff hz0).mpr hz1
  exact div_pos_of_neg_of_neg (by linarith) hz_lt

/-- Theorem: The physical equivalent matching the discrete Unilateral Predictability Horizon limit. -/
theorem unilateral_horizon_equivalence (C0 z δ r : ℝ)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) (hδ0 : 0 < δ) (hδ : δ < C0) :
    C0 * (1 - exp (2 * r * log z)) ≤ δ ↔ r ≤ xi_abs_star C0 z δ := by
  have h_log_z_neg : log z < 0 := (log_neg_iff hz0).mpr hz1
  have h_denom_pos : 0 < 1 - δ / C0 := by
    have h_div : δ / C0 < 1 := (div_lt_one hC0).mpr hδ
    linarith
  unfold xi_abs_star xi
  have h1 : C0 * (1 - exp (2 * r * log z)) ≤ δ ↔ 1 - exp (2 * r * log z) ≤ δ / C0 := by
    rw [mul_comm, le_div_iff₀ hC0]
  have h2 : 1 - exp (2 * r * log z) ≤ δ / C0 ↔ 1 - δ / C0 ≤ exp (2 * r * log z) := by
    constructor <;> intro h <;> linarith
  have h3 : 1 - δ / C0 ≤ exp (2 * r * log z) ↔ log (1 - δ / C0) ≤ 2 * r * log z := by
    rw [← Real.log_le_log_iff h_denom_pos (exp_pos _), log_exp]
  have h4 : log (1 - δ / C0) ≤ 2 * r * log z ↔ r ≤ log (1 - δ / C0) / (2 * log z) := by
    have h_2logz_neg : 2 * log z < 0 := mul_neg_of_pos_of_neg (by linarith) h_log_z_neg
    rw [le_div_iff_of_neg h_2logz_neg]
    have h_mul_comm : r * (2 * log z) = 2 * r * log z := by ring
    rw [h_mul_comm]
  have h5 : log (1 - δ / C0) / (2 * log z) = -1 / (2 * log z) * log (1 / (1 - δ / C0)) := by
    rw [one_div, Real.log_inv]
    ring
  rw [h1, h2, h3, h4, h5]
  have h_coeff : -1 / (2 * log z) = -1 / log z / 2 := by
    have h_logz_ne : log z ≠ 0 := ne_of_lt h_log_z_neg
    field_simp
  rw [h_coeff]
