import entropy.common
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
-- PART 1: Continuous Stationary Covariance Foundation
-- =========================================================================

section ContinuousSetup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The stationary covariance of a continuous spatial process u: ℝ → E satisfies
    the continuous exponential decay model with variance C0 and spatial decay z = e^{-1/ξ}. -/
def ContinuousCovariance (u : ℝ → E) (C0 z : ℝ) : Prop :=
  ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * z ^ |x - y|

/-- Helper Lemma: Norm squared of any continuous node u(x) is exactly equal to C0. -/
lemma continuous_norm_sq (u : ℝ → E) (C0 z : ℝ) (h_cov : ContinuousCovariance u C0 z) (x : ℝ) :
    ‖u x‖^2 = C0 := by
  have h_inner : ‖u x‖^2 = inner ℝ (u x) (u x) := by rw [sq, ← real_inner_self_eq_norm_mul_norm]
  rw [h_inner, h_cov x x, sub_self, abs_zero, Real.rpow_zero, mul_one]

/-- General Helper Lemma: Expansion of the norm squared of a linear combination in E. -/
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

end ContinuousSetup

-- =========================================================================
-- PART 2: Continuous Unilateral Predictability Horizon
-- =========================================================================

section ContinuousUnilateral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: For a continuous stationary process, the optimal linear predictor at
    distance r ≥ 0 yields the exact MSE function C0 * (1 - z^(2*r)). -/
theorem continuous_unilateral_optimal_mse (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ContinuousCovariance u C0 z) (hz0 : 0 < z) (x y : ℝ) (r : ℝ) (hr : |x - y| = r) :
    let β_opt := z ^ r
    ‖u x - β_opt • u y‖^2 = C0 * (1 - z ^ (2 * r)) := by
  intro β_opt
  rw [norm_sub_smul_sq_real, continuous_norm_sq u C0 z h_cov x, continuous_norm_sq u C0 z h_cov y]
  rw [h_cov x y, hr]
  unfold β_opt
  have h_rpow_mul : z ^ r * z ^ r = z ^ (2 * r) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have h_rpow_sq : (z ^ r) ^ 2 = z ^ (2 * r) := by
    rw [sq, h_rpow_mul]
  have h_algebraic : C0 - 2 * z ^ r * (C0 * z ^ r) + (z ^ r) ^ 2 * C0 =
      C0 - 2 * C0 * (z ^ r * z ^ r) + C0 * (z ^ r) ^ 2 := by ring
  rw [h_algebraic, h_rpow_mul, h_rpow_sq]
  ring

/-- Theorem: Link to the physical predictability scale ξ_abs* defined in common.lean.
    The absolute MSE is bounded by δ if and only if the continuous distance r satisfies r ≤ ξ_abs*. -/
theorem continuous_unilateral_horizon_limit (u : ℝ → E) (C0 z δ r : ℝ)
    (h_cov : ContinuousCovariance u C0 z)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) (hδ0 : 0 < δ) (hδ : δ < C0) (hr : 0 ≤ r) :
    ‖u r - (z ^ r) • u 0‖^2 ≤ δ ↔ r ≤ xi_abs_star C0 z δ := by
  have h_dist : |r - 0| = r := by
    rw [sub_zero, abs_of_nonneg hr]
  rw [continuous_unilateral_optimal_mse u C0 z h_cov hz0 r 0 r h_dist]
  have h_exp_eq : z ^ (2 * r) = exp (2 * r * log z) := by
    rw [Real.rpow_def_of_pos hz0]
    congr 1
    ring
  rw [h_exp_eq]
  exact unilateral_horizon_equivalence C0 z δ r hC0 hz0 hz1 hδ0 hδ

end ContinuousUnilateral

-- =========================================================================
-- PART 3: Continuous Bilateral predictability (Spatial Markov Property)
-- =========================================================================

section ContinuousBilateral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: Continuous Spatial Markov Orthogonality.
    Predicting u(x) from its continuous boundary {u(a), u(b)} with a < x < b.
    The optimal continuous predictor P = β1 • u(a) + β2 • u(b) generates an error
    vector (u(x) - P) that is strictly orthogonal to both boundary generators. -/
theorem continuous_bilateral_orthogonality (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ContinuousCovariance u C0 z) (hz0 : 0 < z) (hz1 : z < 1)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) :
    inner ℝ (u x - (((z ^ (x - a) - z ^ ((b - x) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u a +
             ((z ^ (b - x) - z ^ ((x - a) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u b)) (u a) = 0 ∧
    inner ℝ (u x - (((z ^ (x - a) - z ^ ((b - x) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u a +
             ((z ^ (b - x) - z ^ ((x - a) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u b)) (u b) = 0 := by
  let d1 := x - a
  let d2 := b - x
  let d := b - a
  let denom := 1 - z ^ (2 * d)
  let β1 := (z ^ d1 - z ^ (d2 + d)) / denom
  let β2 := (z ^ d2 - z ^ (d1 + d)) / denom
  let P := β1 • u a + β2 • u b
  change inner ℝ (u x - P) (u a) = 0 ∧ inner ℝ (u x - P) (u b) = 0

  have h_denom_ne : 1 - z ^ (2 * d) ≠ 0 := by
    have hd_pos : 0 < b - a := sub_pos.mpr (lt_trans hax hxb)
    have h_z_2d : z ^ (2 * d) < 1 := by
      rw [Real.rpow_def_of_pos hz0]
      have h_log_neg : log z < 0 := (log_neg_iff hz0).mpr hz1
      have : log z * (2 * d) < 0 := by
        have hd : 0 < d := by dsimp [d]; linarith
        have h2d : 0 < 2 * d := mul_pos (by norm_num) hd
        exact mul_neg_of_neg_of_pos h_log_neg h2d
      exact exp_lt_one_iff.mpr this
    linarith

  have hd_sum : d1 + d2 = d := by
    dsimp [d1, d2, d]; ring
  have h_abs_ax : |x - a| = d1 := by
    dsimp [d1]; rw [abs_of_pos (sub_pos.mpr hax)]
  have h_abs_xa : |a - x| = d1 := by
    rw [abs_sub_comm, h_abs_ax]
  have h_abs_bx : |b - x| = d2 := by
    dsimp [d2]; rw [abs_of_pos (sub_pos.mpr hxb)]
  have h_abs_xb : |x - b| = d2 := by
    rw [abs_sub_comm, h_abs_bx]
  have h_abs_ab : |a - b| = d := by
    dsimp [d]
    have : a < b := lt_trans hax hxb
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr this)]
  have h_abs_ba : |b - a| = d := by
    rw [abs_sub_comm]
    exact h_abs_ab

  constructor
  · simp only [P, inner_sub_left, inner_add_left, real_inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [h_cov x a, h_cov a a, h_cov b a]
    rw [h_abs_ax, sub_self, abs_zero, Real.rpow_zero, mul_one, h_abs_ba]
    have h_pow1 : z ^ d2 * z ^ d = z ^ (d2 + d) := by rw [← Real.rpow_add hz0]
    have h_pow2 : z ^ (d1 + d) * z ^ d = z ^ (d1 + d + d) := by rw [← Real.rpow_add hz0]
    have h_pow3 : z ^ (d1 + 2 * d) = z ^ d1 * z ^ (2 * d) := by rw [← Real.rpow_add hz0]
    have h_eq : d1 + d + d = d1 + 2 * d := by ring
    have h_algebraic : (z ^ d1 - z ^ (d2 + d)) * C0 + (z ^ d2 - z ^ (d1 + d)) * (C0 * z ^ d) =
        C0 * (z ^ d1 - z ^ (d2 + d) + z ^ d2 * z ^ d - z ^ (d1 + d) * z ^ d) := by ring
    have h_add : (z ^ d1 - z ^ (d2 + d)) * C0 + (z ^ d2 - z ^ (d1 + d)) * (C0 * z ^ d) =
        z ^ d1 * (1 - z ^ (2 * d)) * C0 := by
      rw [h_algebraic, h_pow1, h_pow2, h_eq, h_pow3]
      ring
    have h_sum : β1 * C0 + β2 * (C0 * z ^ d) = C0 * z ^ d1 := by
      unfold β1 β2 denom
      have h_calc : (z ^ d1 - z ^ (d2 + d)) / (1 - z ^ (2 * d)) * C0 + (z ^ d2 - z ^ (d1 + d)) / (1 - z ^ (2 * d)) * (C0 * z ^ d) =
          ((z ^ d1 - z ^ (d2 + d)) * C0 + (z ^ d2 - z ^ (d1 + d)) * (C0 * z ^ d)) / (1 - z ^ (2 * d)) := by
        field_simp [h_denom_ne]
      rw [h_calc, h_add]
      field_simp [h_denom_ne]
    rw [h_sum]
    ring

  · simp only [P, inner_sub_left, inner_add_left, real_inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [h_cov x b, h_cov a b, h_cov b b]
    rw [h_abs_xb, h_abs_ab, sub_self, abs_zero, Real.rpow_zero, mul_one]
    have h_pow1' : z ^ d1 * z ^ d = z ^ (d1 + d) := by rw [← Real.rpow_add hz0]
    have h_pow2' : z ^ (d2 + d) * z ^ d = z ^ (d2 + d + d) := by rw [← Real.rpow_add hz0]
    have h_pow3' : z ^ (d2 + 2 * d) = z ^ d2 * z ^ (2 * d) := by rw [← Real.rpow_add hz0]
    have h_eq' : d2 + d + d = d2 + 2 * d := by ring
    have h_algebraic' : (z ^ d1 - z ^ (d2 + d)) * (C0 * z ^ d) + (z ^ d2 - z ^ (d1 + d)) * C0 =
        C0 * (z ^ d1 * z ^ d - z ^ (d2 + d) * z ^ d + z ^ d2 - z ^ (d1 + d)) := by ring
    have h_add : (z ^ d1 - z ^ (d2 + d)) * (C0 * z ^ d) + (z ^ d2 - z ^ (d1 + d)) * C0 =
        z ^ d2 * (1 - z ^ (2 * d)) * C0 := by
      rw [h_algebraic', h_pow1', h_pow2', h_eq', h_pow3']
      ring
    have h_sum2 : β1 * (C0 * z ^ d) + β2 * C0 = C0 * z ^ d2 := by
      unfold β1 β2 denom
      have h_calc : (z ^ d1 - z ^ (d2 + d)) / (1 - z ^ (2 * d)) * (C0 * z ^ d) + (z ^ d2 - z ^ (d1 + d)) / (1 - z ^ (2 * d)) * C0 =
          ((z ^ d1 - z ^ (d2 + d)) * (C0 * z ^ d) + (z ^ d2 - z ^ (d1 + d)) * C0) / (1 - z ^ (2 * d)) := by
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
    rw [← Real.rpow_add hz0];
    congr 1
    ring --here
  have h_pow2 : z ^ d2 * z ^ d2 = z ^ (2 * d2) := by
    rw [← Real.rpow_add hz0];
    congr 1
    ring --here
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

/-- Theorem: The minimum continuous Bilateral Prediction Error (conditional variance).
    Evaluating the error vector norm squared under the spatial Markov predictor matches
    the analytical bound C0 * (1 - z^(2*d1) - z^(2*d2) + z^(2*d)) / (1 - z^(2*d)). -/
theorem continuous_bilateral_optimal_mse (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ContinuousCovariance u C0 z) (hz0 : 0 < z) (hz1 : z < 1)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) :
    ‖u x - (((z ^ (x - a) - z ^ ((b - x) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u a +
             ((z ^ (b - x) - z ^ ((x - a) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u b)‖^2 =
    C0 * ((1 - z ^ (2 * (x - a)) - z ^ (2 * (b - x)) + z ^ (2 * (b - a))) / (1 - z ^ (2 * (b - a)))) := by
  let d1 := x - a
  let d2 := b - x
  let d := b - a
  let denom := 1 - z ^ (2 * d)
  let β1 := (z ^ d1 - z ^ (d2 + d)) / denom
  let β2 := (z ^ d2 - z ^ (d1 + d)) / denom
  let P := β1 • u a + β2 • u b
  change ‖u x - P‖^2 = C0 * ((1 - z ^ (2 * d1) - z ^ (2 * d2) + z ^ (2 * d)) / denom)

  have h_orth := continuous_bilateral_orthogonality u C0 z h_cov hz0 hz1 a x b hax hxb
  have h_orth_a : inner ℝ (u x - P) (u a) = 0 := h_orth.left
  have h_orth_b : inner ℝ (u x - P) (u b) = 0 := h_orth.right

  have h_orth_P : inner ℝ (u x - P) P = 0 := by
    unfold P
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    rw [h_orth_a, h_orth_b, mul_zero, mul_zero, add_zero]

  have h_norm_sq : ‖u x - P‖^2 = inner ℝ (u x - P) (u x - P) := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have h_split : inner ℝ (u x - P) (u x - P) = inner ℝ (u x - P) (u x) - inner ℝ (u x - P) P := by
    rw [inner_sub_right]
  rw [h_norm_sq, h_split, h_orth_P, sub_zero]

  have h_inner_ux : inner ℝ (u x - P) (u x) = inner ℝ (u x) (u x) - inner ℝ P (u x) := by
    rw [inner_sub_left]
  rw [h_inner_ux]

  have h_self : inner ℝ (u x) (u x) = C0 := by
    rw [real_inner_self_eq_norm_mul_norm, ← sq, continuous_norm_sq u C0 z h_cov x]
  rw [h_self]

  have h_P_ux : inner ℝ P (u x) = β1 * inner ℝ (u a) (u x) + β2 * inner ℝ (u b) (u x) := by
    unfold P
    rw [inner_add_left, inner_smul_left, inner_smul_left, starRingEnd_apply, starRingEnd_apply, star_trivial, star_trivial]
  rw [h_P_ux]

  have h_abs_xa : |a - x| = d1 := by
    unfold d1; rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hax)]
  have h_abs_xb : |b - x| = d2 := by
    unfold d2; rw [abs_of_pos (sub_pos.mpr hxb)]
  rw [h_cov a x, h_cov b x, h_abs_xa, h_abs_xb]

  have h_denom_ne : 1 - z ^ (2 * d) ≠ 0 := by
    have hd_pos : 0 < b - a := sub_pos.mpr (lt_trans hax hxb)
    have h_z_2d : z ^ (2 * d) < 1 := by
      rw [Real.rpow_def_of_pos hz0]
      have h_log_neg : log z < 0 := (log_neg_iff hz0).mpr hz1
      have : log z * (2 * d) < 0 := by
        have hd : 0 < d := by dsimp [d]; linarith
        have h2d : 0 < 2 * d := mul_pos (by norm_num) hd
        exact mul_neg_of_neg_of_pos h_log_neg h2d
      exact exp_lt_one_iff.mpr this
    linarith

  have h_goal_prep : C0 - (β1 * (C0 * z ^ d1) + β2 * (C0 * z ^ d2)) =
      C0 * (1 - (z ^ d1 * (z ^ d1 - z ^ (d2 + d)) + z ^ d2 * (z ^ d2 - z ^ (d1 + d))) / denom) := by
    unfold β1 β2
    ring

  rw [h_goal_prep]
  have h_sum : d1 + d2 = d := by unfold d1 d2 d; ring
  rw [helper_power_relation z d1 d2 d hz0 h_sum]
  dsimp [denom]
  field_simp [h_denom_ne]
  ring

end ContinuousBilateral
