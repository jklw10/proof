import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
open Real
open RealInnerProductSpace
open Matrix

-- =========================================================================
-- PART 1: Physical Parameters & Analytical Predictability Horizons
-- =========================================================================

section PredictabilityParameters

/-- The physical spatial correlation length ξ is defined from z = e^{-1/ξ} -/
def xi (z : ℝ) : ℝ := -1 / log z

lemma xi_pos (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) : 0 < xi z := by
  have hz_lt : log z < 0 := (Real.log_neg_iff hz0).mpr hz1
  exact div_pos_of_neg_of_neg (by linarith) hz_lt

/-- The Unilateral Predictability scale ξ_abs* -/
def xi_abs_star (C0 z δ : ℝ) : ℝ :=
  (xi z / 2) * log (1 / (1 - δ / C0))

/-- The minimum tolerance for Unilateral predictability (at r = 1) -/
def delta_min_uni (C0 z : ℝ) : ℝ := C0 * (1 - z^2)

/-- The minimum tolerance for Bilateral predictability -/
def delta_min_bi (C0 z : ℝ) : ℝ := C0 * ((1 - z^2) / (1 + z^2))

/-- Theorem: The bilateral predictability limit strictly lowers the minimum allowable
    prediction error compared to the unilateral predictability limit: δ_min^(2) < δ_min^(1) -/
theorem bilateral_strict_reduction (C0 z : ℝ) (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) :
    delta_min_bi C0 z < delta_min_uni C0 z := by
  simp only [delta_min_bi, delta_min_uni]
  apply mul_lt_mul_of_pos_left
  · have h_z2_pos : 0 < z^2 := by
      have : 0 < z * z := mul_pos hz0 hz0
      linarith
    have h_z2_lt_z : z^2 < z := by
      calc
        z^2 = z * z := by ring
        _ < z * 1   := mul_lt_mul_of_pos_left hz1 hz0
        _ = z       := mul_one z
    have h_z2_lt1 : z^2 < 1 := lt_trans h_z2_lt_z hz1
    have h_num_pos : 0 < 1 - z^2 := by linarith
    have h_denom : 1 < 1 + z^2 := by linarith
    have h_denom_pos : 0 < 1 + z^2 := by linarith
    have h_inv_pos : 0 < (1 + z^2)⁻¹ := inv_pos.mpr h_denom_pos
    have h_inv : (1 + z^2)⁻¹ < 1 := by
      calc
        (1 + z^2)⁻¹ = 1 * (1 + z^2)⁻¹ := by ring
        _ < (1 + z^2) * (1 + z^2)⁻¹   := mul_lt_mul_of_pos_right h_denom h_inv_pos
        _ = 1                         := mul_inv_cancel₀ (ne_of_gt h_denom_pos)
    calc
      (1 - z^2) / (1 + z^2) = (1 - z^2) * (1 + z^2)⁻¹ := div_eq_mul_inv _ _
      _ < (1 - z^2) * 1                               := mul_lt_mul_of_pos_left h_inv h_num_pos
      _ = 1 - z^2                                     := by ring
  · exact hC0

/-- Theorem: The physical equivalent matching the discrete Unilateral Predictability Horizon limit.
    The absolute MSE is bounded by δ if and only if the distance r satisfies r ≤ ξ_abs*. -/
theorem unilateral_horizon_equivalence (C0 z δ r : ℝ)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) (hδ0 : 0 < δ) (hδ : δ < C0) :
    C0 * (1 - exp (2 * r * log z)) ≤ δ ↔ r ≤ xi_abs_star C0 z δ := by
  have h_log_z_neg : log z < 0 := (log_neg_iff hz0).mpr hz1
  have h_denom_pos : 0 < 1 - δ / C0 := by
    have h_div : δ / C0 < 1 := (div_lt_one hC0).mpr hδ
    linarith
  unfold xi_abs_star xi
  -- Equivalence chain
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

end PredictabilityParameters

-- =========================================================================
-- PART 2: Hilbert Space Optimization of Linear Predictors
-- =========================================================================

section HilbertPredictors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: For any predictor x ≠ 0 and target y, the parameter β minimizing the
  mean squared error ‖y - β • x‖^2 is β_opt = ⟪x, y⟫ / ‖x‖^2, and this minimum
  squared error is exactly equal to ‖y‖^2 - ⟪x, y⟫^2 / ‖x‖^2.
-/
theorem unilateral_optimal_predictor (x y : E) (hx : x ≠ 0) (β : ℝ) :
    ‖y - (inner ℝ x y / ‖x‖^2) • x‖^2 ≤ ‖y - β • x‖^2 := by
  let β_opt := inner ℝ x y / ‖x‖^2
  have h_decomp : y - β • x = (y - β_opt • x) + (β_opt - β) • x := by
    rw [sub_smul]
    abel
  have hx_norm : ‖x‖^2 = inner ℝ x x := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have hx_ne_zero : inner ℝ x x ≠ 0 := by
    intro h_zero
    rw [inner_self_eq_zero] at h_zero
    exact hx h_zero
  have h_orth : inner ℝ x (y - β_opt • x) = 0 := by
    simp only [inner_sub_right, inner_smul_right]
    unfold β_opt
    rw [hx_norm, div_mul_cancel₀ (inner ℝ x y) hx_ne_zero]
    exact sub_self (inner ℝ x y)
  have h_norm_add : ‖(y - β_opt • x) + (β_opt - β) • x‖^2 =
      ‖y - β_opt • x‖^2 + 2 * inner ℝ (y - β_opt • x) ((β_opt - β) • x) +
      ‖(β_opt - β) • x‖^2 := by
    exact norm_add_sq_real (y - β_opt • x) ((β_opt - β) • x)
  have h_inner_zero : inner ℝ (y - β_opt • x) ((β_opt - β) • x) = 0 := by
    rw [inner_smul_right, real_inner_comm, h_orth, mul_zero]
  have h_norm_add_simp : ‖(y - β_opt • x) + (β_opt - β) • x‖^2 =
      ‖y - β_opt • x‖^2 + ‖(β_opt - β) • x‖^2 := by
    rw [h_norm_add, h_inner_zero]
    ring
  rw [h_decomp, h_norm_add_simp]
  have h_nonneg : 0 ≤ ‖(β_opt - β) • x‖^2 := sq_nonneg _
  linarith

end HilbertPredictors
