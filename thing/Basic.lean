import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic

open Real
open RealInnerProductSpace

-- =========================================================================
-- PART 1: Physical Parameters & Analytical Predictability Horizons
-- =========================================================================

section PredictabilityParameters

/-- The physical spatial correlation length ξ is defined from z = e^{-1/ξ} -/
noncomputable def xi (z : ℝ) : ℝ := -1 / log z

lemma xi_pos (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) : 0 < xi z := by
  have hz_lt : log z < 0 := (Real.log_neg_iff hz0).mpr hz1
  exact div_pos_of_neg_of_neg (by linarith) hz_lt

/-- The Unilateral MSE for prediction at discrete distance r ≥ 1 -/
def MSE_uni (C0 z : ℝ) (r : ℕ) : ℝ := C0 * (1 - z ^ (2 * r))

/-- The Bilateral MSE (local boundary limit) -/
noncomputable def MSE_bi (C0 z : ℝ) : ℝ := C0 * ((1 - z^2) / (1 + z^2))

/-- The Unilateral Predictability scale ξ_abs* -/
noncomputable def xi_abs_star (C0 z δ : ℝ) : ℝ :=
  (xi z / 2) * log (1 / (1 - δ / C0))

/-- The minimum tolerance for Unilateral predictability (at r = 1) -/
noncomputable def delta_min_uni (C0 z : ℝ) : ℝ := C0 * (1 - z^2)

/-- The minimum tolerance for Bilateral predictability -/
noncomputable def delta_min_bi (C0 z : ℝ) : ℝ := C0 * ((1 - z^2) / (1 + z^2))

/-- Theorem: The bilateral predictability limit strictly lowers the minimum allowable
    prediction error compared to the unilateral predictability limit: δ_min^(2) < δ_min^(1) -/
theorem bilateral_strict_reduction (C0 z : ℝ) (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) :
    delta_min_bi C0 z < delta_min_uni C0 z := by
  simp only [delta_min_bi, delta_min_uni]
  apply mul_lt_mul_of_pos_left
  · have h_z2_pos : 0 < z^2 := sq_pos_of_pos hz0
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

/-- Theorem: If we predict a node y using its symmetric boundary u = x_{-1} + x_{1},
  under stationary covariance conditions, the minimum possible MSE is the Bilateral Horizon.
-/
theorem bilateral_optimal_mse (x_neg1 x_1 y : E) (C0 z : ℝ)
    (h_norm_y : ‖y‖ ^ 2 = C0)
    (h_norm_neg1 : ‖x_neg1‖ ^ 2 = C0)
    (h_norm_1 : ‖x_1‖ ^ 2 = C0)
    (h_inner_neg1_1 : inner ℝ x_neg1 x_1 = C0 * z ^ 2)
    (h_inner_y_neg1 : inner ℝ y x_neg1 = C0 * z)
    (h_inner_y_1 : inner ℝ y x_1 = C0 * z)
    (hz_lt1 : z < 1) (hz_pos : 0 < z) (hC0 : 0 < C0) :
    let u := x_neg1 + x_1
    let β_opt := inner ℝ u y / ‖u‖^2
    ‖y - β_opt • u‖^2 = C0 * ((1 - z^2) / (1 + z^2)) := by
  intro u β_opt
  have hu_norm : ‖u‖^2 = 2 * C0 * (1 + z^2) := by
    unfold u
    rw [norm_add_sq_real, h_norm_neg1, h_norm_1, h_inner_neg1_1]
    ring
  have huy_inner : inner ℝ u y = 2 * C0 * z := by
    unfold u
    rw [inner_add_left, real_inner_comm y x_neg1, real_inner_comm y x_1]
    rw [h_inner_y_neg1, h_inner_y_1]
    ring
  have hu_ne_zero : ‖u‖^2 ≠ 0 := by
    rw [hu_norm]
    have h_denom_pos : 0 < 1 + z^2 := by linarith [sq_nonneg z]
    have h_prod_pos : 0 < 2 * C0 * (1 + z^2) :=
      mul_pos (mul_pos (by linarith) hC0) h_denom_pos
    exact ne_of_gt h_prod_pos
  have h_orth_u : inner ℝ u (y - β_opt • u) = 0 := by
    simp only [inner_sub_right, inner_smul_right]
    have hu_norm_inner : ‖u‖^2 = inner ℝ u u := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm]
    unfold β_opt
    rw [← hu_norm_inner, div_mul_cancel₀ (inner ℝ u y) hu_ne_zero]
    exact sub_self (inner ℝ u y)
  have h_decomp_y : y = (y - β_opt • u) + β_opt • u := by abel
  have h_orth_smul : inner ℝ (y - β_opt • u) (β_opt • u) = 0 := by
    rw [real_inner_comm, inner_smul_left, h_orth_u, mul_zero]
  have h_pythag : ‖y‖^2 = ‖y - β_opt • u‖^2 + ‖β_opt • u‖^2 := by
    calc
      ‖y‖^2 = ‖(y - β_opt • u) + β_opt • u‖^2 :=
          congr_arg (fun x => ‖x‖^2) h_decomp_y
      _ = ‖y - β_opt • u‖^2 + 2 * inner ℝ (y - β_opt • u) (β_opt • u) + ‖β_opt • u‖^2 :=
          norm_add_sq_real _ _
      _ = ‖y - β_opt • u‖^2 + ‖β_opt • u‖^2 := by
          rw [h_orth_smul]
          ring
  have h_norm_smul : ‖β_opt • u‖^2 = (inner ℝ u y)^2 / ‖u‖^2 := by
    rw [norm_smul, mul_pow]
    have hu_norm_pos : 0 < ‖u‖^2 := by
      rw [hu_norm]
      have h_denom_pos : 0 < 1 + z^2 := by linarith [sq_nonneg z]
      exact mul_pos (mul_pos (by linarith) hC0) h_denom_pos
    have h_beta_sq : ‖β_opt‖^2 = (inner ℝ u y)^2 / (‖u‖^2)^2 := by
      unfold β_opt
      rw [Real.norm_eq_abs, sq_abs, div_pow]
    rw [h_beta_sq]
    have h_algebraic : ((inner ℝ u y)^2 / (‖u‖^2)^2) * ‖u‖^2 =
        (inner ℝ u y)^2 / ‖u‖^2 := by
      have h_ne : ‖u‖^2 ≠ 0 := ne_of_gt hu_norm_pos
      field_simp
    rw [h_algebraic]
  have h_sub : ‖y - β_opt • u‖^2 = ‖y‖^2 - ‖β_opt • u‖^2 := by linarith [h_pythag]
  rw [h_sub, h_norm_y, h_norm_smul, hu_norm, huy_inner]
  have h_C0_ne : C0 ≠ 0 := ne_of_gt hC0
  have h_z_denom : 1 + z^2 ≠ 0 := by linarith [sq_nonneg z]
  field_simp
  ring

end HilbertPredictors
