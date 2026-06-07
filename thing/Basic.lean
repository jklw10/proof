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

/-- The Unilateral MSE for prediction at discrete distance r ≥ 1 -/
def MSE_uni (C0 z : ℝ) (r : ℕ) : ℝ := C0 * (1 - z ^ (2 * r))

/-- The Bilateral MSE (local boundary limit) -/
def MSE_bi (C0 z : ℝ) : ℝ := C0 * ((1 - z^2) / (1 + z^2))

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

-- =========================================================================
-- PART 3: Spatial Markov Property / Infinite Neighborhood Reduction
-- =========================================================================

section SpatialMarkov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: Spatial Markov Property (Bilateral Minimality).
  For any linear combination of a 4-node neighborhood {x_{-2}, x_{-1}, x_1, x_2},
  the bilateral boundary predictor P = β * x_{-1} + β * x_1 yields the absolute minimum MSE.
  Expanding the predictor further onto x_{-2} and x_2 provides exactly zero further reduction.
-/
theorem spatial_markov_property_optimality (x_neg2 x_neg1 x_1 x_2 y : E) (C0 z : ℝ)
    -- Target variance
    (h_norm_y : ‖y‖^2 = C0)
    -- Predictor variances
    (h_norm_neg2 : ‖x_neg2‖^2 = C0)
    (h_norm_neg1 : ‖x_neg1‖^2 = C0)
    (h_norm_1 : ‖x_1‖^2 = C0)
    (h_norm_2 : ‖x_2‖^2 = C0)
    -- Covariances relative to target y (at distance r)
    (h_y_neg2 : inner ℝ y x_neg2 = C0 * z^2)
    (h_y_neg1 : inner ℝ y x_neg1 = C0 * z)
    (h_y_1 : inner ℝ y x_1 = C0 * z)
    (h_y_2 : inner ℝ y x_2 = C0 * z^2)
    -- Cross-covariances among predictor nodes
    (h_neg2_neg1 : inner ℝ x_neg2 x_neg1 = C0 * z)
    (h_neg2_1 : inner ℝ x_neg2 x_1 = C0 * z^3)
    (h_neg2_2 : inner ℝ x_neg2 x_2 = C0 * z^4)
    (h_neg1_1 : inner ℝ x_neg1 x_1 = C0 * z^2)
    (h_neg1_2 : inner ℝ x_neg1 x_2 = C0 * z^3)
    (h_1_2 : inner ℝ x_1 x_2 = C0 * z)
    -- Physical constraints
    (hz : 1 + z^2 ≠ 0)
    -- Arbitrary weights for the 4-node linear predictor
    (w_neg2 w_neg1 w_1 w_2 : ℝ) :
    let β := z / (1 + z^2)
    let P := β • x_neg1 + β • x_1
    let W := w_neg2 • x_neg2 + w_neg1 • x_neg1 + w_1 • x_1 + w_2 • x_2
    ‖y - P‖^2 ≤ ‖y - W‖^2 := by
  intro β P W
  -- Show that the bilateral error vector (y - P) is orthogonal to every generator
  have h_orth_neg1 : inner ℝ (y - P) x_neg1 = 0 := by
    unfold P β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [real_inner_comm x_neg1 x_1]
    rw [h_y_neg1, real_inner_self_eq_norm_sq, h_norm_neg1, h_neg1_1]
    have h_div : (z / (1 + z^2)) * C0 + (z / (1 + z^2)) * (C0 * z^2) = z * C0 := by
      calc
        (z / (1 + z^2)) * C0 + (z / (1 + z^2)) * (C0 * z^2) = (z / (1 + z^2)) * (1 + z^2) * C0 := by ring
        _ = z * C0 := by rw [div_mul_cancel₀ _ hz]
    rw [h_div]
    ring

  have h_orth_1 : inner ℝ (y - P) x_1 = 0 := by
    unfold P β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [h_y_1, h_neg1_1, real_inner_self_eq_norm_sq, h_norm_1]
    have h_div : (z / (1 + z^2)) * (C0 * z^2) + (z / (1 + z^2)) * C0 = z * C0 := by
      calc
        (z / (1 + z^2)) * (C0 * z^2) + (z / (1 + z^2)) * C0 = (z / (1 + z^2)) * (1 + z^2) * C0 := by ring
        _ = z * C0 := by rw [div_mul_cancel₀ _ hz]
    rw [h_div]
    ring

  have h_orth_neg2 : inner ℝ (y - P) x_neg2 = 0 := by
    unfold P β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [real_inner_comm x_neg2 x_neg1, real_inner_comm x_neg2 x_1]
    rw [h_y_neg2, h_neg2_neg1, h_neg2_1]
    have h_div : (z / (1 + z^2)) * (C0 * z) + (z / (1 + z^2)) * (C0 * z^3) = z^2 * C0 := by
      calc
        (z / (1 + z^2)) * (C0 * z) + (z / (1 + z^2)) * (C0 * z^3) = (z / (1 + z^2)) * (1 + z^2) * (C0 * z) := by ring
        _ = z * (C0 * z) := by rw [div_mul_cancel₀ _ hz]
        _ = z^2 * C0 := by ring
    rw [h_div]
    ring

  have h_orth_2 : inner ℝ (y - P) x_2 = 0 := by
    unfold P β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [h_y_2, h_neg1_2, h_1_2]
    have h_div : (z / (1 + z^2)) * (C0 * z^3) + (z / (1 + z^2)) * (C0 * z) = z^2 * C0 := by
      calc
        (z / (1 + z^2)) * (C0 * z^3) + (z / (1 + z^2)) * (C0 * z) = (z / (1 + z^2)) * (1 + z^2) * (C0 * z) := by ring
        _ = z * (C0 * z) := by rw [div_mul_cancel₀ _ hz]
        _ = z^2 * C0 := by ring
    rw [h_div]
    ring

  -- Decompose the general error (y - W) into orthogonal components (y - P) and (P - W)
  have h_decomp : y - W = (y - P) + (P - W) := by abel

  -- Show that (P - W) lies in the span of the neighborhood, and is thus orthogonal to (y - P)
  have h_orth_P_W : inner ℝ (y - P) (P - W) = 0 := by
    unfold P W
    have h_lin : (β • x_neg1 + β • x_1) - (w_neg2 • x_neg2 + w_neg1 • x_neg1 + w_1 • x_1 + w_2 • x_2) =
        (-w_neg2) • x_neg2 + (β - w_neg1) • x_neg1 + (β - w_1) • x_1 + (-w_2) • x_2 := by
      simp only [neg_smul, sub_smul]
      abel
    rw [h_lin]
    simp only [inner_add_right, inner_smul_right]
    rw [h_orth_neg2, h_orth_neg1, h_orth_1, h_orth_2]
    ring

  -- Apply the Pythagorean theorem in Hilbert Space
  have h_pythag : ‖y - W‖^2 = ‖y - P‖^2 + ‖P - W‖^2 := by
    calc
      ‖y - W‖^2 = ‖(y - P) + (P - W)‖^2 := by rw [h_decomp]
      _ = ‖y - P‖^2 + 2 * inner ℝ (y - P) (P - W) + ‖P - W‖^2 := norm_add_sq_real _ _
      _ = ‖y - P‖^2 + ‖P - W‖^2 := by rw [h_orth_P_W, mul_zero, add_zero]

  -- Since the squared norm is non-negative, the error ‖y - P‖^2 is a strict lower bound
  have h_nonneg : 0 ≤ ‖P - W‖^2 := sq_nonneg _
  linarith

end SpatialMarkov

-- =========================================================================
-- PART 4: Matrix Algebraic Foundation of the Spatial Markov Property
-- =========================================================================

section MatrixAlgebra

/-- The 2x2 boundary covariance matrix for the AR(1) process on a grid -/
def boundary_matrix (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, z^2],
    ![z^2, 1]]

/-- The analytical inverse of the boundary covariance matrix -/
def boundary_matrix_inv (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1 / (1 - z^4), -z^2 / (1 - z^4)],
    ![-z^2 / (1 - z^4), 1 / (1 - z^4)]]

/-- The row covariance vector connecting the target node to its immediate boundary -/
def row_vec (z : ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  ![![z, z]]

/-- The column covariance vector connecting the immediate boundary to the target node -/
def col_vec (z : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  ![![z], ![z]]

/-- Theorem: Prove that boundary_matrix_inv is the exact algebraic inverse
    of boundary_matrix, provided the determinant factor 1 - z^4 is non-zero. -/
theorem boundary_matrix_mul_inv (z : ℝ) (hz4 : 1 - z^4 ≠ 0) :
    boundary_matrix z * boundary_matrix_inv z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [boundary_matrix, boundary_matrix_inv, Matrix.mul_apply, Matrix.one_apply]
    simp [Fin.sum_univ_two]
    have : 1 - z^4 ≠ 0 := hz4
    field_simp
    ring
  }

/-- Theorem: Derivation of the Bilateral Horizon from the matrix representation.
    The conditional variance formula C0 - C0 * (R * A^-1 * C) simplifies
    exactly to the bilateral predictability limit C0 * ((1 - z^2) / (1 + z^2)). -/
theorem bilateral_matrix_reduction (C0 z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (hC0 : 0 < C0) :
    let R := row_vec z
    let A_inv := boundary_matrix_inv z
    let C := col_vec z
    let M := R * A_inv * C
    C0 - C0 * M 0 0 = C0 * ((1 - z^2) / (1 + z^2)) := by
  intro R A_inv C M
  have hz2_lt1 : z^2 < 1 := by
    calc
      z^2 = z * z := by ring
      _ < z * 1   := mul_lt_mul_of_pos_left hz1 hz0
      _ = z       := mul_one z
      _ < 1       := hz1
  have hz2_pos : 0 < z^2 := by
    have : 0 < z * z := mul_pos hz0 hz0
    linarith
  have hz4_lt1 : z^4 < 1 := by
    calc
      z^4 = z^2 * z^2 := by ring
      _ < z^2 * 1     := mul_lt_mul_of_pos_left hz2_lt1 hz2_pos
      _ = z^2         := mul_one _
      _ < 1           := hz2_lt1
  have hz4 : 1 - z^4 ≠ 0 := by linarith [hz4_lt1]
  have hz2_add : 1 + z^2 ≠ 0 := by linarith [sq_nonneg z]
  have h_M_apply : M 0 0 = (2 * z^2) / (1 + z^2) := by
    unfold M R A_inv C row_vec col_vec boundary_matrix_inv
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one]
    have : 1 - z^4 ≠ 0 := hz4
    have : 1 + z^2 ≠ 0 := hz2_add
    field_simp
    ring
  rw [h_M_apply]
  field_simp
  ring

end MatrixAlgebra
#print axioms bilateral_matrix_reduction
