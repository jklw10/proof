import entropy.common
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
set_option linter.unusedSimpArgs false
open Real
open RealInnerProductSpace
open Matrix

/-- The Unilateral MSE for prediction at discrete distance r ≥ 1 -/
def MSE_uni (C0 z : ℝ) (r : ℕ) : ℝ := C0 * (1 - z ^ (2 * r))

/-- The Bilateral MSE (local boundary limit) -/
def MSE_bi (C0 z : ℝ) : ℝ := C0 * ((1 - z^2) / (1 + z^2))

section DiscreteSetup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper function: Maps a discrete process u: ℤ → E satisfying the 1D exponential decay model
    with variance C0 and decay z to the unified framework. -/
def discrete_to_unified (u : ℤ → E) (C0 z : ℝ)
    (h_cov : ∀ x y : ℤ, inner ℝ (u x) (u y) = C0 * z ^ |(x : ℝ) - (y : ℝ)|)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) : ExponentialCovarianceProcess ℤ E where
  u := u
  C0 := C0
  z := z
  hC0 := hC0
  hz0 := hz0
  hz1 := hz1
  cov := by
    intro x y
    rw [Int.dist_eq]
    exact h_cov x y

end DiscreteSetup

section HilbertPredictors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: Specialized discrete bilateral limit.
    If we predict node y using its nearest symmetric neighbors u = x_neg1 + x_1,
    the resulting optimal MSE corresponds exactly to the discrete bilateral horizon limit. -/
theorem discrete_bilateral_optimal_mse (u : ℤ → E) (C0 z : ℝ)
    (h_cov : ∀ x y : ℤ, inner ℝ (u x) (u y) = C0 * z ^ |(x : ℝ) - (y : ℝ)|)
    (hz0 : 0 < z) (hz1 : z < 1) (hC0 : 0 < C0) (y_idx : ℤ) :
    let P := discrete_to_unified u C0 z h_cov hC0 hz0 hz1
    let x_neg1 := P.u (y_idx - 1)
    let x_1 := P.u (y_idx + 1)
    let y := P.u y_idx
    let u_comb := x_neg1 + x_1
    let β_opt := inner ℝ u_comb y / ‖u_comb‖^2
    ‖y - β_opt • u_comb‖^2 = C0 * ((1 - z^2) / (1 + z^2)) := by
  intro P x_neg1 x_1 y u_comb β_opt
  have hd1 : dist (y_idx - 1) y_idx = 1 := by
    rw [Int.dist_eq]
    have h_calc : ((y_idx - 1 : ℤ) : ℝ) - (y_idx : ℝ) = -1 := by
      push_cast
      ring
    rw [h_calc]
    norm_num
  have hd2 : dist y_idx (y_idx + 1) = 1 := by
    rw [Int.dist_eq]
    have h_calc : (y_idx : ℝ) - ((y_idx + 1 : ℤ) : ℝ) = -1 := by
      push_cast
      ring
    rw [h_calc]
    norm_num
  have hd : dist (y_idx - 1) (y_idx + 1) = 2 := by
    rw [Int.dist_eq]
    have h_calc : ((y_idx - 1 : ℤ) : ℝ) - ((y_idx + 1 : ℤ) : ℝ) = -2 := by
      push_cast
      ring
    rw [h_calc]
    norm_num
  have h_sum : (1 : ℝ) + 1 = 2 := by norm_num
  have h_pos : 0 < (2 : ℝ) := by norm_num

  -- Extract the unified MSE evaluated at these points
  have h_mse := ExponentialCovarianceProcess.bilateral_optimal_mse P (y_idx - 1) y_idx (y_idx + 1) 1 1 2 hd1 hd2 hd h_sum h_pos
  dsimp [P, discrete_to_unified] at h_mse ⊢

  have hd2' : dist (y_idx + 1) y_idx = 1 := by rw [dist_comm, hd2]
  have h_inner_comb_y : inner ℝ u_comb y = 2 * C0 * z := by
    unfold u_comb x_neg1 x_1 y
    dsimp [P, discrete_to_unified]
    simp only [inner_add_left]
    rw [h_cov (y_idx - 1) y_idx, h_cov (y_idx + 1) y_idx]
    have h_diff1 : |((y_idx - 1 : ℤ) : ℝ) - (y_idx : ℝ)| = 1 := by
      push_cast
      ring_nf
      norm_num
    have h_diff2 : |((y_idx + 1 : ℤ) : ℝ) - (y_idx : ℝ)| = 1 := by
      push_cast
      ring_nf
      norm_num
    rw [h_diff1, h_diff2]
    simp only [Real.rpow_one]
    ring

  have h_norm_comb : ‖u_comb‖^2 = 2 * C0 * (1 + z^2) := by
    unfold u_comb x_neg1 x_1
    dsimp [P, discrete_to_unified]
    have h_sq : ‖u (y_idx - 1) + u (y_idx + 1)‖^2 =
        inner ℝ (u (y_idx - 1) + u (y_idx + 1)) (u (y_idx - 1) + u (y_idx + 1)) := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm]
    rw [h_sq]
    simp only [inner_add_left, inner_add_right]
    rw [h_cov (y_idx - 1) (y_idx - 1), h_cov (y_idx + 1) (y_idx + 1),
        h_cov (y_idx + 1) (y_idx - 1), h_cov (y_idx - 1) (y_idx + 1)]
    have h_sub_self1 : |((y_idx - 1 : ℤ) : ℝ) - ((y_idx - 1 : ℤ) : ℝ)| = 0 := by
      rw [sub_self, abs_zero]
    have h_sub_self2 : |((y_idx + 1 : ℤ) : ℝ) - ((y_idx + 1 : ℤ) : ℝ)| = 0 := by
      rw [sub_self, abs_zero]
    have h_sub_diff1 : |((y_idx + 1 : ℤ) : ℝ) - ((y_idx - 1 : ℤ) : ℝ)| = 2 := by
      push_cast
      ring_nf
      norm_num
    have h_sub_diff2 : |((y_idx - 1 : ℤ) : ℝ) - ((y_idx + 1 : ℤ) : ℝ)| = 2 := by
      push_cast
      ring_nf
      norm_num
    rw [h_sub_self1, h_sub_self2, h_sub_diff1, h_sub_diff2]
    simp only [Real.rpow_zero, mul_one, Real.rpow_two]
    ring

  have h_β1_eq : (z ^ (1 : ℝ) - z ^ ((1 : ℝ) + 2)) / (1 - z ^ (2 * (2 : ℝ))) = z / (1 + z^2) := by
    simp only [Real.rpow_one]
    have h_pow3 : z ^ ((1 : ℝ) + 2) = z^3 := by
      have : (1 : ℝ) + 2 = (3 : ℕ) := by norm_num
      rw [this, Real.rpow_natCast]
    have h_pow4 : z ^ (2 * (2 : ℝ)) = (z^2)^2 := by
      have : (2 : ℝ) * 2 = (4 : ℕ) := by norm_num
      rw [this, Real.rpow_natCast]
      ring
    rw [h_pow3, h_pow4]
    have h_denom_factor : 1 - (z^2)^2 = (1 - z^2) * (1 + z^2) := by ring
    have h_num_factor : z - z^3 = z * (1 - z^2) := by ring
    rw [h_num_factor, h_denom_factor]
    have hz_lt1 : z^2 < 1 := by
      calc
        z^2 = z * z := by ring
        _ < z * 1   := mul_lt_mul_of_pos_left hz1 hz0
        _ = z       := mul_one z
        _ < 1       := hz1
    have h_ne : 1 - z^2 ≠ 0 := by linarith [sq_nonneg z]
    field_simp

  have h_β_opt : β_opt = z / (1 + z^2) := by
    unfold β_opt
    rw [h_inner_comb_y, h_norm_comb]
    have hC0_ne : C0 ≠ 0 := by linarith
    have hz_ne : 1 + z^2 ≠ 0 := by linarith [sq_nonneg z]
    field_simp

  have h_mse' := h_mse
  rw [← smul_add] at h_mse'
  rw [h_β1_eq] at h_mse'

  dsimp only [y, x_neg1, x_1, u_comb, P, discrete_to_unified] at ⊢
  rw [h_β_opt]
  rw [h_mse']

  -- Algebraically match the unified output structure to the discrete ratio representation
  have h_ratio_eq : (1 - z ^ ((2 : ℝ) * 1) - z ^ ((2 : ℝ) * 1) + z ^ ((2 : ℝ) * 2)) / (1 - z ^ ((2 : ℝ) * 2)) =
      (1 - z^2) / (1 + z^2) := by
    have h1 : (2 : ℝ) * 1 = ((2 : ℕ) : ℝ) := by norm_num
    have h2 : (2 : ℝ) * 2 = ((4 : ℕ) : ℝ) := by norm_num
    rw [h1, h2]
    simp only [Real.rpow_natCast]
    have h_denom_factor : 1 - z^4 = (1 - z^2) * (1 + z^2) := by ring
    have h_num_factor : 1 - z^2 - z^2 + z^4 = (1 - z^2)^2 := by ring
    rw [h_num_factor, h_denom_factor]
    have hz_lt1 : z^2 < 1 := by
      calc
        z^2 = z * z := by ring
        _ < z * 1   := mul_lt_mul_of_pos_left hz1 hz0
        _ = z       := mul_one z
        _ < 1       := hz1
    have h_ne : 1 - z^2 ≠ 0 := by linarith [sq_nonneg z]
    field_simp

  rw [h_ratio_eq]
end HilbertPredictors

section SpatialMarkov

/-- Theorem: Spatial Markov Property (Bilateral Minimality).
    For any linear combination of a 4-node neighborhood {x_{-2}, x_{-1}, x_1, x_2},
    the bilateral boundary predictor P = β * x_{-1} + β * x_1 yields the absolute minimum MSE.
    Now formalized elegantly under the unified metric space framework. -/
theorem spatial_markov_property_optimality {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess T E) (x_neg2 x_neg1 y x_1 x_2 : T)
    (hd_neg2_neg1 : dist x_neg2 x_neg1 = 1)
    (hd_neg2_y : dist x_neg2 y = 2)
    (hd_neg2_1 : dist x_neg2 x_1 = 3)
    (hd_neg2_2 : dist x_neg2 x_2 = 4)
    (hd_neg1_y : dist x_neg1 y = 1)
    (hd_neg1_1 : dist x_neg1 x_1 = 2)
    (hd_neg1_2 : dist x_neg1 x_2 = 3)
    (hd_y_1 : dist y x_1 = 1)
    (hd_y_2 : dist y x_2 = 2)
    (hd_1_2 : dist x_1 x_2 = 1)
    (hz : 1 + P.z^2 ≠ 0)
    (w_neg2 w_neg1 w_1 w_2 : ℝ) :
    let β := P.z / (1 + P.z^2)
    let Pred := β • P.u x_neg1 + β • P.u x_1
    let W := w_neg2 • P.u x_neg2 + w_neg1 • P.u x_neg1 + w_1 • P.u x_1 + w_2 • P.u x_2
    ‖P.u y - Pred‖^2 ≤ ‖P.u y - W‖^2 := by
  intro β Pred W

  have h_pow2 : P.z ^ (2 : ℝ) = P.z^2 := by
    have : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  have h_pow3 : P.z ^ (3 : ℝ) = P.z^3 := by
    have : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]

  -- Show that the bilateral error vector (y - Pred) is orthogonal to every generator
  have h_orth_neg1 : inner ℝ (P.u y - Pred) (P.u x_neg1) = 0 := by
    unfold Pred β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [P.cov y x_neg1, P.cov x_neg1 x_neg1, P.cov x_1 x_neg1]
    have h_d1 : dist y x_neg1 = 1 := by rw [dist_comm, hd_neg1_y]
    have h_d2 : dist x_neg1 x_neg1 = 0 := dist_self _
    have h_d3 : dist x_1 x_neg1 = 2 := by rw [dist_comm, hd_neg1_1]
    rw [h_d1, h_d2, h_d3]
    simp only [Real.rpow_zero, mul_one, Real.rpow_one, Real.rpow_natCast]
    rw [h_pow2]
    field_simp
    ring

  have h_orth_1 : inner ℝ (P.u y - Pred) (P.u x_1) = 0 := by
    unfold Pred β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [P.cov y x_1, P.cov x_neg1 x_1, P.cov x_1 x_1]
    have h_d1 : dist y x_1 = 1 := hd_y_1
    have h_d2 : dist x_neg1 x_1 = 2 := hd_neg1_1
    have h_d3 : dist x_1 x_1 = 0 := dist_self _
    rw [h_d1, h_d2, h_d3]
    simp only [Real.rpow_zero, mul_one, Real.rpow_one, Real.rpow_natCast]
    rw [h_pow2]
    field_simp
    ring

  have h_orth_neg2 : inner ℝ (P.u y - Pred) (P.u x_neg2) = 0 := by
    unfold Pred β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [P.cov y x_neg2, P.cov x_neg1 x_neg2, P.cov x_1 x_neg2]
    have h_d1 : dist y x_neg2 = 2 := by rw [dist_comm, hd_neg2_y]
    have h_d2 : dist x_neg1 x_neg2 = 1 := by rw [dist_comm, hd_neg2_neg1]
    have h_d3 : dist x_1 x_neg2 = 3 := by rw [dist_comm, hd_neg2_1]
    rw [h_d1, h_d2, h_d3]
    simp only [Real.rpow_zero, mul_one, Real.rpow_one, Real.rpow_natCast]
    rw [h_pow2, h_pow3]
    field_simp
    ring

  have h_orth_2 : inner ℝ (P.u y - Pred) (P.u x_2) = 0 := by
    unfold Pred β
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [P.cov y x_2, P.cov x_neg1 x_2, P.cov x_1 x_2]
    have h_d1 : dist y x_2 = 2 := hd_y_2
    have h_d2 : dist x_neg1 x_2 = 3 := hd_neg1_2
    have h_d3 : dist x_1 x_2 = 1 := hd_1_2
    rw [h_d1, h_d2, h_d3]
    simp only [Real.rpow_zero, mul_one, Real.rpow_one, Real.rpow_natCast]
    rw [h_pow2, h_pow3]
    field_simp
    ring

  -- Decompose the general error (y - W) into orthogonal components (y - Pred) and (Pred - W)
  have h_decomp : P.u y - W = (P.u y - Pred) + (Pred - W) := by abel

  -- Show that (Pred - W) lies in the span of the neighborhood, and is thus orthogonal to (y - Pred)
  have h_orth_P_W : inner ℝ (P.u y - Pred) (Pred - W) = 0 := by
    unfold Pred W
    have h_lin : (β • P.u x_neg1 + β • P.u x_1) - (w_neg2 • P.u x_neg2 + w_neg1 • P.u x_neg1 + w_1 • P.u x_1 + w_2 • P.u x_2) =
        (-w_neg2) • P.u x_neg2 + (β - w_neg1) • P.u x_neg1 + (β - w_1) • P.u x_1 + (-w_2) • P.u x_2 := by
      simp only [neg_smul, sub_smul]
      abel
    rw [h_lin]
    simp only [inner_add_right, inner_smul_right]
    rw [h_orth_neg2, h_orth_neg1, h_orth_1, h_orth_2]
    ring

  -- Apply the Pythagorean theorem in Hilbert Space
  have h_pythag : ‖P.u y - W‖^2 = ‖P.u y - Pred‖^2 + ‖Pred - W‖^2 := by
    calc
      ‖P.u y - W‖^2 = ‖(P.u y - Pred) + (Pred - W)‖^2 := by rw [h_decomp]
      _ = ‖P.u y - Pred‖^2 + 2 * inner ℝ (P.u y - Pred) (Pred - W) + ‖Pred - W‖^2 := norm_add_sq_real _ _
      _ = ‖P.u y - Pred‖^2 + ‖Pred - W‖^2 := by rw [h_orth_P_W, mul_zero, add_zero]

  have h_nonneg : 0 ≤ ‖Pred - W‖^2 := sq_nonneg _
  linarith

end SpatialMarkov
