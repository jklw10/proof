import Mathlib.Analysis.SpecialFunctions.Pow.Real
import entropy.common
import entropy.motion
import entropy.gravity
import entropy.ThreeD

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real

-- =========================================================================
-- PART 1: Emergent Physical Constant Definitions
-- =========================================================================

/-- The emergent Planck Length (minimum informational resolution scale) of the universe. -/
def planck_length (C0 Λ : ℝ) : ℝ := C0 / Λ

/-- The emergent Gravitational Constant mapping the entropic coupling γ to the Planck scale. -/
def G_eff (γ C0 Λ : ℝ) : ℝ := γ * (planck_length C0 Λ) ^ (2 : ℕ)

/-- The quantum energy offset κ² corresponding to the inverse squared correlation scale. -/
def quantum_energy_offset (ξ : ℝ) : ℝ := 1 / ξ ^ (2 : ℕ)


-- =========================================================================
-- PART 2: Analytical Limit and Error Bounds for 3D Entropic Force
-- =========================================================================

/-- Theorem: Analytical 3D Entropic Force Error Bound.
    Proves that the ratio of the full entropic force F to its Newtonian-like long-range
    asymptotic approximation F_asymp = - G_eff / r^3 converges to 1 as r → ∞.
    Specifically, it extracts the exact algebraic error bound at any separation r > r_crit,
    verifying that the systematic correction is exactly 1 / (η^2 * r^2 - 1). -/
theorem entropic_force_3d_error_bound (γ C0 Λ r : ℝ)
    (hγ : 0 < γ) (hC0 : 0 < C0) (hΛ : 0 < Λ) (hr : C0 / Λ < r) :
    let η := Λ / C0
    let lP := planck_length C0 Λ
    let F := entropic_force_3d γ η r
    let F_asymp := - (G_eff γ C0 Λ) / r ^ (3 : ℕ)
    |F / F_asymp - 1| = 1 / (η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1) := by
  intro η lP F F_asymp
  have h_r_pos : 0 < r := by
    have h_div : 0 < C0 / Λ := div_pos hC0 hΛ
    linarith
  have hC0_ne : C0 ≠ 0 := ne_of_gt hC0
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ
  have h_r_ne : r ≠ 0 := ne_of_gt h_r_pos
  have h_r3_ne : r ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 h_r_ne

  -- Prove that the denominator of the error bound is strictly positive for r > r_crit
  have h_denom_pos : 0 < η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1 := by
    unfold η
    have h1 : C0 / Λ < r := hr
    have h2 : 0 < C0 / Λ := div_pos hC0 hΛ
    have h_sq : (C0 / Λ) ^ (2 : ℕ) < r ^ (2 : ℕ) := sq_lt_sq.mpr (by rw [abs_of_pos h2, abs_of_pos h_r_pos]; exact hr)
    have h3 : (Λ / C0) ^ (2 : ℕ) * (C0 / Λ) ^ (2 : ℕ) < (Λ / C0) ^ (2 : ℕ) * r ^ (2 : ℕ) := by
      apply mul_lt_mul_of_pos_left h_sq
      exact sq_pos_of_ne_zero (div_ne_zero hΛ_ne hC0_ne)
    have h_cancel : (Λ / C0) ^ (2 : ℕ) * (C0 / Λ) ^ (2 : ℕ) = 1 := by
      rw [← mul_pow]
      have : (Λ / C0) * (C0 / Λ) = 1 := by
        field_simp
      rw [this, one_pow]
    rw [h_cancel] at h3
    linarith

  have h_denom_ne : η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1 ≠ 0 := ne_of_gt h_denom_pos

  -- 1. Division fixed by field_simp
  have h_F_eq : F = - (γ / (r * (η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1))) := by
    unfold F entropic_force_3d
    field_simp [h_r_ne, h_denom_ne]


  -- 2. lP issue fixed by unfolding planck_length and G_eff directly, and dsimp η to match variables
  have h_ratio : F / F_asymp = (η ^ (2 : ℕ) * r ^ (3 : ℕ)) / (r * (η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1)) := by
    unfold F_asymp G_eff planck_length
    rw [h_F_eq]
    dsimp [η] at *
    field_simp [hC0_ne, hΛ_ne, h_r_ne, h_denom_ne]


  -- 3. Simplified cleanly using field_simp instead of manual cancellation
  have h_ratio_simpl : F / F_asymp = (η ^ (2 : ℕ) * r ^ (2 : ℕ)) / (η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1) := by
    rw [h_ratio]
    field_simp [h_r_ne, h_denom_ne]


  -- 4. Over-rewriting bug completely bypassed via field_simp
  have h_sub : F / F_asymp - 1 = 1 / (η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1) := by
    rw [h_ratio_simpl]
    field_simp [h_denom_ne]
    ring

  rw [h_sub, abs_of_pos]
  exact one_div_pos.mpr h_denom_pos

#print axioms entropic_force_3d_error_bound
