import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import entropy.common

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real
open Filter
open Set

-- =========================================================================
-- PART 1: Definitions for 3D Entropic Gravity
-- =========================================================================

/-- The 3D continuous spatial covariance (Yukawa approximation at short range). -/
def C3d (C0 r : ℝ) : ℝ := C0 / r

/-- The 3D entropic force acting on a coordinate at distance r.
    It scales as -1/r^3 at long ranges. -/
def entropic_force_3d (γ η r : ℝ) : ℝ :=
  - (γ / r) * (1 / (η ^ (2 : ℕ) * r ^ (2 : ℕ) - 1))

/-- The 3D entropic potential energy with spatial resolution limit Λ (UV cutoff). -/
def entropic_potential_3d (γ Λ C0 r : ℝ) : ℝ :=
  (γ / 2) * log (Λ * (1 - C0 ^ (2 : ℕ) / (Λ ^ (2 : ℕ) * r ^ (2 : ℕ))))

-- =========================================================================
-- PART 2: The Cauchy-Schwarz Informational Exclusion Boundary
-- =========================================================================

/-- Theorem: The Cauchy-Schwarz Informational Exclusion Boundary.
    In 3D, the spatial covariance function satisfies C(r) = C0 / r, and the local
    resolution limit is C(0) = Λ. The Cauchy-Schwarz inequality strictly requires
    C(r)^2 ≤ C(0)^2, which mathematically guarantees that independent communicating
    states cannot exist closer than the critical distance r_crit = C0 / Λ. -/
theorem continuous_3d_exclusion_limit (C0 Λ r : ℝ)
    (hC0 : 0 < C0) (hΛ : 0 < Λ) (hr : 0 < r)
    (h_cs : (C0 / r) ^ (2 : ℕ) ≤ Λ ^ (2 : ℕ)) :
    C0 / Λ ≤ r := by
  have h_pos : 0 < C0 / r := div_pos hC0 hr
  rw [sq_le_sq] at h_cs
  rw [abs_of_pos h_pos, abs_of_pos hΛ] at h_cs
  have h_cs' : C0 / r ≤ Λ := h_cs
  have h_mul : C0 ≤ r * Λ := by
    have := (div_le_iff₀ hr).mp h_cs'
    linarith
  have h_div : C0 / Λ ≤ r := by
    rw [div_le_iff₀ hΛ]
    linarith [h_mul]
  exact h_div

-- =========================================================================
-- PART 3: The 3D Entropic Potential Gradient Theorem
-- =========================================================================

/-- Theorem: 3D Continuous Potential Derivative.
    The continuous attractive entropic force field is the exact negative gradient
    of the 3D entropic potential energy for all separations r > r_crit. -/
theorem continuous_3d_potential_deriv (γ Λ C0 r : ℝ)
    (hγ : 0 < γ) (hΛ : 0 < Λ) (hC0 : 0 < C0) (hr_gt : C0 / Λ < r) :
    let V := fun (y : ℝ) => entropic_potential_3d γ Λ C0 y
    HasDerivAt V (- entropic_force_3d γ (Λ / C0) r) r := by
  intro V
  have h_r_pos : 0 < r := by
    have h_c_l : 0 < C0 / Λ := div_pos hC0 hΛ
    linarith [hr_gt]
  have h_r_ne : r ≠ 0 := ne_of_gt h_r_pos

  -- We restrict the derivative proof to a neighborhood where y > C0 / Λ (meaning y is strictly positive)
  have h_nhds : Ioi (C0 / Λ) ∈ nhds r := by
    apply IsOpen.mem_nhds isOpen_Ioi
    rw [mem_Ioi]
    exact hr_gt
  have h_eventual : ∀ᶠ y in nhds r, Λ * (1 - C0 ^ (2 : ℕ) / (Λ ^ (2 : ℕ) * y ^ (2 : ℕ))) = Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / y ^ (2 : ℕ)) := by
    filter_upwards [h_nhds]
    intro y hy
    rw [mem_Ioi] at hy
    have hy_pos : 0 < y := by
      have h_c_l : 0 < C0 / Λ := div_pos hC0 hΛ
      linarith
    have h_L_ne : Λ ≠ 0 := ne_of_gt hΛ
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    field_simp [h_L_ne, hy_ne]


  -- 1. Derivative of y ↦ y^2 is 2 * r
  have h_deriv_sq : HasDerivAt (fun (y : ℝ) => y ^ (2 : ℕ)) (2 * r) r := by
    have h := hasDerivAt_pow 2 r
    have h_simpl : ((2 : ℕ) : ℝ) * r ^ (2 - 1) = 2 * r := by
      have h1 : 2 - 1 = 1 := rfl
      rw [h1, pow_one, Nat.cast_two]
    rw [h_simpl] at h
    exact h

  -- 2. Derivative of y ↦ 1 / y^2 is - 2 * r / r^4
  have h_deriv_inv_sq : HasDerivAt (fun (y : ℝ) => 1 / y ^ (2 : ℕ)) (- (2 * r) / (r ^ (2 : ℕ)) ^ 2) r := by
    have h_inv : HasDerivAt (fun (y : ℝ) => (y ^ (2 : ℕ))⁻¹) (- (2 * r) / (r ^ (2 : ℕ)) ^ 2) r := by
      apply HasDerivAt.inv h_deriv_sq
      exact ne_of_gt (sq_pos_of_ne_zero h_r_ne)
    have h_eq : (fun (y : ℝ) => (y ^ (2 : ℕ))⁻¹) = (fun (y : ℝ) => 1 / y ^ (2 : ℕ)) := by
      ext y'
      exact (one_div (y' ^ (2 : ℕ))).symm
    rw [h_eq] at h_inv
    exact h_inv

  -- 3. Derivative of y ↦ (C0^2 / Λ) * (1 / y^2)
  have h_deriv_mul : HasDerivAt (fun (y : ℝ) => (C0 ^ (2 : ℕ) / Λ) * (1 / y ^ (2 : ℕ))) ((C0 ^ (2 : ℕ) / Λ) * (- (2 * r) / (r ^ (2 : ℕ)) ^ 2)) r := by
    exact HasDerivAt.const_mul (C0 ^ (2 : ℕ) / Λ) h_deriv_inv_sq

  -- 4. Derivative of y ↦ Λ - (C0^2 / Λ) * (1 / y^2)
  have h_deriv_sub : HasDerivAt (fun (y : ℝ) => Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / y ^ (2 : ℕ))) (0 - (C0 ^ (2 : ℕ) / Λ) * (- (2 * r) / (r ^ (2 : ℕ)) ^ 2)) r := by
    have h_const : HasDerivAt (fun _ => Λ) 0 r := hasDerivAt_const r Λ
    exact HasDerivAt.sub h_const h_deriv_mul

  -- 5. Prove that the argument inside the logarithm is strictly positive
  have h_arg_pos : Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / r ^ (2 : ℕ)) > 0 := by
    have h_L_ne : Λ ≠ 0 := ne_of_gt hΛ
    have h_r_gt_pos : (C0 / Λ) ^ (2 : ℕ) < r ^ (2 : ℕ) := by
      have h_c_l : 0 < C0 / Λ := div_pos hC0 hΛ
      exact sq_lt_sq.mpr (by rw [abs_of_pos h_c_l, abs_of_pos h_r_pos]; exact hr_gt)
    have h_div_lt : C0 ^ (2 : ℕ) / Λ ^ (2 : ℕ) < r ^ (2 : ℕ) := by
      rw [div_pow] at h_r_gt_pos
      exact h_r_gt_pos
    have h_inv_lt : 1 / r ^ (2 : ℕ) < 1 / (C0 ^ (2 : ℕ) / Λ ^ (2 : ℕ)) := by
      rw [one_div_lt_one_div]
      · exact h_div_lt
      · exact sq_pos_of_ne_zero h_r_ne
      · exact div_pos (sq_pos_of_ne_zero (ne_of_gt hC0)) (sq_pos_of_ne_zero (ne_of_gt hΛ))
    have h_simpl : 1 / (C0 ^ (2 : ℕ) / Λ ^ (2 : ℕ)) = Λ ^ (2 : ℕ) / C0 ^ (2 : ℕ) := one_div_div (C0 ^ (2 : ℕ)) (Λ ^ (2 : ℕ))
    rw [h_simpl] at h_inv_lt
    have h_mul_lt : (C0 ^ (2 : ℕ) / Λ) * (1 / r ^ (2 : ℕ)) < (C0 ^ (2 : ℕ) / Λ) * (Λ ^ (2 : ℕ) / C0 ^ (2 : ℕ)) := by
      apply mul_lt_mul_of_pos_left h_inv_lt
      exact div_pos (sq_pos_of_ne_zero (ne_of_gt hC0)) hΛ
    have h_cancel : (C0 ^ (2 : ℕ) / Λ) * (Λ ^ (2 : ℕ) / C0 ^ (2 : ℕ)) = Λ := by
      have h_C0_sq_ne : C0 ^ (2 : ℕ) ≠ 0 := by
        rw [sq]
        exact ne_of_gt (mul_pos hC0 hC0)
      have h_L_ne' : Λ ≠ 0 := ne_of_gt hΛ
      field_simp [h_C0_sq_ne, h_L_ne']
    rw [h_cancel] at h_mul_lt
    linarith

  -- 6. Derivative of the logarithm
  have h_deriv_log : HasDerivAt (fun (y : ℝ) => log (Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / y ^ (2 : ℕ))))
      ((0 - (C0 ^ (2 : ℕ) / Λ) * (- (2 * r) / (r ^ (2 : ℕ)) ^ 2)) / (Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / r ^ (2 : ℕ)))) r := by
    exact HasDerivAt.log h_deriv_sub (ne_of_gt h_arg_pos)

  -- 7. Multiply by (γ / 2)
  have h_deriv_final : HasDerivAt (fun (y : ℝ) => (γ / 2) * log (Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / y ^ (2 : ℕ))))
      ((γ / 2) * ((0 - (C0 ^ (2 : ℕ) / Λ) * (- (2 * r) / (r ^ (2 : ℕ)) ^ 2)) / (Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / r ^ (2 : ℕ))))) r := by
    exact HasDerivAt.const_mul (γ / 2) h_deriv_log

  -- 8. Transfer derivative using congruence on eventually equal functions
  have h_deriv_V : HasDerivAt V ((γ / 2) * ((0 - (C0 ^ (2 : ℕ) / Λ) * (- (2 * r) / (r ^ (2 : ℕ)) ^ 2)) / (Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / r ^ (2 : ℕ))))) r := by
    apply HasDerivAt.congr_of_eventuallyEq h_deriv_final
    filter_upwards [h_eventual]
    intro y hy
    dsimp [V, entropic_potential_3d]
    rw [hy]

  -- 9. Simplify the derivative term to match the 3D entropic force
  have h_deriv_eq : ((γ / 2) * ((0 - (C0 ^ (2 : ℕ) / Λ) * (- (2 * r) / (r ^ (2 : ℕ)) ^ 2)) / (Λ - (C0 ^ (2 : ℕ) / Λ) * (1 / r ^ (2 : ℕ))))) =
      - entropic_force_3d γ (Λ / C0) r := by
    unfold entropic_force_3d
    have h_C_ne : C0 ≠ 0 := ne_of_gt hC0
    have h_L_ne : Λ ≠ 0 := ne_of_gt hΛ
    have h_denom_ne : (Λ / C0) ^ (2 : ℕ) * r ^ (2 : ℕ) - 1 ≠ 0 := by
      have h_r_gt_pos : (C0 / Λ) ^ (2 : ℕ) < r ^ (2 : ℕ) := by
        have h_c_l : 0 < C0 / Λ := div_pos hC0 hΛ
        exact sq_lt_sq.mpr (by rw [abs_of_pos h_c_l, abs_of_pos h_r_pos]; exact hr_gt)
      have h_div_lt : C0 ^ (2 : ℕ) / Λ ^ (2 : ℕ) < r ^ (2 : ℕ) := by
        rw [div_pow] at h_r_gt_pos
        exact h_r_gt_pos
      have h_L_sq_pos : 0 < Λ ^ (2 : ℕ) := sq_pos_of_ne_zero h_L_ne
      rw [div_lt_iff₀ h_L_sq_pos] at h_div_lt
      have h_div_r : 1 < (Λ ^ (2 : ℕ) / C0 ^ (2 : ℕ)) * r ^ (2 : ℕ) := by
        have h_C_sq_pos : 0 < C0 ^ (2 : ℕ) := sq_pos_of_ne_zero h_C_ne
        rw [div_mul_eq_mul_div]
        rw [lt_div_iff₀ h_C_sq_pos]
        rw [one_mul]
        linarith [h_div_lt]
      have h_simpl2 : (Λ / C0) ^ (2 : ℕ) * r ^ (2 : ℕ) = (Λ ^ (2 : ℕ) / C0 ^ (2 : ℕ)) * r ^ (2 : ℕ) := by
        rw [div_pow]
      rw [h_simpl2]
      linarith [h_div_r]
    field_simp [h_r_ne, h_C_ne, h_L_ne, h_denom_ne, h_arg_pos]
    ring

  rw [h_deriv_eq] at h_deriv_V
  exact h_deriv_V

-- =========================================================================
-- PART 4: Unification with the Generalized Covariance Process (GCP)
-- =========================================================================

/-- The normalized 3D continuous covariance kernel K3d(r) = C0 / (Λ * r).
    At the exclusion boundary r_crit = C0 / Λ, K3d(r_crit) = 1. -/
def K3d (C0 Λ r : ℝ) : ℝ := C0 / (Λ * r)

/-- Theorem: Normalization of K3d at the critical exclusion boundary.
    Confirms that K3d maps exactly to 1 at r_crit. -/
theorem K3d_boundary_normalized (C0 Λ : ℝ) (hC0 : 0 < C0) (hΛ : 0 < Λ) :
    K3d C0 Λ (C0 / Λ) = 1 := by
  unfold K3d
  have h_mul : Λ * (C0 / Λ) = C0 := by
    rw [mul_div_cancel₀ C0 (ne_of_gt hΛ)]
  rw [h_mul]
  exact div_self (ne_of_gt hC0)

/-- Theorem: Equivalence of the 3D Potential to the Generalized Potential.
    Proves that the 3D entropic potential energy is the exact continuous 3D specialization
    of the generalized entropic potential V(r) = (γ / 2) * log (C0 * (1 - (K r) ^ 2))
    under the mapping C0 → Λ (variance parameter) and K → K3d. -/
theorem entropic_potential_3d_eq_generalized (γ Λ C0 r : ℝ) (hC0 : 0 < C0) (hΛ : 0 < Λ) (hr : 0 < r) :
    entropic_potential_3d γ Λ C0 r = (γ / 2) * log (Λ * (1 - (K3d C0 Λ r) ^ 2)) := by
  unfold entropic_potential_3d K3d
  congr 3
  have h_sq : (C0 / (Λ * r)) ^ 2 = C0 ^ 2 / (Λ ^ 2 * r ^ 2) := by
    rw [div_pow, mul_pow]
  rw [h_sq]

#print axioms continuous_3d_potential_deriv
#print axioms continuous_3d_exclusion_limit
#print axioms K3d_boundary_normalized
#print axioms entropic_potential_3d_eq_generalized
