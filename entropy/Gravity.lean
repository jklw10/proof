import entropy.motion

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
-- PART 1: The Mutual Force Definition & Newton's Third Law
-- =========================================================================

/-- The mutual entropic gravitational force exerted on particle 1 at x1
    by particle 2 at x2. It is purely attractive. -/
def mutual_force (γ ξ x1 x2 : ℝ) : ℝ :=
  entropic_force γ ξ (x1 - x2)

/-- Theorem: Newton's Third Law of Entropic Gravity.
    The mutual force is symmetric but opposite in sign: F_12 = - F_21. -/
theorem mutual_force_symmetric (γ ξ x1 x2 : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) :
    mutual_force γ ξ x1 x2 = - mutual_force γ ξ x2 x1 := by
  unfold mutual_force entropic_force
  by_cases h : x1 - x2 = 0
  · have h_rev : x2 - x1 = 0 := by linarith
    rw [if_pos h, if_pos h_rev, neg_zero]
  · have h_ne : x1 - x2 ≠ 0 := h
    rcases lt_or_gt_of_ne h_ne with hlt | hgt
    · -- Case: x1 - x2 < 0 (meaning x2 - x1 > 0)
      have h_gt2 : x2 - x1 > 0 := by linarith
      have h_not_gt : ¬ x1 - x2 > 0 := by linarith
      have h_rev_ne : x2 - x1 ≠ 0 := ne_of_gt h_gt2
      rw [if_neg h_ne, if_neg h_not_gt]
      rw [if_neg h_rev_ne, if_pos h_gt2]
      have h_eq : -(x1 - x2) = x2 - x1 := by ring
      rw [h_eq]
      ring
    · -- Case: x1 - x2 > 0 (meaning x2 - x1 < 0)
      have h_lt2 : x2 - x1 < 0 := by linarith
      have h_not_gt2 : ¬ x2 - x1 > 0 := by linarith
      have h_rev_ne : x2 - x1 ≠ 0 := ne_of_lt h_lt2
      rw [if_neg h_ne, if_pos hgt]
      rw [if_neg h_rev_ne, if_neg h_not_gt2]
      have h_eq : -(x2 - x1) = x1 - x2 := by ring
      rw [h_eq]
      ring

-- =========================================================================
-- PART 2: Asymptotic Monotonicity (Far-field vs Near-field)
-- =========================================================================

/-- Theorem: The force of entropic gravity strictly decays as distance increases.
    For any separations r1 < r2, the magnitude of the force at r2 is strictly
    smaller than at r1. -/
theorem mutual_force_monotone (γ ξ r1 r2 : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ)
    (hr1 : 0 < r1) (hr2 : r1 < r2) :
    |entropic_force γ ξ r2| < |entropic_force γ ξ r1| := by
  have h_f1_neg : entropic_force γ ξ r1 < 0 := entropic_force_neg_of_pos γ ξ r1 hγ hξ hr1
  have h_f2_neg : entropic_force γ ξ r2 < 0 := entropic_force_neg_of_pos γ ξ r2 hγ hξ (by linarith)
  rw [abs_of_neg h_f1_neg, abs_of_neg h_f2_neg]
  simp only [neg_lt_neg_iff]
  unfold entropic_force
  have hr1_ne : r1 ≠ 0 := ne_of_gt hr1
  have hr2_ne : r2 ≠ 0 := ne_of_gt (by linarith)
  rw [if_neg hr1_ne, if_pos hr1, if_neg hr2_ne, if_pos (by linarith : r2 > 0)]
  have h_div_pos : 0 < γ / ξ := div_pos hγ hξ
  have h_exp_gt1 : 1 < exp (2 * r1 / ξ) := by
    rw [← Real.exp_zero]
    apply exp_lt_exp.mpr
    apply div_pos (mul_pos (by norm_num) hr1) hξ
  have h_exp_gt2 : 1 < exp (2 * r2 / ξ) := by
    rw [← Real.exp_zero]
    apply exp_lt_exp.mpr
    apply div_pos (mul_pos (by norm_num) (by linarith : 0 < r2)) hξ
  have h_denom1_pos : 0 < exp (2 * r1 / ξ) - 1 := by linarith [h_exp_gt1]
  have h_denom2_pos : 0 < exp (2 * r2 / ξ) - 1 := by linarith [h_exp_gt2]
  have h_inv_lt : 1 / (exp (2 * r2 / ξ) - 1) < 1 / (exp (2 * r1 / ξ) - 1) := by
    rw [one_div_lt_one_div h_denom2_pos h_denom1_pos]
    have h_sub_cancel : exp (2 * r1 / ξ) - 1 < exp (2 * r2 / ξ) - 1 ↔ exp (2 * r1 / ξ) < exp (2 * r2 / ξ) := by
      constructor <;> intro h <;> linarith
    rw [h_sub_cancel]
    apply exp_lt_exp.mpr
    have h_num_lt : 2 * r1 < 2 * r2 := by linarith
    exact div_lt_div_of_pos_right h_num_lt hξ
  have h_diff_pos : 0 < 1 / (exp (2 * r1 / ξ) - 1) - 1 / (exp (2 * r2 / ξ) - 1) := by linarith [h_inv_lt]
  nlinarith [h_div_pos, h_diff_pos]

-- =========================================================================
-- PART 3: The Conservative Potential Field (Gradient Law)
-- =========================================================================

/-- The mutual entropic potential energy between two particles at x1 and x2. -/
def mutual_potential (γ C0 z : ℝ) (x1 x2 : ℝ) : ℝ :=
  (γ / 2) * log (C0 * (1 - z ^ (2 * |x1 - x2|)))

/-- Theorem: Conservative Field of Entropic Gravity.
    The mutual entropic force is the negative gradient of the mutual entropic potential.
    For any particle separation, the derivative of the potential with respect to x1
    is exactly equal to - F_12. -/
theorem mutual_potential_gradient (γ ξ C0 z : ℝ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (hz0 : 0 < z) (hz1 : z < 1)
    (h_log_z : log z = -1 / ξ) (x1 x2 : ℝ) (h_sep : x2 < x1) (hC0 : 0 < C0) :
    let U := fun (y : ℝ) => mutual_potential γ C0 z y x2
    HasDerivAt U (- mutual_force γ ξ x1 x2) x1 := by
  intro U
  -- Locally around x1, the absolute value |y - x2| simplifies to y - x2 because x2 < x1.
  have h_nhds : Ioi x2 ∈ nhds x1 := IsOpen.mem_nhds isOpen_Ioi h_sep
  have h_local : ∀ᶠ y in nhds x1, U y = (γ / 2) * log (C0 * (1 - z ^ (2 * (y - x2)))) := by
    filter_upwards [h_nhds]
    intro y hy
    dsimp [U, mutual_potential]
    have h_abs : |y - x2| = y - x2 := abs_of_pos (sub_pos.mpr hy)
    rw [h_abs]

  -- Let V(u) be the shifted entropic potential
  let V := fun (u : ℝ) => (γ / 2) * log (C0 * (1 - z ^ (2 * u)))

  -- V has derivative - entropic_force at (x1 - x2) by our continuous potential derivative theorem
  have h_deriv_V : HasDerivAt V (- entropic_force γ ξ (x1 - x2)) (x1 - x2) := by
    apply continuous_potential_deriv γ ξ C0 z hγ hξ hz0 hz1 h_log_z (x1 - x2) (sub_pos.mpr h_sep) hC0

  -- The coordinate shift function g(y) = y - x2 has derivative 1
  have h_deriv_g : HasDerivAt (fun y => y - x2) 1 x1 := by
    have h_id : HasDerivAt (fun y => y) 1 x1 := hasDerivAt_id x1
    have h_const : HasDerivAt (fun _ => x2) 0 x1 := hasDerivAt_const x1 x2
    have h_sub := HasDerivAt.sub h_id h_const
    rw [sub_zero] at h_sub
    exact h_sub

  -- By the Chain Rule, the composition V ∘ (fun y => y - x2) has derivative - entropic_force * 1
  have h_deriv_comp : HasDerivAt (V ∘ (fun y => y - x2)) (- entropic_force γ ξ (x1 - x2) * 1) x1 := by
    exact HasDerivAt.comp x1 h_deriv_V h_deriv_g
  rw [mul_one] at h_deriv_comp

  -- Transfer the derivative to U using the local neighborhood equivalence
  have h_final : HasDerivAt U (- mutual_force γ ξ x1 x2) x1 := by
    unfold mutual_force
    apply HasDerivAt.congr_of_eventuallyEq h_deriv_comp
    filter_upwards [h_local]
    intro y hy
    exact hy
  exact h_final

#print axioms mutual_potential_gradient
#print axioms mutual_force_symmetric
#print axioms mutual_force_monotone
