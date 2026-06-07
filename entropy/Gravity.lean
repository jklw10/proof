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
    The mutual force is symmetric but opposite in sign. -/
theorem mutual_force_symmetric (γ ξ x1 x2 : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) :
    mutual_force γ ξ x1 x2 = - mutual_force γ ξ x2 x1 := by
  unfold mutual_force entropic_force
  by_cases h : x1 - x2 = 0
  · have h_rev : x2 - x1 = 0 := by linarith
    rw [if_pos h, if_pos h_rev, neg_zero]
  · have h_ne : x1 - x2 ≠ 0 := h
    rcases lt_or_gt_of_ne h_ne with hlt | hgt
    · have h_gt2 : x2 - x1 > 0 := by linarith
      have h_not_gt : ¬ x1 - x2 > 0 := by linarith
      have h_rev_ne : x2 - x1 ≠ 0 := ne_of_gt h_gt2
      rw [if_neg h_ne, if_neg h_not_gt]
      rw [if_neg h_rev_ne, if_pos h_gt2]
      have h_eq : -(x1 - x2) = x2 - x1 := by ring
      rw [h_eq]
      ring
    · have h_lt2 : x2 - x1 < 0 := by linarith
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

/-- Theorem: The force of entropic gravity strictly decays as distance increases. -/
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

/-- Theorem: Conservative Field of Entropic Gravity.
    Now formulated using the explicit parameters of the unified covariance process. -/
theorem mutual_potential_gradient {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess T E) (γ ξ : ℝ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (h_log_z : log P.z = -1 / ξ) (x1 x2 : ℝ) (h_sep : x2 < x1) :
    let U := fun (y : ℝ) => (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * |y - x2|)))
    HasDerivAt U (- mutual_force γ ξ x1 x2) x1 := by
  intro U
  have h_nhds : Ioi x2 ∈ nhds x1 := IsOpen.mem_nhds isOpen_Ioi h_sep
  have h_local : ∀ᶠ y in nhds x1, U y = (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * (y - x2)))) := by
    filter_upwards [h_nhds]
    intro y hy
    dsimp [U]
    have h_abs : |y - x2| = y - x2 := abs_of_pos (sub_pos.mpr hy)
    rw [h_abs]

  let V := fun (u : ℝ) => (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * u)))

  have h_deriv_V : HasDerivAt V (- entropic_force γ ξ (x1 - x2)) (x1 - x2) := by
    apply continuous_potential_deriv P γ ξ hγ hξ h_log_z (x1 - x2) (sub_pos.mpr h_sep)

  have h_deriv_g : HasDerivAt (fun y => y - x2) 1 x1 := by
    have h_id : HasDerivAt (fun y => y) 1 x1 := hasDerivAt_id x1
    have h_const : HasDerivAt (fun _ => x2) 0 x1 := hasDerivAt_const x1 x2
    have h_sub := HasDerivAt.sub h_id h_const
    rw [sub_zero] at h_sub
    exact h_sub

  have h_deriv_comp : HasDerivAt (V ∘ (fun y => y - x2)) (- entropic_force γ ξ (x1 - x2) * 1) x1 := by
    exact HasDerivAt.comp x1 h_deriv_V h_deriv_g
  rw [mul_one] at h_deriv_comp

  have h_final : HasDerivAt U (- mutual_force γ ξ x1 x2) x1 := by
    unfold mutual_force
    apply HasDerivAt.congr_of_eventuallyEq h_deriv_comp
    filter_upwards [h_local]
    intro y hy
    exact hy
  exact h_final
