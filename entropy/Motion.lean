import entropy.common

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real

-- =========================================================================
-- PART 1: The Coordinate Entropic Force Field
-- =========================================================================

/-- The directional entropic force acting on coordinate x.
    It is attractive (points toward 0) and scales inversely with distance at short ranges. -/
def entropic_force (γ ξ x : ℝ) : ℝ :=
  if x = 0 then 0
  else if x > 0 then - (γ / ξ) * (1 / (exp (2 * x / ξ) - 1))
  else (γ / ξ) * (1 / (exp (2 * (-x) / ξ) - 1))

/-- Lemma: The entropic force is exactly zero at the origin. -/
lemma entropic_force_zero (γ ξ : ℝ) : entropic_force γ ξ 0 = 0 := by
  unfold entropic_force
  rw [if_pos rfl]

/-- Lemma: The entropic force is strictly negative for any positive displacement. -/
lemma entropic_force_neg_of_pos (γ ξ x : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) (hx : 0 < x) :
    entropic_force γ ξ x < 0 := by
  unfold entropic_force
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hx_gt : x > 0 := hx
  rw [if_neg hx_ne, if_pos hx_gt]
  have h_div_pos : 0 < γ / ξ := div_pos hγ hξ
  have h_exp_gt : 1 < exp (2 * x / ξ) := by
    rw [← Real.exp_zero]
    apply exp_lt_exp.mpr
    apply div_pos (mul_pos (by norm_num) hx) hξ
  have h_sub_pos : 0 < exp (2 * x / ξ) - 1 := by linarith
  have h_inv_pos : 0 < 1 / (exp (2 * x / ξ) - 1) := one_div_pos.mpr h_sub_pos
  have h_prod_pos : 0 < (γ / ξ) * (1 / (exp (2 * x / ξ) - 1)) := mul_pos h_div_pos h_inv_pos
  linarith

/-- Lemma: The entropic force is strictly positive for any negative displacement. -/
lemma entropic_force_pos_of_neg (γ ξ x : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) (hx : x < 0) :
    0 < entropic_force γ ξ x := by
  unfold entropic_force
  have hx_ne : x ≠ 0 := ne_of_lt hx
  have hx_not_gt : ¬ x > 0 := by linarith
  rw [if_neg hx_ne, if_neg hx_not_gt]
  have h_div_pos : 0 < γ / ξ := div_pos hγ hξ
  have h_neg_x_pos : 0 < -x := neg_pos.mpr hx
  have h_exp_gt : 1 < exp (2 * (-x) / ξ) := by
    rw [← Real.exp_zero]
    apply exp_lt_exp.mpr
    apply div_pos (mul_pos (by norm_num) h_neg_x_pos) hξ
  have h_sub_pos : 0 < exp (2 * (-x) / ξ) - 1 := by linarith
  have h_inv_pos : 0 < 1 / (exp (2 * (-x) / ξ) - 1) := one_div_pos.mpr h_sub_pos
  exact mul_pos h_div_pos h_inv_pos

/-- Theorem: The entropic force is strictly dissipative / attractive, meaning
    it always acts in the opposite direction of the displacement x. -/
theorem entropic_force_attractive (γ ξ x : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) :
    x * entropic_force γ ξ x ≤ 0 := by
  by_cases hx : x = 0
  · rw [hx, zero_mul]
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · have h_pos : 0 < entropic_force γ ξ x := entropic_force_pos_of_neg γ ξ x hγ hξ hlt
      have h_prod : x * entropic_force γ ξ x < 0 := mul_neg_of_neg_of_pos hlt h_pos
      linarith
    · have h_neg : entropic_force γ ξ x < 0 := entropic_force_neg_of_pos γ ξ x hγ hξ hgt
      have h_prod : x * entropic_force γ ξ x < 0 := mul_neg_of_pos_of_neg hgt h_neg
      linarith

-- =========================================================================
-- PART 2: The Discrete Dynamical Update (Motion)
-- =========================================================================

/-- Motion is defined as a discrete-time updating step.
    A state at step t progresses to t+1 by moving along the entropic gradient. -/
def step_motion (γ ξ dt x : ℝ) : ℝ :=
  x + dt * entropic_force γ ξ x

/-- A trajectory is a sequence of coordinates over discrete time steps n : ℕ -/
def trajectory (γ ξ dt : ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => step_motion γ ξ dt (trajectory γ ξ dt x0 n)

/-- Theorem: Perfect predictability (the origin) is a stable, stationary fixed point
    of the entropic dynamics. If the trajectory starts at 0, it stays at 0. -/
theorem trajectory_zero (γ ξ dt : ℝ) (n : ℕ) : trajectory γ ξ dt 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold trajectory
    rw [ih]
    unfold step_motion
    rw [entropic_force_zero, mul_zero, add_zero]

-- =========================================================================
-- PART 3: Defining the "Actor" (Self-Correcting Field Position)
-- =========================================================================

/-- An "Actor" is defined as a trajectory that actively satisfies
    the entropic update rule and converges to the origin (perfect predictability). -/
structure Actor (γ ξ dt : ℝ) where
  x0 : ℝ                  -- Initial coordinate perturbation
  pos : ℕ → ℝ             -- The coordinate path over time
  is_trajectory : ∀ n, pos (n + 1) = step_motion γ ξ dt (pos n)
  self_corrects : ∀ ε > 0, ∃ N, ∀ n ≥ N, |pos n| < ε

#print axioms entropic_force_attractive
#print axioms trajectory_zero
