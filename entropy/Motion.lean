import entropy.common
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

lemma entropic_force_zero (γ ξ : ℝ) : entropic_force γ ξ 0 = 0 := by
  unfold entropic_force
  rw [if_pos rfl]

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
-- PART 2: Duality Proofs Grounded in the Unified Process Model
-- =========================================================================

lemma real_pow_lt_one (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (n : ℕ) (hn : 0 < n) : z ^ n < 1 := by
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hz0]
  apply exp_lt_one_iff.mpr
  have h_log_neg : log z < 0 := (log_neg_iff hz0).mpr hz1
  have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  nlinarith

/-- Theorem: The Discrete Duality Theorem.
    Now formulated using the explicit parameters of the unified covariance process. -/
theorem discrete_potential_difference {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess T E) (γ : ℝ) (r : ℕ)
    (hγ : 0 < γ) (hr : 0 < r) :
    let V := fun (n : ℕ) => (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * n)))
    V (r + 1) - V r = (γ / 2) * log ((1 - P.z ^ (2 * (r + 1))) / (1 - P.z ^ (2 * r))) := by
  intro V
  dsimp [V]
  have h_factor : (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * (r + 1)))) - (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * r))) =
      (γ / 2) * (log (P.C0 * (1 - P.z ^ (2 * (r + 1)))) - log (P.C0 * (1 - P.z ^ (2 * r)))) := by ring
  rw [h_factor]
  congr 1
  have h_z_r1 : 0 < 1 - P.z ^ (2 * (r + 1)) := by
    have h_pow : P.z ^ (2 * (r + 1)) < 1 := by
      apply real_pow_lt_one P.z P.hz0 P.hz1 (2 * (r + 1)) (by positivity)
    linarith
  have h_z_r : 0 < 1 - P.z ^ (2 * r) := by
    have h_pow : P.z ^ (2 * r) < 1 := by
      apply real_pow_lt_one P.z P.hz0 P.hz1 (2 * r) (by positivity)
    linarith
  have h_log1 : log (P.C0 * (1 - P.z ^ (2 * (r + 1)))) = log P.C0 + log (1 - P.z ^ (2 * (r + 1))) := by
    rw [log_mul (ne_of_gt P.hC0) (ne_of_gt h_z_r1)]
  have h_log2 : log (P.C0 * (1 - P.z ^ (2 * r))) = log P.C0 + log (1 - P.z ^ (2 * r)) := by
    rw [log_mul (ne_of_gt P.hC0) (ne_of_gt h_z_r)]
  rw [h_log1, h_log2]
  have h_sub_eq : (log P.C0 + log (1 - P.z ^ (2 * (r + 1)))) - (log P.C0 + log (1 - P.z ^ (2 * r))) =
      log (1 - P.z ^ (2 * (r + 1))) - log (1 - P.z ^ (2 * r)) := by ring
  rw [h_sub_eq, log_div (ne_of_gt h_z_r1) (ne_of_gt h_z_r)]

/-- Theorem: The Continuous Duality Theorem.
    Now formulated using the explicit parameters of the unified covariance process. -/
theorem continuous_potential_deriv {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess T E) (γ ξ : ℝ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (h_log_z : log P.z = -1 / ξ) (x : ℝ) (hx : 0 < x) :
    let V := fun (y : ℝ) => (γ / 2) * log (P.C0 * (1 - P.z ^ (2 * y)))
    HasDerivAt V (- entropic_force γ ξ x) x := by
  intro V
  have h_V_eq : ∀ y > 0, V y = (γ / 2) * log (P.C0 * (1 - exp (2 * y * log P.z))) := by
    intro y hy
    dsimp [V]
    congr 2
    rw [Real.rpow_def_of_pos P.hz0]
    ring_nf
  have h_linear : HasDerivAt (fun y => 2 * y * log P.z) (2 * log P.z) x := by
    have : (fun y => 2 * y * log P.z) = (fun y => y * (2 * log P.z)) := by ext; ring
    rw [this]
    exact hasDerivAt_mul_const (2 * log P.z)
  have h_deriv_exp_pre : HasDerivAt (fun y => exp (2 * y * log P.z)) (exp (2 * x * log P.z) * (2 * log P.z)) x := by
    exact HasDerivAt.exp h_linear
  have h_deriv_exp : HasDerivAt (fun y => exp (2 * y * log P.z)) (2 * log P.z * exp (2 * x * log P.z)) x := by
    have h_eq : exp (2 * x * log P.z) * (2 * log P.z) = 2 * log P.z * exp (2 * x * log P.z) := by ring
    rw [← h_eq]
    exact h_deriv_exp_pre
  have h_sub_pos : ∀ y > 0, 0 < 1 - exp (2 * y * log P.z) := by
    intro y hy
    have h_log_neg : log P.z < 0 := (log_neg_iff P.hz0).mpr P.hz1
    have h_prod_neg : 2 * y * log P.z < 0 := by
      have h_pos_coeff : 0 < 2 * y := by linarith
      exact mul_neg_of_pos_of_neg h_pos_coeff h_log_neg
    have h_exp_lt1 : exp (2 * y * log P.z) < 1 := exp_lt_one_iff.mpr h_prod_neg
    linarith
  have h_arg_pos : ∀ y > 0, 0 < P.C0 * (1 - exp (2 * y * log P.z)) := by
    intro y hy
    exact mul_pos P.hC0 (h_sub_pos y hy)
  have h_sub_pre : HasDerivAt ((fun _ => (1 : ℝ)) - (fun y => exp (2 * y * log P.z))) (0 - (2 * log P.z * exp (2 * x * log P.z))) x := by
    have h1 : HasDerivAt (fun _ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
    exact HasDerivAt.sub h1 h_deriv_exp
  have h_deriv_arg : HasDerivAt (fun y => P.C0 * (1 - exp (2 * y * log P.z))) (-P.C0 * (2 * log P.z * exp (2 * x * log P.z))) x := by
    have h_fn_eq : (fun y => 1 - exp (2 * y * log P.z)) = (fun _ => (1 : ℝ)) - (fun y => exp (2 * y * log P.z)) := by rfl
    have h_val_eq : - (2 * log P.z * exp (2 * x * log P.z)) = 0 - (2 * log P.z * exp (2 * x * log P.z)) := by ring
    have h_sub : HasDerivAt (fun y => 1 - exp (2 * y * log P.z)) (- (2 * log P.z * exp (2 * x * log P.z))) x := by
      rw [h_fn_eq, h_val_eq]
      exact h_sub_pre
    have h_mul := HasDerivAt.const_mul P.C0 h_sub
    have h_ring : P.C0 * - (2 * log P.z * exp (2 * x * log P.z)) = -P.C0 * (2 * log P.z * exp (2 * x * log P.z)) := by ring
    rw [h_ring] at h_mul
    exact h_mul
  have h_deriv_log_pre : HasDerivAt (fun y => log (P.C0 * (1 - exp (2 * y * log P.z))))
      (-P.C0 * (2 * log P.z * exp (2 * x * log P.z)) / (P.C0 * (1 - exp (2 * x * log P.z)))) x := by
    exact HasDerivAt.log h_deriv_arg (ne_of_gt (h_arg_pos x hx))
  have h_deriv_log : HasDerivAt (fun y => log (P.C0 * (1 - exp (2 * y * log P.z))))
      (1 / (P.C0 * (1 - exp (2 * x * log P.z))) * (-P.C0 * (2 * log P.z * exp (2 * x * log P.z)))) x := by
    have h_eq : -P.C0 * (2 * log P.z * exp (2 * x * log P.z)) / (P.C0 * (1 - exp (2 * x * log P.z))) =
        1 / (P.C0 * (1 - exp (2 * x * log P.z))) * (-P.C0 * (2 * log P.z * exp (2 * x * log P.z))) := by ring
    rw [← h_eq]
    exact h_deriv_log_pre
  have h_deriv_final := HasDerivAt.const_mul (γ / 2) h_deriv_log
  have h_V_deriv : HasDerivAt V ((γ / 2) * (1 / (P.C0 * (1 - exp (2 * x * log P.z))) * (-P.C0 * (2 * log P.z * exp (2 * x * log P.z))))) x := by
    apply HasDerivAt.congr_of_eventuallyEq h_deriv_final
    filter_upwards [Ioi_mem_nhds hx]
    intro y hy
    exact h_V_eq y hy
  have h_force_eq : (γ / 2) * (1 / (P.C0 * (1 - exp (2 * x * log P.z))) * (-P.C0 * (2 * log P.z * exp (2 * x * log P.z)))) =
      - entropic_force γ ξ x := by
    unfold entropic_force
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hx_gt : x > 0 := hx
    rw [if_neg hx_ne, if_pos hx_gt]
    have h_log_neg : log P.z = -1 / ξ := h_log_z
    have h_exp_minus : exp (2 * x * log P.z) = 1 / exp (2 * x / ξ) := by
      rw [h_log_neg]
      have : 2 * x * (-1 / ξ) = - (2 * x / ξ) := by ring
      rw [this, exp_neg, inv_eq_one_div]
    have h_exp_gt1 : 1 < exp (2 * x / ξ) := by
      rw [← exp_zero]
      apply exp_lt_exp.mpr
      apply div_pos (mul_pos (by norm_num) hx) hξ
    have h_denom_ne1 : exp (2 * x / ξ) - 1 ≠ 0 := by linarith
    have h_denom_ne2 : 1 - exp (2 * x * log P.z) ≠ 0 := by
      rw [h_exp_minus]
      have h_exp_ne : exp (2 * x / ξ) ≠ 0 := ne_of_gt (exp_pos _)
      intro h_zero
      field_simp [h_exp_ne] at h_zero
      rw [mul_zero] at h_zero
      linarith [h_exp_gt1, h_zero]
    have h_C0_ne : P.C0 ≠ 0 := ne_of_gt P.hC0
    have h_xi_ne : ξ ≠ 0 := ne_of_gt hξ
    rw [h_exp_minus, h_log_neg]
    field_simp [h_denom_ne1, h_C0_ne, h_xi_ne, ne_of_gt (exp_pos (2 * x / ξ))]
  rw [h_force_eq] at h_V_deriv
  exact h_V_deriv

-- =========================================================================
-- PART 3: The Discrete Dynamical Update (Motion)
-- =========================================================================

def step_motion (γ ξ dt x : ℝ) : ℝ :=
  x + dt * entropic_force γ ξ x

def trajectory (γ ξ dt : ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => step_motion γ ξ dt (trajectory γ ξ dt x0 n)

theorem trajectory_zero (γ ξ dt : ℝ) (n : ℕ) : trajectory γ ξ dt 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold trajectory
    rw [ih]
    unfold step_motion
    rw [entropic_force_zero, mul_zero, add_zero]

-- =========================================================================
-- PART 4: Defining the "Actor"
-- =========================================================================

structure Actor (γ ξ dt : ℝ) where
  x0 : ℝ
  pos : ℕ → ℝ
  is_trajectory : ∀ n, pos (n + 1) = step_motion γ ξ dt (pos n)
  self_corrects : ∀ ε > 0, ∃ N, ∀ n ≥ N, |pos n| < ε

def origin_actor (γ ξ dt : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) (hdt : 0 < dt) : Actor γ ξ dt where
  x0 := 0
  pos := trajectory γ ξ dt 0
  is_trajectory := by
    intro n
    rfl
  self_corrects := by
    intro ε hε
    use 0
    intro n hn
    rw [trajectory_zero]
    rw [abs_zero]
    exact hε
