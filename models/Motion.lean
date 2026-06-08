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
-- PART 1: The Generalized Coordinate Entropic Force Field
-- =========================================================================

/-- The generalized entropic force acting on a coordinate with separation r. -/
def generalized_entropic_force (γ : ℝ) (Kr : ℝ) (K'r : ℝ) : ℝ :=
  γ * (Kr * K'r) / (1 - Kr ^ 2)

/-- The directional coordinate force acting on x (pulling it toward 0).
    It is purely attractive and scales with the covariance kernel K and its derivative K'. -/
def generalized_coordinate_force (γ : ℝ) (K : ℝ → ℝ) (K' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0
  else if x > 0 then generalized_entropic_force γ (K x) (K' x)
  else - generalized_entropic_force γ (K (-x)) (K' (-x))

lemma generalized_coordinate_force_zero (γ : ℝ) (K K' : ℝ → ℝ) :
    generalized_coordinate_force γ K K' 0 = 0 := by
  unfold generalized_coordinate_force
  rw [if_pos rfl]

lemma generalized_coordinate_force_neg_of_pos (γ : ℝ) (K K' : ℝ → ℝ) (x : ℝ) (hγ : 0 < γ)
    (hx : 0 < x) (hK : 0 < K x) (hK' : K' x < 0) (h_bound : (K x)^2 < 1) :
    generalized_coordinate_force γ K K' x < 0 := by
  unfold generalized_coordinate_force
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hx_gt : x > 0 := hx
  rw [if_neg hx_ne, if_pos hx_gt]
  unfold generalized_entropic_force
  have h_num : γ * (K x * K' x) < 0 := by
    have h_mul : K x * K' x < 0 := mul_neg_of_pos_of_neg hK hK'
    exact mul_neg_of_pos_of_neg hγ h_mul
  have h_denom : 0 < 1 - (K x)^2 := by linarith
  exact div_neg_of_neg_of_pos h_num h_denom

lemma generalized_coordinate_force_pos_of_neg (γ : ℝ) (K K' : ℝ → ℝ) (x : ℝ) (hγ : 0 < γ)
    (hx : x < 0) (hK : 0 < K (-x)) (hK' : K' (-x) < 0) (h_bound : (K (-x))^2 < 1) :
    0 < generalized_coordinate_force γ K K' x := by
  unfold generalized_coordinate_force
  have hx_ne : x ≠ 0 := ne_of_lt hx
  have hx_not_gt : ¬ x > 0 := by linarith
  rw [if_neg hx_ne, if_neg hx_not_gt]
  unfold generalized_entropic_force
  have h_num : γ * (K (-x) * K' (-x)) < 0 := by
    have h_mul : K (-x) * K' (-x) < 0 := mul_neg_of_pos_of_neg hK hK'
    exact mul_neg_of_pos_of_neg hγ h_mul
  have h_denom : 0 < 1 - (K (-x))^2 := by linarith
  have h_div_neg : γ * (K (-x) * K' (-x)) / (1 - (K (-x))^2) < 0 := div_neg_of_neg_of_pos h_num h_denom
  linarith

/-- Theorem: Purely attractive behavior.
    For any coordinate x, the work product x * F(x) is non-positive,
    confirming that the force always acts in a restoring direction toward 0. -/
theorem generalized_coordinate_force_attractive (γ : ℝ) (K K' : ℝ → ℝ) (x : ℝ) (hγ : 0 < γ)
    (hK_pos : ∀ r > 0, 0 < K r) (hK'_neg : ∀ r > 0, K' r < 0) (h_bound : ∀ r > 0, (K r)^2 < 1) :
    x * generalized_coordinate_force γ K K' x ≤ 0 := by
  by_cases hx : x = 0
  · rw [hx, zero_mul]
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · have h_pos : 0 < generalized_coordinate_force γ K K' x := by
        have h_neg_x : -x > 0 := neg_pos.mpr hlt
        exact generalized_coordinate_force_pos_of_neg γ K K' x hγ hlt (hK_pos (-x) h_neg_x) (hK'_neg (-x) h_neg_x) (h_bound (-x) h_neg_x)
      have h_prod : x * generalized_coordinate_force γ K K' x < 0 := mul_neg_of_neg_of_pos hlt h_pos
      linarith
    · have h_neg : generalized_coordinate_force γ K K' x < 0 := by
        exact generalized_coordinate_force_neg_of_pos γ K K' x hγ hgt (hK_pos x hgt) (hK'_neg x hgt) (h_bound x hgt)
      have h_prod : x * generalized_coordinate_force γ K K' x < 0 := mul_neg_of_pos_of_neg hgt h_neg
      linarith

-- =========================================================================
-- PART 2: Duality Proofs Grounded in the Generalized Process Model
-- =========================================================================

/-- Theorem: The Generalized Discrete Duality Theorem.
    Computes the exact discrete potential difference between successive shell layers
    for any generalized covariance kernel K. -/
theorem generalized_discrete_potential_difference {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : GeneralizedCovarianceProcess T E) (γ : ℝ) (r : ℕ)
    (hγ : 0 < γ) (hr : 0 < r)
    (h_bound_r : (P.K (r : ℝ))^2 < 1) (h_bound_r1 : (P.K (r + 1 : ℝ))^2 < 1) :
    let V := fun (n : ℕ) => (γ / 2) * log (P.C0 * (1 - (P.K (n : ℝ))^2))
    V (r + 1) - V r = (γ / 2) * log ((1 - (P.K (r + 1 : ℝ))^2) / (1 - (P.K (r : ℝ))^2)) := by
  intro V
  dsimp [V]
  push_cast at *
  have h_z_r1 : 0 < 1 - (P.K (↑r + 1))^2 := by linarith
  have h_z_r : 0 < 1 - (P.K ↑r)^2 := by linarith
  have h_log1 : log (P.C0 * (1 - (P.K (↑r + 1))^2)) = log P.C0 + log (1 - (P.K (↑r + 1))^2) := by
    exact log_mul (ne_of_gt P.hC0) (ne_of_gt h_z_r1)
  have h_log2 : log (P.C0 * (1 - (P.K ↑r)^2)) = log P.C0 + log (1 - (P.K ↑r)^2) := by
    exact log_mul (ne_of_gt P.hC0) (ne_of_gt h_z_r)
  rw [h_log1, h_log2]
  rw [log_div (ne_of_gt h_z_r1) (ne_of_gt h_z_r)]
  ring

/-- Theorem: The Generalized Continuous Duality Theorem.
    The continuous coordinate force field is the exact negative derivative
    of the generalized potential for any arbitrary covariance kernel K. -/
theorem generalized_potential_deriv {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : GeneralizedCovarianceProcess T E) (γ : ℝ) (hγ : 0 < γ)
    (x : ℝ) (hx : 0 < x) (K' : ℝ → ℝ) (hK_deriv : HasDerivAt P.K (K' x) x)
    (h_bounds : (P.K x) ^ 2 < 1) :
    let V := fun (y : ℝ) => (γ / 2) * log (P.C0 * (1 - (P.K y) ^ 2))
    HasDerivAt V (- generalized_coordinate_force γ P.K K' x) x := by
  intro V

  -- 1. Derivative of y ↦ (P.K y)^2 via Chain Rule
  have h_deriv_sq : HasDerivAt (fun y => (P.K y) ^ 2) (2 * P.K x * K' x) x := by
    have h_pow : HasDerivAt (fun u => u ^ 2) (2 * P.K x) (P.K x) := by
      have h := hasDerivAt_pow 2 (P.K x)
      have h_simpl : ((2 : ℕ) : ℝ) * P.K x ^ (2 - 1) = 2 * P.K x := by
        have h1 : 2 - 1 = 1 := rfl
        rw [h1, pow_one, Nat.cast_two]
      rw [h_simpl] at h
      exact h
    have h_comp := HasDerivAt.comp x h_pow hK_deriv
    exact h_comp

  -- 2. Derivative of y ↦ 1 - (P.K y)^2
  have h_deriv_sub : HasDerivAt (fun y => 1 - (P.K y) ^ 2) (0 - 2 * P.K x * K' x) x := by
    have h_const : HasDerivAt (fun _ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
    exact HasDerivAt.sub h_const h_deriv_sq

  -- 3. Derivative of y ↦ P.C0 * (1 - (P.K y)^2)
  have h_deriv_mul : HasDerivAt (fun y => P.C0 * (1 - (P.K y) ^ 2)) (P.C0 * (0 - 2 * P.K x * K' x)) x := by
    exact HasDerivAt.const_mul P.C0 h_deriv_sub

  -- 4. Prove that the argument inside the logarithm is strictly positive
  have h_pos : 0 < P.C0 * (1 - (P.K x) ^ 2) := by
    have h_sub : 0 < 1 - (P.K x) ^ 2 := by linarith
    exact mul_pos P.hC0 h_sub

  -- 5. Derivative of the logarithm
  have h_deriv_log : HasDerivAt (fun y => log (P.C0 * (1 - (P.K y) ^ 2)))
      (P.C0 * (0 - 2 * P.K x * K' x) / (P.C0 * (1 - (P.K x) ^ 2))) x := by
    exact HasDerivAt.log h_deriv_mul (ne_of_gt h_pos)

  -- 6. Multiply by (γ / 2)
  have h_deriv_final : HasDerivAt (fun y => (γ / 2) * log (P.C0 * (1 - (P.K y) ^ 2)))
      ((γ / 2) * (P.C0 * (0 - 2 * P.K x * K' x) / (P.C0 * (1 - (P.K x) ^ 2)))) x := by
    exact HasDerivAt.const_mul (γ / 2) h_deriv_log

  -- 7. Simplify the derivative term to match the generalized coordinate entropic force
  have h_simplify : ((γ / 2) * (P.C0 * (0 - 2 * P.K x * K' x) / (P.C0 * (1 - (P.K x) ^ 2)))) =
      - generalized_coordinate_force γ P.K K' x := by
    unfold generalized_coordinate_force
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hx_gt : x > 0 := hx
    rw [if_neg hx_ne, if_pos hx_gt]
    unfold generalized_entropic_force
    have h_C0_ne : P.C0 ≠ 0 := ne_of_gt P.hC0
    have h_denom_ne : 1 - (P.K x) ^ 2 ≠ 0 := by linarith
    field_simp [h_C0_ne, h_denom_ne]
    ring

  rw [h_simplify] at h_deriv_final
  exact h_deriv_final

-- =========================================================================
-- PART 3: The Discrete Dynamical Update (Motion)
-- =========================================================================

def step_motion (γ : ℝ) (K K' : ℝ → ℝ) (dt x : ℝ) : ℝ :=
  x + dt * generalized_coordinate_force γ K K' x

def trajectory (γ : ℝ) (K K' : ℝ → ℝ) (dt : ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => step_motion γ K K' dt (trajectory γ K K' dt x0 n)

theorem trajectory_zero (γ : ℝ) (K K' : ℝ → ℝ) (dt : ℝ) (n : ℕ) :
    trajectory γ K K' dt 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold trajectory
    rw [ih]
    unfold step_motion
    rw [generalized_coordinate_force_zero, mul_zero, add_zero]

-- =========================================================================
-- PART 4: Defining the Generalized "Actor"
-- =========================================================================

structure Actor (γ : ℝ) (K K' : ℝ → ℝ) (dt : ℝ) where
  x0 : ℝ
  pos : ℕ → ℝ
  is_trajectory : ∀ n, pos (n + 1) = step_motion γ K K' dt (pos n)
  self_corrects : ∀ ε > 0, ∃ N, ∀ n ≥ N, |pos n| < ε

def origin_actor (γ : ℝ) (K K' : ℝ → ℝ) (dt : ℝ) (hγ : 0 < γ) (hdt : 0 < dt) : Actor γ K K' dt where
  x0 := 0
  pos := trajectory γ K K' dt 0
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

#print axioms generalized_coordinate_force_attractive
#print axioms trajectory_zero
#print axioms generalized_discrete_potential_difference
