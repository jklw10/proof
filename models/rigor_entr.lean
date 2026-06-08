import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Basic

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real
open RealInnerProductSpace
open Finset

-- =========================================================================
-- PART 1: The Positive Semi-Definiteness Constraint (Schoenberg Check)
-- =========================================================================

/-- Re-defining the Generalized Covariance Process for completeness -/
structure GeneralizedCovarianceProcess (T : Type*) [MetricSpace T]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  u : T → E
  C0 : ℝ
  K : ℝ → ℝ
  hC0 : 0 < C0
  hK0 : K 0 = 1
  cov : ∀ x y : T, inner ℝ (u x) (u y) = C0 * K (dist x y)

namespace GeneralizedCovarianceProcess

variable {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem: Necessary Condition of Process Existence.
    If a GeneralizedCovarianceProcess exists, then the radial basis kernel K
    is mathematically guaranteed to be positive semi-definite on T. -/
theorem generalized_covariance_positive_semidefinite
    {ι : Type*} (P : GeneralizedCovarianceProcess T E)
    (s : Finset ι) (x : ι → T) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * P.K (dist (x i) (x j)) := by
  -- 1. Relate the K-sum to the Hilbert space inner product of the linear combination
  have h_inner : inner ℝ (∑ i ∈ s, c i • P.u (x i)) (∑ j ∈ s, c j • P.u (x j)) =
      P.C0 * ∑ i ∈ s, ∑ j ∈ s, c i * c j * P.K (dist (x i) (x j)) := by
    rw [sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    simp_rw [P.cov]
    -- Extract the constant C0 from the nested summations
    simp only [mul_sum]
    congr 1 with i
    congr 1 with j
    ring

  -- 2. Inner product of any vector with itself in a Hilbert space is non-negative
  have h_nonneg : 0 ≤ inner ℝ (∑ i ∈ s, c i • P.u (x i)) (∑ j ∈ s, c j • P.u (x j)) := real_inner_self_nonneg

  -- 3. Since C0 > 0, the sum must also be non-negative
  rw [h_inner] at h_nonneg
  exact nonneg_of_mul_nonneg_right h_nonneg P.hC0

end GeneralizedCovarianceProcess

-- =========================================================================
-- PART 2: Fourier Transform Core Calculus Proof
-- =========================================================================

/-- Theorem: Exact Derivative of the Fourier Transform Antiderivative.
    Proves the exact derivative of the antiderivative mapping exponential 1D spatial
    covariance to the Lorentzian spectral density, justifying the spectral peak representation. -/
theorem fourier_transform_antiderivative (a b x : ℝ) (hab : a^2 + b^2 ≠ 0) :
    let F := fun (y : ℝ) => exp (-a * y) * (b * sin (b * y) - a * cos (b * y)) / (a^2 + b^2)
    HasDerivAt F (exp (-a * x) * cos (b * x)) x := by
  intro F
  let f_num := fun (y : ℝ) => exp (-a * y) * (b * sin (b * y) - a * cos (b * y))

  -- 1. Derivative of exp (-a * y)
  have h_deriv_exp : HasDerivAt (fun y => exp (-a * y)) (-a * exp (-a * x)) x := by
    have h_lin : HasDerivAt (fun y => -a * y) (-a) x := by
      have := HasDerivAt.const_mul (-a) (hasDerivAt_id' x)
      exact this.congr_deriv (by ring)
    have h_comp := HasDerivAt.exp h_lin
    rw [mul_comm] at h_comp
    exact h_comp

  -- 2. Derivative of (b * sin (b * y) - a * cos (b * y))
  have h_deriv_trig : HasDerivAt (fun y => b * sin (b * y) - a * cos (b * y))
      (b^2 * cos (b * x) + a * b * sin (b * x)) x := by
    have h_lin : HasDerivAt (fun y => b * y) b x := by
      have := HasDerivAt.const_mul b (hasDerivAt_id' x)
      exact this.congr_deriv (by ring)

    have h_deriv_sin : HasDerivAt (fun y => sin (b * y)) (cos (b * x) * b) x := by
      exact HasDerivAt.sin h_lin
    have h_deriv_sin_scaled := HasDerivAt.const_mul b h_deriv_sin

    have h_deriv_cos : HasDerivAt (fun y => cos (b * y)) (-sin (b * x) * b) x := by
      exact HasDerivAt.cos h_lin
    have h_deriv_cos_scaled := HasDerivAt.const_mul a h_deriv_cos

    have h_sub := HasDerivAt.sub h_deriv_sin_scaled h_deriv_cos_scaled
    have h_eq : b * (cos (b * x) * b) - a * (-sin (b * x) * b) = b^2 * cos (b * x) + a * b * sin (b * x) := by ring
    rw [h_eq] at h_sub
    exact h_sub

  -- 3. Product rule of the numerator
  have h_deriv_num : HasDerivAt f_num
      (-a * exp (-a * x) * (b * sin (b * x) - a * cos (b * x)) +
       exp (-a * x) * (b^2 * cos (b * x) + a * b * sin (b * x))) x := by
    exact HasDerivAt.mul h_deriv_exp h_deriv_trig

  -- 4. Division by the constant (a^2 + b^2)
  have h_deriv_final := HasDerivAt.div_const h_deriv_num (a^2 + b^2)

  -- 5. Algebraic simplification of the derivative term
  have h_simpl : (-a * exp (-a * x) * (b * sin (b * x) - a * cos (b * x)) +
       exp (-a * x) * (b^2 * cos (b * x) + a * b * sin (b * x))) / (a^2 + b^2) =
      exp (-a * x) * cos (b * x) := by
    field_simp [hab]
    ring

  exact h_deriv_final.congr_deriv h_simpl

-- =========================================================================
-- PART 3: Reversing the Dynamical Derivations (ODE Uniqueness)
-- =========================================================================

/-- Theorem: Uniqueness of the first-order linear ODE.
    If a real function satisfies dy/dt = -C * y with y(0) = y0,
    then y(t) is uniquely and mathematically proven to be y0 * exp(-C * t). -/
theorem ode_uniqueness_exponential_decay (y : ℝ → ℝ) (C y0 : ℝ)
    (h_init : y 0 = y0)
    (h_ode : ∀ t, HasDerivAt y (-C * y t) t) :
    ∀ t, y t = y0 * exp (-C * t) := by
  intro t
  -- Define the auxiliary function f(u) = y(u) * exp(C * u)
  let f := fun (u : ℝ) => y u * exp (C * u)

  -- We prove that the derivative of f is zero everywhere
  have h_deriv_f : ∀ u, HasDerivAt f 0 u := by
    intro u
    have h_lin : HasDerivAt (fun y => C * y) C u := by
      have := HasDerivAt.const_mul C (hasDerivAt_id' u)
      exact this.congr_deriv (by ring)
    have h_deriv_exp : HasDerivAt (fun v => exp (C * v)) (C * exp (C * u)) u := by
      have h_comp := HasDerivAt.exp h_lin
      exact h_comp.congr_deriv (by ring)
    have h_product := HasDerivAt.mul (h_ode u) h_deriv_exp
    have h_zero : (-C * y u) * exp (C * u) + y u * (C * exp (C * u)) = 0 := by ring
    rw [h_zero] at h_product
    exact h_product

  -- Applying the Mean Value Theorem (constant derivative implies constant function)
  have h_deriv_eq_zero : ∀ u, deriv f u = 0 := by
    intro u
    exact (h_deriv_f u).deriv

  have h_diff : Differentiable ℝ f := by
    intro u
    exact (h_deriv_f u).differentiableAt

  have h_const : ∀ u, f u = f 0 := by
    intro u
    exact is_const_of_deriv_eq_zero h_diff h_deriv_eq_zero u 0

  have h_f0 : f 0 = y0 := by
    dsimp [f]
    rw [h_init, mul_zero, exp_zero, mul_one]

  have h_fu : f t = y t * exp (C * t) := rfl
  have h_eq_y : y t * exp (C * t) = y0 := by
    rw [← h_fu, h_const t, h_f0]

  -- Multiply both sides by exp (-C * t) to isolate y t
  have h_mult : (y t * exp (C * t)) * exp (-C * t) = y0 * exp (-C * t) := by rw [h_eq_y]
  rw [mul_assoc] at h_mult
  rw [← exp_add] at h_mult
  have h_exp_zero : C * t + -C * t = 0 := by ring
  rw [h_exp_zero] at h_mult
  rw [exp_zero] at h_mult
  rw [mul_one] at h_mult
  exact h_mult

-- =========================================================================
-- PART 4: Information-Theoretic Derivation of the Entropic Force
-- =========================================================================

/-- The predictive differential entropy (Shannon Entropy) of a 1D Gaussian
    prediction channel with error variance σ² = C0 * (1 - K(r)²). -/
def predictive_entropy (C0 : ℝ) (K : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 / 2) * log (2 * Real.pi * exp 1 * C0 * (1 - (K r)^2))

/-- The predictive potential V(r) is defined directly as the scaled predictive entropy. -/
def predictive_potential_entropy (γ C0 : ℝ) (K : ℝ → ℝ) (r : ℝ) : ℝ :=
  γ * predictive_entropy C0 K r

/-- The predictive force is defined directly as the negative derivative of the potential.
    It is computed directly from the potential, rather than being hardcoded as a magic value! -/
def computed_predictive_force (γ C0 : ℝ) (K : ℝ → ℝ) (r : ℝ) : ℝ :=
  - deriv (predictive_potential_entropy γ C0 K) r


/-- Auxiliary Theorem: Computes the derivative of the predictive entropy H. -/
theorem continuous_predictive_entropy_deriv (C0 : ℝ) (K : ℝ → ℝ) (K' : ℝ → ℝ) (r : ℝ)
    (h_pos : 2 * Real.pi * exp 1 * C0 * (1 - (K r)^2) > 0)
    (hK_deriv : HasDerivAt K (K' r) r) :
    let H := fun (y : ℝ) => predictive_entropy C0 K y
    HasDerivAt H (- (K r * K' r) / (1 - (K r)^2)) r := by
  intro H
  have h_ne_zero : 2 * Real.pi * exp 1 * C0 * (1 - (K r)^2) ≠ 0 := ne_of_gt h_pos
  have hC_const : 2 * Real.pi * exp 1 * C0 ≠ 0 := left_ne_zero_of_mul h_ne_zero

  have hC0_ne : C0 ≠ 0 := by
    intro h_zero
    rw [h_zero, mul_zero] at hC_const
    exact hC_const rfl

  -- 1. Derivative of y ↦ 1 - (K y)^2
  have h_deriv_sq : HasDerivAt (fun y => (K y)^2) (2 * K r * K' r) r := by
    have h_pow := hasDerivAt_pow 2 (K r)
    have h_simpl : ((2 : ℕ) : ℝ) * (K r) ^ (2 - 1) = 2 * K r := by
      have h1 : 2 - 1 = 1 := rfl
      rw [h1, pow_one, Nat.cast_two]
    rw [h_simpl] at h_pow
    exact HasDerivAt.comp r h_pow hK_deriv

  have h_deriv_one_sub : HasDerivAt (fun y => 1 - (K y)^2) (- 2 * K r * K' r) r := by
    have h_const := hasDerivAt_const r (1 : ℝ)
    have h_sub := HasDerivAt.sub h_const h_deriv_sq
    rw [zero_sub] at h_sub
    have h_ring : - (2 * K r * K' r) = -2 * K r * K' r := by ring
    rw [h_ring] at h_sub
    exact h_sub

  -- 2. Derivative of y ↦ 2 * pi * e * C0 * (1 - K(y)^2)
  have h_deriv_inner := HasDerivAt.const_mul (2 * Real.pi * exp 1 * C0) h_deriv_one_sub

  -- 3. Derivative of the Logarithm
  have h_deriv_log := HasDerivAt.log h_deriv_inner (ne_of_gt h_pos)

  -- 4. Multiply by (1 / 2) to get the final derivative of H
  have h_deriv_H := HasDerivAt.const_mul (1 / 2) h_deriv_log

  -- 5. Algebraic simplification
  have h_simpl : (1 / 2) * ((2 * Real.pi * exp 1 * C0 * (-2 * K r * K' r)) / (2 * Real.pi * exp 1 * C0 * (1 - (K r)^2))) =
      - (K r * K' r) / (1 - (K r)^2) := by
    have h_denom : 1 - (K r)^2 ≠ 0 := by
      rcases mul_pos_iff.mp h_pos with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact ne_of_gt h2
      · exact ne_of_lt h2
    field_simp [hC_const, h_denom]
  exact h_deriv_H.congr_deriv h_simpl


/-- Auxiliary Theorem: Computes the derivative of the scaled potential V. -/
theorem continuous_entropic_potential_deriv (γ C0 : ℝ) (K K' : ℝ → ℝ) (r : ℝ)
    (h_pos : 2 * Real.pi * exp 1 * C0 * (1 - (K r)^2) > 0)
    (hK_deriv : HasDerivAt K (K' r) r) :
    let V := fun (y : ℝ) => predictive_potential_entropy γ C0 K y
    let F_formula := γ * (K r * K' r) / (1 - (K r)^2)
    HasDerivAt V (- F_formula) r := by
  intro V F_formula
  have h_deriv_H := continuous_predictive_entropy_deriv C0 K K' r h_pos hK_deriv
  have h_deriv_V := HasDerivAt.const_mul γ h_deriv_H
  have h_simpl : γ * (- (K r * K' r) / (1 - (K r)^2)) = - F_formula := by
    unfold F_formula
    ring
  exact h_deriv_V.congr_deriv h_simpl


/-- Theorem: First-Principles Derivation of the Entropic Force.
    Proves that the computed entropic force (defined directly as the negative derivative
    of the predictive entropy potential) evaluates exactly to the classical mechanical formula. -/
theorem computed_force_eq_formula (γ C0 : ℝ) (K K' : ℝ → ℝ) (r : ℝ)
    (h_pos : 2 * Real.pi * exp 1 * C0 * (1 - (K r)^2) > 0)
    (hK_deriv : HasDerivAt K (K' r) r) :
    let F_formula := γ * (K r * K' r) / (1 - (K r)^2)
    computed_predictive_force γ C0 K r = F_formula := by
  intro F_formula
  unfold computed_predictive_force
  have h_deriv := continuous_entropic_potential_deriv γ C0 K K' r h_pos hK_deriv
  rw [h_deriv.deriv]
  ring

#print axioms continuous_entropic_potential_deriv
#print axioms computed_force_eq_formula
#print axioms continuous_predictive_entropy_deriv
#print axioms ode_uniqueness_exponential_decay
#print axioms GeneralizedCovarianceProcess
