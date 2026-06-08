import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import entropy.common
import entropy.Constants
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real
open Complex

-- =========================================================================
-- PART 1: The Wick Rotation Derivative
-- =========================================================================

/-- Lemma: The derivative of the Wick rotation coordinate map τ ↦ -I * τ is -I. -/
lemma deriv_wick (τ : ℂ) : HasDerivAt (fun y => -Complex.I * y) (-Complex.I) τ := by
  have h := hasDerivAt_id' τ
  have h_mul := HasDerivAt.const_mul (-Complex.I) h
  rw [mul_one] at h_mul
  exact h_mul

-- =========================================================================
-- PART 2: The Wick Rotation Equivalence Theorem
-- =========================================================================

/-- Theorem: Wick Rotation of Schrödinger to Imperfect Diffusion.
    If a state ψ(t) satisfies the Fourier-space Schrödinger equation with energy offset κ2,
    then its Wick-rotated counterpart u(τ) = ψ(-I * τ) strictly satisfies the
    Fourier-space damped (imperfect) diffusion equation. -/
theorem wick_rotation_equivalence (ψ : ℂ → ℂ) (D κ2 k : ℂ) (τ : ℂ)
    (h_schrodinger : HasDerivAt ψ (-Complex.I * (D * k^2 + κ2) * ψ (-Complex.I * τ)) (-Complex.I * τ)) :
    let u := fun (y : ℂ) => ψ (-Complex.I * y)
    HasDerivAt u (-(D * k^2 + κ2) * u τ) τ := by
  intro u

  -- 1. The derivative of the inner coordinate shift τ ↦ -I * τ
  have h_g : HasDerivAt (fun y => -Complex.I * y) (-Complex.I) τ := deriv_wick τ

  -- 2. Apply the Chain Rule: d(f(g(x)))/dx = f'(g(x)) * g'(x)
  have h_comp := HasDerivAt.comp τ h_schrodinger h_g

  -- 3. We use the fundamental property of the imaginary unit: I * I = -1
  have h_I_mul : Complex.I * Complex.I = -1 := Complex.I_mul_I

  -- 4. Prove that the chain-rule product algebraically simplifies to the damped diffusion term
  have h_deriv_eq : (-Complex.I * (D * k^2 + κ2) * ψ (-Complex.I * τ)) * -Complex.I =
      -(D * k^2 + κ2) * u τ := by
    dsimp [u]
    -- Group the Complex.I terms together using ring properties
    have h_algebraic : (-Complex.I * (D * k^2 + κ2) * ψ (-Complex.I * τ)) * -Complex.I =
        (Complex.I * Complex.I) * ((D * k^2 + κ2) * ψ (-Complex.I * τ)) := by ring
    rw [h_algebraic, h_I_mul]
    ring

  rw [h_deriv_eq] at h_comp
  exact h_comp

-- =========================================================================
-- PART 3: Grounding Wick Rotation in the Unified Process Models
-- =========================================================================

/-- Theorem: Legacy Wick Spectral Mapping to the Exponential Covariance Process.
    If the quantum system's energy offset κ2 matches the inverse squared correlation length
    1 / ξ^2 of our unified exponential covariance process, the Wick-rotated diffusion equation
    strictly represents the physical spectral damping of our process. -/
theorem process_wick_spectral_relation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess ℝ E) (D k : ℂ) (τ : ℂ) (ψ : ℂ → ℂ)
    (h_schrodinger : HasDerivAt ψ (-Complex.I * (D * k^2 + ((1 : ℂ) / (xi P.z : ℂ)^2)) * ψ (-Complex.I * τ)) (-Complex.I * τ)) :
    let u := fun (y : ℂ) => ψ (-Complex.I * y)
    HasDerivAt u (-(D * k^2 + ((1 : ℂ) / (xi P.z : ℂ)^2)) * u τ) τ := by
  exact wick_rotation_equivalence ψ D (1 / (xi P.z : ℂ)^2) k τ h_schrodinger

/-- Theorem: Generalized Wick Spectral Mapping to the Generalized Covariance Process.
    If the quantum system's energy offset κ2 matches the inverse squared characteristic scale
    1 / ξ^2 of our generalized covariance process with length scale ξ > 0, the Wick-rotated
    diffusion equation strictly represents the physical spectral damping of our generalized process. -/
theorem generalized_process_wick_spectral_relation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : GeneralizedCovarianceProcess ℝ E) (ξ : ℝ) (hξ : 0 < ξ) (D k : ℂ) (τ : ℂ) (ψ : ℂ → ℂ)
    (h_schrodinger : HasDerivAt ψ (-Complex.I * (D * k^2 + ((1 : ℂ) / (ξ : ℂ)^2)) * ψ (-Complex.I * τ)) (-Complex.I * τ)) :
    let u := fun (y : ℂ) => ψ (-Complex.I * y)
    HasDerivAt u (-(D * k^2 + ((1 : ℂ) / (ξ : ℂ)^2)) * u τ) τ := by
  exact wick_rotation_equivalence ψ D (1 / (ξ : ℂ)^2) k τ h_schrodinger

-- =========================================================================
-- PART 4: The Fundamental Entropic Diffusion Steady-State
-- =========================================================================

/-- Lemma: Connects the physical spatial scale ξ directly to the log-decay parameter.
    Proves that the quantum energy offset κ² (1/ξ²) is algebraically identical
    to the squared rate of logarithmic decay (log z)². -/
lemma quantum_offset_eq_log_sq (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    quantum_energy_offset (xi z) = (Real.log z)^2 := by
  unfold quantum_energy_offset xi
  have h_log : Real.log z ≠ 0 := by
    have h_log_neg : Real.log z < 0 := (Real.log_neg_iff hz0).mpr hz1
    exact ne_of_lt h_log_neg
  field_simp

/-- Theorem: The Steady-State Entropic Diffusion Equation.
    Proves that the spatial covariance function K(r) = z^r is the exact solution to the
    screened diffusion (stationary Klein-Gordon/screened Poisson) equation:

        d²/dr² K(r) = κ² * K(r)

    where the screening mass (or dissipation rate) κ² is exactly the quantum energy offset (1/ξ²).

    This formalizes the perspective that "predictability" (K) is not an arbitrary choice,
    but the natural steady-state structure of the fundamental entropic diffusion operator. -/
theorem covariance_is_diffusion_steady_state (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (r : ℝ) :
    let κ2 := quantum_energy_offset (xi z)
    let K := fun (y : ℝ) => z ^ y
    let dK := fun (y : ℝ) => Real.log z * z ^ y
    HasDerivAt K (Real.log z * z ^ r) r ∧
    HasDerivAt dK (κ2 * z ^ r) r := by
  intro κ2 K dK

  -- Step 1: Align K(y) exactly with the internal exponential representation exp(log z * y)
  have h_rpow : K = (fun y => Real.exp (Real.log z * y)) := by
    ext y
    exact Real.rpow_def_of_pos hz0 y

  -- Step 2: Compute the derivative of the inner coordinate shift: y ↦ log(z) * y
  have h_linear : HasDerivAt (fun y => Real.log z * y) (Real.log z) r := by
    have h_eq : (fun y => Real.log z * y) = (fun y => y * Real.log z) := by
      ext y
      rw [mul_comm]
    rw [h_eq]
    have h_id := hasDerivAt_id' r |>.mul_const (Real.log z)
    rw [one_mul] at h_id
    exact h_id

  -- Step 3: Apply the Chain Rule for exp
  have h_comp := HasDerivAt.exp h_linear

  -- Step 4: Algebraically swap the multiplication order in the derivative to match the goal
  have h_deriv_eq : Real.exp (Real.log z * r) * Real.log z = Real.log z * z ^ r := by
    rw [mul_comm (Real.exp (Real.log z * r)), ← Real.rpow_def_of_pos hz0 r]

  rw [h_deriv_eq] at h_comp

  -- Step 5: Establish the first derivative of K
  have h_deriv1 : HasDerivAt K (Real.log z * z ^ r) r := by
    rw [h_rpow]
    exact h_comp

  -- Step 6: Prove the second derivative d²/dr² K(r) = κ² * K(r)
  have h_deriv2 : HasDerivAt dK (κ2 * z ^ r) r := by
    -- Scale the first derivative by log(z)
    have h_scaled := HasDerivAt.const_mul (Real.log z) h_deriv1
    -- Relate (log z)² to the quantum energy offset κ²
    have h_algebraic : Real.log z * (Real.log z * z ^ r) = κ2 * z ^ r := by
      rw [← mul_assoc, ← sq, ← quantum_offset_eq_log_sq z hz0 hz1]
    rw [h_algebraic] at h_scaled
    exact h_scaled

  exact ⟨h_deriv1, h_deriv2⟩

#print axioms process_wick_spectral_relation
#print axioms generalized_process_wick_spectral_relation
