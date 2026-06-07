import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import entropy.common

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
-- PART 3: Grounding Wick Rotation in the Unified Process Model
-- =========================================================================

/-- Theorem: Wick Spectral Mapping to the Unified Process Model.
    If the quantum system's energy offset κ2 matches the inverse squared correlation length
    1 / ξ^2 of our unified covariance process, the Wick-rotated diffusion equation strictly
    represents the physical spectral damping of our process. -/
theorem process_wick_spectral_relation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess ℝ E) (D k : ℂ) (τ : ℂ) (ψ : ℂ → ℂ)
    (h_schrodinger : HasDerivAt ψ (-Complex.I * (D * k^2 + ((1 : ℂ) / (xi P.z : ℂ)^2)) * ψ (-Complex.I * τ)) (-Complex.I * τ)) :
    let u := fun (y : ℂ) => ψ (-Complex.I * y)
    HasDerivAt u (-(D * k^2 + ((1 : ℂ) / (xi P.z : ℂ)^2)) * u τ) τ := by
  exact wick_rotation_equivalence ψ D (1 / (xi P.z : ℂ)^2) k τ h_schrodinger
