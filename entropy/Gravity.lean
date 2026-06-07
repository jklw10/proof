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

/-- The generalized mutual entropic force exerted on particle 1 at x1
    by particle 2 at x2 under any arbitrary covariance kernel K. -/
def generalized_mutual_force (γ : ℝ) (K : ℝ → ℝ) (K' : ℝ → ℝ) (x1 x2 : ℝ) : ℝ :=
  let r := x1 - x2
  if r = 0 then 0
  else if r > 0 then generalized_entropic_force γ (K r) (K' r)
  else - generalized_entropic_force γ (K (-r)) (K' (-r))

/-- Theorem: Newton's Third Law of Generalized Entropic Gravity.
    The generalized mutual force is symmetric but opposite in sign. -/
theorem generalized_mutual_force_symmetric (γ : ℝ) (K : ℝ → ℝ) (K' : ℝ → ℝ) (x1 x2 : ℝ) :
    generalized_mutual_force γ K K' x1 x2 = - generalized_mutual_force γ K K' x2 x1 := by
  unfold generalized_mutual_force
  by_cases h : x1 - x2 = 0
  · have h_rev : x2 - x1 = 0 := by linarith
    rw [if_pos h, if_pos h_rev, neg_zero]
  · have h_ne : x1 - x2 ≠ 0 := h
    rcases lt_or_gt_of_ne h_ne with hlt | hgt
    · have h_gt2 : x2 - x1 > 0 := by linarith
      have h_not_gt : ¬ x1 - x2 > 0 := by linarith
      have h_rev_ne : x2 - x1 ≠ 0 := ne_of_gt h_gt2
      rw [if_neg h_ne, if_neg h_not_gt, if_neg h_rev_ne, if_pos h_gt2]
      have h_eq : -(x1 - x2) = x2 - x1 := by ring
      rw [h_eq]
    · have h_lt2 : x2 - x1 < 0 := by linarith
      have h_not_gt2 : ¬ x2 - x1 > 0 := by linarith
      have h_rev_ne : x2 - x1 ≠ 0 := ne_of_lt h_lt2
      rw [if_neg h_ne, if_pos hgt, if_neg h_rev_ne, if_neg h_not_gt2]
      have h_eq : -(x2 - x1) = x1 - x2 := by ring
      rw [h_eq, neg_neg]

-- =========================================================================
-- PART 2: The Conservative Potential Field (Gradient Law)
-- =========================================================================

/-- Theorem: Conservative Field of Generalized Entropic Gravity.
    The generalized mutual force field is the exact negative gradient
    of the generalized entropic potential energy for all separations. -/
theorem generalized_mutual_potential_gradient {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : GeneralizedCovarianceProcess T E) (γ : ℝ) (hγ : 0 < γ)
    (K' : ℝ → ℝ) (x1 x2 : ℝ) (h_sep : x2 < x1)
    (hK_deriv : HasDerivAt P.K (K' (x1 - x2)) (x1 - x2))
    (h_bounds : (P.K (x1 - x2)) ^ 2 < 1) :
    let U := fun (y : ℝ) => (γ / 2) * log (P.C0 * (1 - (P.K |y - x2|)^2))
    HasDerivAt U (- generalized_mutual_force γ P.K K' x1 x2) x1 := by
  intro U
  have h_sep_pos : 0 < x1 - x2 := sub_pos.mpr h_sep
  have h_nhds : Ioi x2 ∈ nhds x1 := IsOpen.mem_nhds isOpen_Ioi h_sep
  have h_local : ∀ᶠ y in nhds x1, U y = (γ / 2) * log (P.C0 * (1 - (P.K (y - x2))^2)) := by
    filter_upwards [h_nhds]
    intro y hy
    dsimp [U]
    have h_abs : |y - x2| = y - x2 := abs_of_pos (sub_pos.mpr hy)
    rw [h_abs]

  let V := fun (u : ℝ) => (γ / 2) * log (P.C0 * (1 - (P.K u)^2))

  have h_deriv_V : HasDerivAt V (- generalized_coordinate_force γ P.K K' (x1 - x2)) (x1 - x2) := by
    apply generalized_potential_deriv P γ hγ (x1 - x2) h_sep_pos K' hK_deriv h_bounds

  have h_deriv_g : HasDerivAt (fun y => y - x2) 1 x1 := by
    have h_id : HasDerivAt (fun y => y) 1 x1 := hasDerivAt_id x1
    have h_const : HasDerivAt (fun _ => x2) 0 x1 := hasDerivAt_const x1 x2
    have h_sub := HasDerivAt.sub h_id h_const
    rw [sub_zero] at h_sub
    exact h_sub

  have h_deriv_comp : HasDerivAt (V ∘ (fun y => y - x2)) (- generalized_coordinate_force γ P.K K' (x1 - x2) * 1) x1 := by
    exact HasDerivAt.comp x1 h_deriv_V h_deriv_g
  rw [mul_one] at h_deriv_comp

  have h_final : HasDerivAt U (- generalized_mutual_force γ P.K K' x1 x2) x1 := by
    have h_force_eq : generalized_mutual_force γ P.K K' x1 x2 = generalized_coordinate_force γ P.K K' (x1 - x2) := by
      unfold generalized_mutual_force generalized_coordinate_force
      rfl
    rw [h_force_eq]
    apply HasDerivAt.congr_of_eventuallyEq h_deriv_comp
    filter_upwards [h_local]
    intro y hy
    exact hy
  exact h_final

#print axioms generalized_mutual_potential_gradient
#print axioms generalized_mutual_force_symmetric
