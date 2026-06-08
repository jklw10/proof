import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Disjoint
import Mathlib.Order.Interval.Set.Basic

set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
noncomputable section
open Finset
open Real
open Filter
open Topology
open MeasureTheory
open Set
open Asymptotics

-- =========================================================================
-- PART 1: The Algebraic Decomposition Lemma (Proven)
-- =========================================================================

lemma discrete_entropy_algebraic_decomposition {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℝ) (Δx : ℝ) (h_pos_f : ∀ i ∈ s, 0 < f i) (h_pos_Δx : 0 < Δx) :
    let P := fun i => f i * Δx
    let H_discrete := - ∑ i ∈ s, P i * log (P i)
    H_discrete + log Δx = - (∑ i ∈ s, f i * log (f i) * Δx) + (1 - ∑ i ∈ s, f i * Δx) * log Δx := by
  intro P H_discrete
  have h_log_mul : ∀ i ∈ s, log (P i) = log (f i) + log Δx := by
    intro i hi
    dsimp [P]
    exact log_mul (ne_of_gt (h_pos_f i hi)) (ne_of_gt h_pos_Δx)
  have h_term : ∀ i ∈ s, P i * log (P i) = f i * log (f i) * Δx + (f i * Δx) * log Δx := by
    intro i hi
    dsimp [P]
    rw [h_log_mul i hi]
    ring
  have h_sum_split : ∑ i ∈ s, P i * log (P i) = ∑ i ∈ s, (f i * log (f i) * Δx + (f i * Δx) * log Δx) := by
    apply sum_congr rfl
    exact h_term
  dsimp [H_discrete]
  rw [h_sum_split, sum_add_distrib, ← sum_mul, ← sum_mul]
  ring


-- =========================================================================
-- PART 2: Analytical Limit Skeletons and Bounds (Proven)
-- =========================================================================

lemma polynomial_times_log_limit (β : ℝ) (hβ : 0 < β) :
  Tendsto (fun (N : ℕ) =>
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    (N : ℝ) ^ (-β) * log Δx)
  atTop
  (nhds 0) := by
  have h_eq : (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      (N : ℝ) ^ (-β) * log Δx) =ᶠ[atTop]
    (fun (N : ℕ) => log 2 * (N : ℝ) ^ (-β) - (1 / 2) * (log (N : ℝ) * (N : ℝ) ^ (-β))) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro N hN
    have hN_pos : 0 < (N : ℝ) := by positivity
    have h_sqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    have h_div : 0 < Real.sqrt (N : ℝ) / 2 := by linarith
    dsimp only
    rw [log_div one_ne_zero (ne_of_gt h_div)]
    rw [log_one, zero_sub]
    rw [log_div (ne_of_gt h_sqrt) (by norm_num)]
    rw [log_sqrt (le_of_lt hN_pos)]
    ring

  rw [Filter.tendsto_congr' h_eq]

  have h_lim_pow : Tendsto (fun (N : ℕ) => (N : ℝ) ^ (-β)) atTop (nhds 0) := by
    have h_lim := tendsto_rpow_neg_atTop hβ
    exact h_lim.comp tendsto_natCast_atTop_atTop

  have h_lim_log_pow : Tendsto (fun (N : ℕ) => log (N : ℝ) * (N : ℝ) ^ (-β)) atTop (nhds 0) := by
    have hβ2 : 0 < β / 2 := half_pos hβ
    have h_o : (fun x : ℝ => log x) =o[atTop] (fun x : ℝ => x ^ (β / 2)) :=
      isLittleO_log_rpow_atTop hβ2
    have h_o_mul := h_o.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ (-β)) atTop)
    have h_eq2 : (fun x : ℝ => x ^ (β / 2) * x ^ (-β)) =ᶠ[atTop] (fun x : ℝ => x ^ (- (β / 2))) := by
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      use 1
      intro x hx
      have hx_pos : 0 < x := by linarith
      rw [← rpow_add hx_pos]
      congr 1
      ring
    have h_o_simped := h_o_mul.congr' (Filter.EventuallyEq.refl _ _) h_eq2
    have h_lim_neg : Tendsto (fun x : ℝ => x ^ (- (β / 2))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hβ2
    have h_lim_real : Tendsto (fun x : ℝ => log x * x ^ (-β)) atTop (nhds 0) :=
      h_o_simped.trans_tendsto h_lim_neg
    exact h_lim_real.comp tendsto_natCast_atTop_atTop

  have h_lim_pow_scaled := Tendsto.const_mul (log 2) h_lim_pow
  have h_lim_log_pow_scaled := Tendsto.const_mul (1 / 2) h_lim_log_pow
  have h_sub := Tendsto.sub h_lim_pow_scaled h_lim_log_pow_scaled
  rw [mul_zero, mul_zero, sub_zero] at h_sub
  exact h_sub


-- =========================================================================
-- PART 3: The Analytical Sub-Lemmas
-- =========================================================================

/-- Lemma 2.1a: The left tail of the continuous integral decays at a polynomial rate. -/
axiom left_tail_integral_decay (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
  ∃ (C_tail : ℝ) (β : ℝ), 0 ≤ C_tail ∧ 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let b := (N : ℝ) * Δx
    (∫ x in Set.Iic (-b), f x) ≤ C_tail * (N : ℝ) ^ (-β)

/-- Lemma 2.1b: The right tail of the continuous integral decays at a polynomial rate. -/
axiom tail_integral_decay (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
  ∃ (C_tail : ℝ) (β : ℝ), 0 ≤ C_tail ∧ 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let b := (N : ℝ) * Δx
    (∫ x in Set.Ici b, f x) ≤ C_tail * (N : ℝ) ^ (-β)

/-- Lemma 2.2: The discretization error of the core Riemann sum is O(N^{-1/2}).
  The total variation of f on any bounded interval is bounded by the integral of |f'|.
  Therefore, the core sum error scales with Δx = 2/√N.
-/
axiom riemann_sum_core_error (f : ℝ → ℝ)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  ∃ (C_riemann : ℝ), 0 ≤ C_riemann ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let s' := Finset.Ico (- (N : ℤ)) (N : ℤ)
    |(∫ x in Set.Icc (- ((N : ℝ) * Δx)) ((N : ℝ) * Δx), f x) - ∑ i ∈ s', f (i * Δx) * Δx| ≤ C_riemann * (N : ℝ) ^ (-(1/2 : ℝ))

/-- Lemma 2.3: The single endpoint boundary term f(N * Δx) * Δx converges to 0.
  Since the endpoint lies at 2√N, the density decays as O(N^{-p/2}),
  and the step size Δx = O(N^{-1/2}), yielding a combined rate of O(N^{-(p+1)/2}).
-/
lemma boundary_term_decay (f : ℝ → ℝ)
    (hf_pos : ∀ x, 0 < f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
  ∃ (C_bound : ℝ) (β : ℝ), 0 ≤ C_bound ∧ 0 < β ∧ ∀ (N : ℕ),
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    f ((N : ℝ) * Δx) * Δx ≤ C_bound * (N : ℝ) ^ (-β) := by
  rcases hf_decay with ⟨C, p, hp, hf_dec⟩
  use max 0 (C * (2 : ℝ) ^ (1 - p)), (p + 1) / 2
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · linarith
  · intro N
    dsimp only
    rcases eq_or_ne N 0 with rfl | hN
    · have h_lhs : f (0 * (1 / (Real.sqrt 0 / (2 : ℝ)))) * (1 / (Real.sqrt 0 / (2 : ℝ))) = 0 := by
        simp only [Real.sqrt_zero, zero_div, div_zero, mul_zero]
      have h_rhs : (max 0 (C * (2 : ℝ) ^ (1 - p))) * (0 : ℝ) ^ (-((p + 1) / 2)) = 0 := by
        have h_pow_zero : (0 : ℝ) ^ (-((p + 1) / 2)) = 0 := by
          apply Real.zero_rpow
          have h_exp_neg : -((p + 1) / (2 : ℝ)) < 0 := by
            apply neg_lt_zero.mpr
            apply div_pos
            · linarith
            · linarith
          exact ne_of_lt h_exp_neg
        rw [h_pow_zero, mul_zero]
      simp only [Nat.cast_zero]
      rw [h_lhs, h_rhs]
    · have hN_pos : 0 < (N : ℝ) := by positivity
      have h_sqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
      have h_div : 0 < Real.sqrt (N : ℝ) / (2 : ℝ) := by linarith
      have h_Δx : 1 / (Real.sqrt (N : ℝ) / (2 : ℝ)) = (2 : ℝ) / Real.sqrt (N : ℝ) := by ring

      have h_val : (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) = (2 : ℝ) * Real.sqrt (N : ℝ) := by
        rw [h_Δx]
        rw [← mul_div_assoc]
        rw [mul_comm (N : ℝ) (2 : ℝ)]
        rw [mul_div_assoc]
        rw [Real.div_sqrt]

      have hf_dec_apply := hf_dec ((2 : ℝ) * Real.sqrt (N : ℝ))
      rw [h_val]

      have h_denom_le : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p ≤ (1 + |(2 : ℝ) * Real.sqrt (N : ℝ)|) ^ p := by
        have h_abs : |(2 : ℝ) * Real.sqrt (N : ℝ)| = (2 : ℝ) * Real.sqrt (N : ℝ) := by
          apply abs_of_nonneg
          positivity
        rw [h_abs]
        apply Real.rpow_le_rpow
        · positivity
        · linarith
        · linarith

      have h_denom_pos : 0 < ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p := by
        apply Real.rpow_pos_of_pos; positivity
      have h_denom_pos' : 0 < (1 + |(2 : ℝ) * Real.sqrt (N : ℝ)|) ^ p := by
        apply Real.rpow_pos_of_pos; positivity

      have hC_pos : 0 < C := by
        have h_dec_0 := hf_dec 0
        have h_pos_0 := hf_pos 0
        have h_denom : (1 + |(0 : ℝ)|) ^ p = 1 := by
          simp only [abs_zero, add_zero, Real.one_rpow]
        rw [h_denom, div_one] at h_dec_0
        exact lt_of_lt_of_le h_pos_0 h_dec_0

      have h_f_bound : f ((2 : ℝ) * Real.sqrt (N : ℝ)) ≤ C / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p := by
        apply le_trans hf_dec_apply
        exact div_le_div_of_nonneg_left hC_pos.le h_denom_pos h_denom_le

      have h_prod_le : f ((2 : ℝ) * Real.sqrt (N : ℝ)) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) ≤
          (C / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p) * ((2 : ℝ) / Real.sqrt (N : ℝ)) := by
        rw [h_Δx]
        apply mul_le_mul_of_nonneg_right h_f_bound
        positivity

      have h_mul_rpow : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p = (2 : ℝ) ^ p * (Real.sqrt (N : ℝ)) ^ p := by
        apply Real.mul_rpow
        · norm_num
        · positivity

      have h_sqrt_eq : Real.sqrt (N : ℝ) = (N : ℝ) ^ (1/2 : ℝ) := by
        apply Real.sqrt_eq_rpow

      have h_rpow_mul : ((N : ℝ) ^ (1/2 : ℝ)) ^ p = (N : ℝ) ^ ((1/2 : ℝ) * p) := by
        exact (Real.rpow_mul hN_pos.le (1/2 : ℝ) p).symm

      have h_denom_eq : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p = (2 : ℝ) ^ p * (N : ℝ) ^ (p / 2) := by
        rw [h_mul_rpow, h_sqrt_eq, h_rpow_mul]
        congr 1
        congr 1
        ring

      have h_algebra : (C / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p) * ((2 : ℝ) / Real.sqrt (N : ℝ)) =
          C * (2 : ℝ) ^ (1 - p) * (N : ℝ) ^ (-((p + 1) / 2)) := by
        rw [h_denom_eq, h_sqrt_eq]
        have h_pow_neg1 : 1 / (N : ℝ) ^ (p / 2) = (N : ℝ) ^ (-(p / 2)) := by
          rw [Real.rpow_neg hN_pos.le, inv_eq_one_div]
        have h_pow_neg2 : 1 / (N : ℝ) ^ (1/2 : ℝ) = (N : ℝ) ^ (-(1/2 : ℝ)) := by
          rw [Real.rpow_neg hN_pos.le, inv_eq_one_div]
        have h1 : C / ((2 : ℝ) ^ p * (N : ℝ) ^ (p / 2)) = C * (2 : ℝ) ^ (-p) * (N : ℝ) ^ (-(p / 2)) := by
          rw [div_mul_eq_div_div]
          rw [div_eq_mul_one_div]
          rw [h_pow_neg1]
          rw [div_eq_mul_one_div]
          rw [← inv_eq_one_div]
          rw [← Real.rpow_neg (by positivity)]
        have h2 : (2 : ℝ) / (N : ℝ) ^ (1/2 : ℝ) = (2 : ℝ) * (N : ℝ) ^ (-(1/2 : ℝ)) := by
          rw [div_eq_mul_one_div, h_pow_neg2]
        rw [h1, h2]
        have h_base2 : (2 : ℝ) ^ (-p) * (2 : ℝ) = (2 : ℝ) ^ (1 - p) := by
          have : (2 : ℝ) ^ (-p) * (2 : ℝ) = (2 : ℝ) ^ (-p) * (2 : ℝ) ^ (1 : ℝ) := by
            congr 1
            exact (Real.rpow_one 2).symm
          rw [this]
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring
        have h_baseN : (N : ℝ) ^ (-(p / 2)) * (N : ℝ) ^ (-(1/2 : ℝ)) = (N : ℝ) ^ (-((p + 1) / 2)) := by
          rw [← Real.rpow_add hN_pos]
          congr 1
          ring
        rw [show C * (2 : ℝ) ^ (-p) * (N : ℝ) ^ (-(p / 2)) * ((2 : ℝ) * (N : ℝ) ^ (-(1/2 : ℝ))) =
          C * ((2 : ℝ) ^ (-p) * (2 : ℝ)) * ((N : ℝ) ^ (-(p / 2)) * (N : ℝ) ^ (-(1/2 : ℝ))) by ring]
        rw [h_base2, h_baseN]

      rw [h_algebra] at h_prod_le
      apply le_trans h_prod_le
      have : C * (2 : ℝ) ^ (1 - p) ≤ max 0 (C * (2 : ℝ) ^ (1 - p)) := le_max_right _ _
      have h_pos_pow : 0 ≤ (N : ℝ) ^ (-((p + 1) / 2)) := by positivity
      exact mul_le_mul_of_nonneg_right this h_pos_pow


-- =========================================================================
-- PART 4: Assembly of the Rate Bound (Proven)
-- =========================================================================

/-- Helper Lemma: Partition of the total continuous probability mass (1) into three domains. -/
lemma integral_partition_of_one (f : ℝ → ℝ) (hf_integrable : Integrable f) (hf_norm : ∫ x, f x = 1) (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Iic (-b), f x) + (∫ x in Ico (-b) b, f x) + (∫ x in Ici b, f x) = 1 := by

  -- Step 1: Combine [-b, b) and [b, ∞) into [-b, ∞)
  have h_union1 : Ico (-b) b ∪ Ici b = Ici (-b) := by
    exact Ico_union_Ici_eq_Ici (by linarith)

  have h_disj1 : Disjoint (Ico (-b) b) (Ici b) := by
    rw [Set.disjoint_left]
    rintro x hx_co hx_ci
    rw [Set.mem_Ico] at hx_co
    rw [Set.mem_Ici] at hx_ci
    have hx_lt_b := hx_co.2
    have hb_le_x := hx_ci
    linarith

  have h_int1 : (∫ x in Ico (-b) b, f x) + (∫ x in Ici b, f x) = ∫ x in Ici (-b), f x := by
    rw [← setIntegral_union h_disj1 measurableSet_Ici hf_integrable.restrict hf_integrable.restrict]
    rw [h_union1]

  -- Step 2: Combine (-∞, -b] and [-b, ∞) to cover the whole real line ℝ
  rw [add_assoc, h_int1]
  have h_disj2 : Disjoint (Iic (-b)) (Ioi (-b)) := by
    rw [Set.disjoint_left]
    rintro x hx_ic hx_oi
    rw [Set.mem_Iic] at hx_ic
    rw [Set.mem_Ioi] at hx_oi
    linarith

  have h_int2 : (∫ x in Iic (-b), f x) + (∫ x in Ici (-b), f x) = ∫ x in Set.univ, f x := by
    -- We can use Ioi (-b) instead of Ici (-b) because the single point {-b} has measure 0.
    have h_ae : Ici (-b) =ᵐ[volume] Ioi (-b) := (Ioi_ae_eq_Ici).symm
    have h_eq : ∫ x in Ici (-b), f x = ∫ x in Ioi (-b), f x := setIntegral_congr_set h_ae
    rw [h_eq]
    rw [← setIntegral_union h_disj2 measurableSet_Ioi hf_integrable.restrict hf_integrable.restrict]
    have h_union2 : Iic (-b) ∪ Ioi (-b) = Set.univ := by
      exact Iic_union_Ioi
    rw [h_union2]

  rw [h_int2]
  rw [setIntegral_univ]
  exact hf_norm

/-- Helper Lemma: Splits the boundary term (i = N) off from the closed interval Riemann sum. -/
lemma finset_sum_endpoint_split_nat (f : ℝ → ℝ) (N : ℕ) (Δx : ℝ) :
    ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f ((i : ℝ) * Δx) * Δx =
    (∑ i ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), f ((i : ℝ) * Δx) * Δx) + f (((N : ℤ) : ℝ) * Δx) * Δx := by
  have h_le : -(N : ℤ) ≤ (N : ℤ) := by omega
  have h_not_mem : (N : ℤ) ∉ Finset.Ico (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Ico, lt_self_iff_false, and_false, not_false_iff]
  have h_insert : Finset.Icc (-(N : ℤ)) (N : ℤ) = insert (N : ℤ) (Finset.Ico (-(N : ℤ)) (N : ℤ)) := by
    symm
    apply Finset.Ico_insert_right h_le
  rw [h_insert]
  rw [Finset.sum_insert h_not_mem]
  ring

/-- Theorem: Splitting of 1 = ∫ x, f(x) and bounds the overall error via triangle inequality. -/
theorem integral_split_and_error_decomp (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_norm : ∫ x, f x = 1) (N : ℕ) (hN : 0 < N) :
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let b := (N : ℝ) * Δx
    let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
    let s' := Finset.Ico (- (N : ℤ)) (N : ℤ)
    |1 - ∑ i ∈ s, f (i * Δx) * Δx| ≤
      (∫ x in Set.Iic (-b), f x) +
      |(∫ x in Set.Icc (-b) b, f x) - ∑ i ∈ s', f (i * Δx) * Δx| +
      (∫ x in Set.Ici b, f x) +
      f (b) * Δx := by
  intro σ Δx b s s'

  -- 1. Derive integrability from the fact that its Bochner integral is 1 (non-zero)
  have h_ne_zero : ∫ x, f x ≠ 0 := by
    rw [hf_norm]
    norm_num
  have hf_int : Integrable f := MeasureTheory.Integrable.of_integral_ne_zero h_ne_zero

  -- Compute nonnegativity of boundaries for the partition lemma
  have h_σ_pos : 0 < σ := by
    have hN_pos : 0 < (N : ℝ) := by positivity
    exact div_pos (Real.sqrt_pos.mpr hN_pos) (by linarith)
  have h_Δx_pos : 0 < Δx := div_pos (by linarith) h_σ_pos
  have hb_nonneg : 0 ≤ b := by
    have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
    exact mul_nonneg hN_nonneg h_Δx_pos.le

  -- 2. Use the partition of 1
  have h_part := integral_partition_of_one f hf_int hf_norm b hb_nonneg
  have h_sum_split := finset_sum_endpoint_split_nat f N Δx

  -- Clean up coercions in h_sum_split to match s, s', and b
  have h_cast : ((N : ℤ) : ℝ) = (N : ℝ) := by norm_cast
  rw [h_cast] at h_sum_split
  change ∑ i ∈ s, f (i * Δx) * Δx = (∑ i ∈ s', f (i * Δx) * Δx) + f b * Δx at h_sum_split

  -- 3. Substitute both partitions into the left-hand side
  rw [← h_part, h_sum_split]

  -- 4. Rearrange terms algebraically under the absolute value using Ico
  have h_algebra : (∫ x in Set.Iic (-b), f x) + (∫ x in Set.Ico (-b) b, f x) + (∫ x in Set.Ici b, f x) -
      ((∑ i ∈ s', f (i * Δx) * Δx) + f b * Δx) =
      (∫ x in Set.Iic (-b), f x) +
      (((∫ x in Set.Ico (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)) +
      (∫ x in Set.Ici b, f x) - f b * Δx) := by ring
  rw [h_algebra]

  -- 5. Define standard non-negativity of set integration
  have h_nonneg_Iic : 0 ≤ ∫ x in Set.Iic (-b), f x := by
    exact MeasureTheory.setIntegral_nonneg measurableSet_Iic (fun x _ => hf_nonneg x)

  have h_nonneg_Ici : 0 ≤ ∫ x in Set.Ici b, f x := by
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun x _ => hf_nonneg x)

  have h_nonneg_bound : 0 ≤ f b * Δx := by
    have hf_val : 0 ≤ f b := hf_nonneg b
    have h_σ_pos : 0 < σ := by
      have hN_pos : 0 < (N : ℝ) := by positivity
      exact div_pos (Real.sqrt_pos.mpr hN_pos) (by linarith)
    have h_Δx_pos : 0 < Δx := div_pos (by linarith) h_σ_pos
    exact mul_nonneg hf_val h_Δx_pos.le

  -- 6. Establish absolute value simplification equations for non-negative terms
  have h_abs_Iic : |∫ x in Set.Iic (-b), f x| = ∫ x in Set.Iic (-b), f x :=
    abs_of_nonneg h_nonneg_Iic

  have h_abs_Ici : |∫ x in Set.Ici b, f x| = ∫ x in Set.Ici b, f x :=
    abs_of_nonneg h_nonneg_Ici

  have h_abs_neg_bound : |- (f b * Δx)| = f b * Δx := by
    rw [abs_neg, abs_of_nonneg h_nonneg_bound]

  -- 7. Rewrite Set.Ico to Set.Icc everywhere before setting up triangle inequalities
  have h_Ico_ae : Ico (-b) b =ᵐ[volume] Icc (-b) b := by
    exact Ico_ae_eq_Icc
  have h_Ico_eq_Icc : ∫ x in Set.Ico (-b) b, f x = ∫ x in Set.Icc (-b) b, f x := by
    exact setIntegral_congr_set h_Ico_ae
  rw [h_Ico_eq_Icc]

  -- 8. State and rearrange the three triangle inequalities in the context
  have h_step1 := abs_add_le (∫ x in Set.Iic (-b), f x)
    (((∫ x in Set.Icc (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)) +
    (∫ x in Set.Ici b, f x) - f b * Δx)

  have h_rearrange2 : ((∫ x in Set.Icc (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)) +
      (∫ x in Set.Ici b, f x) - f b * Δx =
      ((∫ x in Set.Icc (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)) +
      ((∫ x in Set.Ici b, f x) - f b * Δx) := by ring

  have h_step2 : |((∫ x in Set.Icc (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)) +
      ((∫ x in Set.Ici b, f x) - f b * Δx)| ≤
      |(∫ x in Set.Icc (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)| +
      |(∫ x in Set.Ici b, f x) - f b * Δx| :=
    abs_add_le ((∫ x in Set.Icc (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx))
      ((∫ x in Set.Ici b, f x) - f b * Δx)
  rw [← h_rearrange2] at h_step2

  have h_rearrange3 : (∫ x in Set.Ici b, f x) - f b * Δx =
      (∫ x in Set.Ici b, f x) + (- (f b * Δx)) := by ring

  have h_step3 : |(∫ x in Set.Ici b, f x) + (- (f b * Δx))| ≤
      |(∫ x in Set.Ici b, f x)| + |- (f b * Δx)| :=
    abs_add_le (∫ x in Set.Ici b, f x) (- (f b * Δx))
  rw [← h_rearrange3] at h_step3

  -- 9. Combine the triangle inequalities linearly to close the goal
  linarith

lemma scaling_error_rate_bound (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f)
    (hf_norm : ∫ x, f x = 1)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  ∃ (C' : ℝ) (β : ℝ), 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
    |1 - ∑ i ∈ s, f (i * Δx) * Δx| ≤ C' * (N : ℝ) ^ (-β) := by
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x => le_of_lt (hf_pos x)
  rcases left_tail_integral_decay f hf_nonneg hf_decay with ⟨C_ltail, β_ltail, hC_ltail, hβ_ltail, h_ltail⟩
  rcases tail_integral_decay f hf_nonneg hf_decay with ⟨C_rtail, β_rtail, hC_rtail, hβ_rtail, h_rtail⟩
  rcases riemann_sum_core_error f hd hf_deriv_decay with ⟨C_riemann, hC_riemann, h_riemann⟩
  rcases boundary_term_decay f hf_pos hf_decay with ⟨C_bound, β_bound, hC_bound, hβ_bound, h_bound⟩

  let C_total := C_ltail + C_riemann + C_rtail + C_bound
  let β := min (1/2 : ℝ) (min β_ltail (min β_rtail β_bound))
  use C_total, β
  constructor
  · apply lt_min (by norm_num) (lt_min hβ_ltail (lt_min hβ_rtail hβ_bound))
  · intro N hN
    dsimp only
    have hN_pos : 0 < (N : ℝ) := by positivity
    have hN1 : 1 ≤ (N : ℝ) := by
      have : 1 ≤ N := hN
      exact_mod_cast this
    have h_split := integral_split_and_error_decomp f hf_nonneg hf_norm N hN
    dsimp only at h_split
    apply le_trans h_split

    have h_half : β ≤ 1/2 := min_le_left _ _
    have h_rest : β ≤ min β_ltail (min β_rtail β_bound) := min_le_right _ _
    have h_ltail_le : β ≤ β_ltail := le_trans h_rest (min_le_left _ _)
    have h_rest2 : β ≤ min β_rtail β_bound := le_trans h_rest (min_le_right _ _)
    have h_rtail_le : β ≤ β_rtail := le_trans h_rest2 (min_le_left _ _)
    have h_bound_le : β ≤ β_bound := le_trans h_rest2 (min_le_right _ _)

    have h_pow_half : (N : ℝ) ^ (-(1/2 : ℝ)) ≤ (N : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_half)
    have h_pow_ltail : (N : ℝ) ^ (-β_ltail) ≤ (N : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_ltail_le)
    have h_pow_rtail : (N : ℝ) ^ (-β_rtail) ≤ (N : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_rtail_le)
    have h_pow_bound : (N : ℝ) ^ (-β_bound) ≤ (N : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_bound_le)

    have h_term_ltail : C_ltail * (N : ℝ) ^ (-β_ltail) ≤ C_ltail * (N : ℝ) ^ (-β) :=
      mul_le_mul_of_nonneg_left h_pow_ltail hC_ltail
    have h_term_riemann : C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) ≤ C_riemann * (N : ℝ) ^ (-β) :=
      mul_le_mul_of_nonneg_left h_pow_half hC_riemann
    have h_term_rtail : C_rtail * (N : ℝ) ^ (-β_rtail) ≤ C_rtail * (N : ℝ) ^ (-β) :=
      mul_le_mul_of_nonneg_left h_pow_rtail hC_rtail
    have h_term_bound : C_bound * (N : ℝ) ^ (-β_bound) ≤ C_bound * (N : ℝ) ^ (-β) :=
      mul_le_mul_of_nonneg_left h_pow_bound hC_bound

    have h_lt := h_ltail N hN
    have h_rt := h_rtail N hN
    have h_rie := h_riemann N hN
    have h_bd := h_bound N
    dsimp only at h_lt h_rt h_rie h_bd

    have h_sum :
      (∫ x in Set.Iic (-((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2)))), f x) +
      |(∫ x in Set.Icc (-((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2)))) ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2))), f x) -
        ∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), f (i * (1 / (Real.sqrt (N : ℝ) / 2))) * (1 / (Real.sqrt (N : ℝ) / 2))| +
      (∫ x in Set.Ici ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2))), f x) +
      f ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2))) * (1 / (Real.sqrt (N : ℝ) / 2)) ≤
      C_ltail * (N : ℝ) ^ (-β_ltail) + C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) + C_rtail * (N : ℝ) ^ (-β_rtail) + C_bound * (N : ℝ) ^ (-β_bound) :=
      add_le_add (add_le_add (add_le_add h_lt h_rie) h_rt) h_bd

    have h_sum2 : C_ltail * (N : ℝ) ^ (-β_ltail) + C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) + C_rtail * (N : ℝ) ^ (-β_rtail) + C_bound * (N : ℝ) ^ (-β_bound) ≤
        C_ltail * (N : ℝ) ^ (-β) + C_riemann * (N : ℝ) ^ (-β) + C_rtail * (N : ℝ) ^ (-β) + C_bound * (N : ℝ) ^ (-β) :=
      add_le_add (add_le_add (add_le_add h_term_ltail h_term_riemann) h_term_rtail) h_term_bound

    have h_algebraic : C_ltail * (N : ℝ) ^ (-β) + C_riemann * (N : ℝ) ^ (-β) + C_rtail * (N : ℝ) ^ (-β) + C_bound * (N : ℝ) ^ (-β) =
        C_total * (N : ℝ) ^ (-β) := by ring

    rw [h_algebraic] at h_sum2
    exact le_trans h_sum h_sum2

-- =========================================================================
-- PART 5: Squeeze Convergence of the Scaling Error (Proven)
-- =========================================================================

lemma scaling_error_limit (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f)
    (hf_norm : ∫ x, f x = 1)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      (1 - ∑ i ∈ s, f (i * Δx) * Δx) * log Δx)
    atTop
    (nhds 0) := by
  rcases scaling_error_rate_bound f hf hf_pos hf_int hf_norm hf_decay hd hf_deriv_decay with ⟨C', β, hβ, h_bound⟩
  rw [tendsto_zero_iff_abs_tendsto_zero]

  have h_le : (fun (N : ℕ) => (0 : ℝ)) ≤ᶠ[atTop] (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      |(1 - ∑ i ∈ s, f (i * Δx) * Δx) * log Δx|) := by
    apply Eventually.of_forall
    intro N
    exact abs_nonneg _

  have h_ue : (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      |(1 - ∑ i ∈ s, f (i * Δx) * Δx) * log Δx|) ≤ᶠ[atTop]
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ;
      -C' * ((N : ℝ) ^ (-β) * log Δx)) := by
    unfold EventuallyLE
    rw [eventually_atTop]
    use 4
    intro N hN
    dsimp only
    rw [abs_mul]
    have hN_pos : 0 < (N : ℝ) := by positivity
    have h_sqrt_ge : 2 ≤ Real.sqrt (N : ℝ) := by
      have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have h_sqrt_four : (2 : ℝ) = Real.sqrt 4 := by
        have h_sq : (4 : ℝ) = 2^2 := by norm_num
        rw [h_sq, Real.sqrt_sq_eq_abs]
        norm_num
      rw [h_sqrt_four]
      exact Real.sqrt_le_sqrt this
    have h_σ_ge : 1 ≤ Real.sqrt (N : ℝ) / 2 := by linarith
    have h_div : 0 < Real.sqrt (N : ℝ) / 2 := by linarith
    have h_Δx_le : 1 / (Real.sqrt (N : ℝ) / 2) ≤ 1 := by
      rw [div_le_iff₀ h_div]
      linarith
    have h_Δx_pos : 0 < 1 / (Real.sqrt (N : ℝ) / 2) := by
      exact div_pos (by linarith) (by linarith)
    have h_log_le : log (1 / (Real.sqrt (N : ℝ) / 2)) ≤ 0 :=
      log_nonpos (le_of_lt h_Δx_pos) h_Δx_le
    have h_abs_log : |log (1 / (Real.sqrt (N : ℝ) / 2))| = - log (1 / (Real.sqrt (N : ℝ) / 2)) :=
      abs_of_nonpos h_log_le
    rw [h_abs_log]
    have h_mul_le : |1 - ∑ i ∈ Finset.Icc (- (N : ℤ)) (N : ℤ), f (i * (1 / (Real.sqrt (N : ℝ) / 2))) * (1 / (Real.sqrt (N : ℝ) / 2))| * -log (1 / (Real.sqrt (N : ℝ) / 2)) ≤
        C' * (N : ℝ) ^ (-β) * -log (1 / (Real.sqrt (N : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact h_bound N (by linarith)
      · linarith [h_log_le]
    have h_ring : C' * (N : ℝ) ^ (-β) * -log (1 / (Real.sqrt (N : ℝ) / 2)) = -C' * ((N : ℝ) ^ (-β) * log (1 / (Real.sqrt (N : ℝ) / 2))) := by ring
    rw [h_ring] at h_mul_le
    exact h_mul_le

  have h_lim_upper : Tendsto (fun N : ℕ =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ;
      -C' * ((N : ℝ) ^ (-β) * log Δx)) atTop (nhds 0) := by
    have h_lim := polynomial_times_log_limit β hβ
    have h_mul := Tendsto.const_mul (-C') h_lim
    rw [mul_zero] at h_mul
    exact h_mul

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim_upper h_le h_ue


-- =========================================================================
-- PART 6: Auxiliary Limit Axiom (Entropy Core Convergence)
-- =========================================================================

axiom riemann_sum_entropy_convergence (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f)
    (hf_norm : ∫ x, f x = 1)
    (hf_ent_int : Integrable (fun x => f x * log (f x)))
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ∑ i ∈ s, f (i * Δx) * log (f (i * Δx)) * Δx)
    atTop
    (nhds (∫ x, f x * log (f x)))


-- =========================================================================
-- PART 7: The Main Theorem Proof (Proven)
-- =========================================================================

theorem discrete_to_continuous_entropy_convergence_proven (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f)
    (hf_norm : ∫ x, f x = 1)
    (hf_ent_int : Integrable (fun x => f x * log (f x)))
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let P := fun (i : ℤ) => f (i * Δx) * Δx
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      let H_discrete := - ∑ i ∈ s, P i * log (P i)
      H_discrete + log Δx)
    atTop
    (nhds (- ∫ x, f x * log (f x))) := by
  have h_decomp : (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let P := fun (i : ℤ) => f (i * Δx) * Δx
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      let H_discrete := - ∑ i ∈ s, P i * log (P i)
      H_discrete + log Δx) =ᶠ[atTop]
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ);
      (- ∑ i ∈ s, f (i * Δx) * log (f (i * Δx)) * Δx) +
      (1 - ∑ i ∈ s, f (i * Δx) * Δx) * log Δx) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro N hN
    dsimp only
    have h_pos_Δx : 0 < 1 / (Real.sqrt (N : ℝ) / 2) := by
      have hN_pos : 0 < (N : ℝ) := by positivity
      have h_sqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
      exact div_pos (by linarith) (by linarith)
    apply discrete_entropy_algebraic_decomposition
    · intro i _
      exact hf_pos (i * (1 / (Real.sqrt (N : ℝ) / 2)))
    · exact h_pos_Δx

  rw [Filter.tendsto_congr' h_decomp]

  have h_lim1 := riemann_sum_entropy_convergence f hf hf_pos hf_int hf_norm hf_ent_int hf_decay
  have h_lim2 := scaling_error_limit f hf hf_pos hf_int hf_norm hf_decay hd hf_deriv_decay

  have h_neg_lim1 := Tendsto.neg h_lim1
  have h_combined := Tendsto.add h_neg_lim1 h_lim2
  rw [add_zero] at h_combined
  exact h_combined
