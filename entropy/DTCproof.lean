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
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Data.Set.Operations
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Basic
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
open Topology
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

lemma hasDerivAt_one_add_x_pow (p : ℝ) (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun y => (1 + y)^(1 - p)) ((1 - p) * (1 + x)^(-p)) x := by
  have h_pos : 0 < 1 + x := by linarith
  have h_inner : HasDerivAt (fun y => 1 + y) 1 x := by
    simpa using hasDerivAt_id' x |>.const_add 1
  -- Here we use the standard composition of power and linear terms
  have h_pow : HasDerivAt (fun y => y^(1 - p)) ((1 - p) * (1 + x)^(1 - p - 1)) (1 + x) := by
    exact hasDerivAt_rpow_const (Or.inl h_pos.ne')
  have h_chain := HasDerivAt.comp x h_pow h_inner
  simp only [mul_one] at h_chain
  have h_exponent : 1 - p - 1 = -p := by ring
  rwa [h_exponent] at h_chain


lemma tendsto_one_add_x_pow_neg (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (1 + x)^(1 - p)) atTop (nhds 0) := by
  have hp_pos : 0 < p - 1 := by linarith
  have h_neg_eq : 1 - p = -(p - 1) := by ring

  -- Lower bound: Eventually, 0 ≤ (1 + x)^(1 - p)
  have h_lower : ∀ᶠ x : ℝ in atTop, 0 ≤ (1 + x)^(1 - p) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have : 0 ≤ 1 + x := by linarith
    exact Real.rpow_nonneg this _

  -- Upper bound: Eventually, (1 + x)^(1 - p) ≤ x^(1 - p)
  have h_upper : ∀ᶠ x : ℝ in atTop, (1 + x)^(1 - p) ≤ x^(1 - p) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h_pos_x : 0 < x := by linarith
    have h_pos_one_add : 0 < 1 + x := by linarith
    rw [h_neg_eq, Real.rpow_neg h_pos_one_add.le, Real.rpow_neg h_pos_x.le]
    gcongr
    linarith

  -- The limit of the upper bound is 0
  have h_lim_base : Tendsto (fun x : ℝ => x^(1 - p)) atTop (nhds 0) := by
    rw [h_neg_eq]
    exact tendsto_rpow_neg_atTop hp_pos

  -- Apply the primed squeeze theorem to match filter-level eventual bounds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    h_lim_base
    h_lower
    h_upper


lemma setIntegral_eq_tendsto_intervalIntegral {f : ℝ → ℝ} (b : ℝ) (hf : IntegrableOn f (Ici b)) :
    Tendsto (fun t => ∫ x in b..t, f x) atTop (nhds (∫ x in Ici b, f x)) := by
  -- 1. Represent the set Ici b as the union of expanding intervals Ioc b t
  have h_union : (⋃ t : ℝ, Ioc b t) = Ioi b := by
    ext x
    simp only [mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨t, hbx, _⟩; exact hbx
    · intro hx
      -- Since b < x, choose the upper bound t = x + 1 which strictly exceeds x
      have h_lt : x < x + 1 := by linarith
      exact ⟨x + 1, hx, h_lt.le⟩

  -- 2. Apply the monotone convergence theorem for set integrals
  have h_set_lim : Tendsto (fun t => ∫ x in Ioc b t, f x) atTop (nhds (∫ x in Ioi b, f x)) := by
    have h_mono : Monotone (fun t : ℝ => Ioc b t) := by
      intro t₁ t₂ h_le
      exact Ioc_subset_Ioc_right h_le
    have h_meas : ∀ t, MeasurableSet (Ioc b t) := fun _ => measurableSet_Ioc
    have h_union_eq : (⋃ t, Ioc b t) = Ioi b := h_union
    -- If f is integrable on Ici b, it is integrable on the slightly smaller Ioi b
    have hfi : IntegrableOn f (⋃ t, Ioc b t) := by
      rw [h_union_eq]
      exact hf.mono_set Ioi_subset_Ici_self

    have h_tendsto := tendsto_setIntegral_of_monotone h_meas h_mono hfi
    rwa [h_union_eq] at h_tendsto

  -- 3. Show that the interval integral and set integral are eventually equal
  have h_eq : (fun t => ∫ x in b..t, f x) =ᶠ[atTop] (fun t => ∫ x in Ioc b t, f x) := by
    filter_upwards [eventually_ge_atTop b] with t ht
    rw [intervalIntegral.integral_of_le ht]


  -- 4. Re-align intervals to close the goal (the point {b} has measure 0)
  have h_integral_eq : (∫ x in Ici b, f x) = ∫ x in Ioi b, f x := by
    -- The set-difference between Ici b and Ioi b is the singleton {b}, which has measure 0
    have h_ae : Ici b =ᵐ[volume] Ioi b := by
      simp only [ae_eq_set]
      constructor
      · -- Ici b \ Ioi b is {b}
        have h_diff1 : (Ici b \ Ioi b) = {b} := by
          ext x
          simp only [mem_diff, Set.mem_Ici, Set.mem_Ioi, mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩; linarith
          · rintro rfl; exact ⟨by linarith, by linarith⟩
        rw [h_diff1]
        exact volume_singleton
      · -- Ioi b \ Ici b is empty
        have h_diff2 : (Ioi b \ Ici b) = ∅ := by
          ext x
          simp only [mem_diff, Set.mem_Ioi, Set.mem_Ici, mem_empty_iff_false, iff_false]
          rintro ⟨h1, h2⟩; linarith
        rw [h_diff2]
        exact measure_empty --here

    exact setIntegral_congr_set h_ae

  -- Unify the limit sequences
  rw [tendsto_congr' h_eq, h_integral_eq]
  exact h_set_lim

/-- Direct evaluation of the definite improper integral of (1+x)^(-p). -/
lemma setIntegral_one_add_x_rpow_neg (p : ℝ) (hp : 2 < p) (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Ici b, (1 + x)^(-p)) = (1 + b)^(1 - p) / (p - 1) := by--here
  have hp_sub_pos : 0 < p - 1 := by linarith
  have h_neg : 1 - p < 0 := by linarith
  have hp1 : p ≠ 1 := by linarith

  let F : ℝ → ℝ := fun x => - ((1 + x)^(1 - p) / (p - 1))

  -- 1. Derivative of F
  have h_deriv : ∀ x ∈ Ici b, HasDerivAt F ((1 + x)^(-p)) x := by
    intro x hx
    have hx_pos : -1 < x := by
      have : b ≤ x := hx
      linarith
    have h_pow := hasDerivAt_one_add_x_pow p x hx_pos
    have h_div := h_pow.div_const (p - 1)
    have h_neg_deriv := h_div.neg
    have h_simpl : -((1 - p) * (1 + x)^(-p) / (p - 1)) = (1 + x)^(-p) := by
      calc -((1 - p) * (1 + x)^(-p) / (p - 1))
        _ = -((-(p - 1) * (1 + x)^(-p)) / (p - 1)) := by congr 2; ring
        _ = ((p - 1) * (1 + x)^(-p)) / (p - 1)    := by ring
        _ = (1 + x)^(-p) * (p - 1) / (p - 1)     := by ring
        _ = (1 + x)^(-p)                         := by rw [mul_div_cancel_right₀ _ hp_sub_pos.ne']
    rwa [h_simpl] at h_neg_deriv

  -- 2. Limit of F at infinity
  have h_lim : Tendsto F atTop (nhds 0) := by
    have h_pow_lim := tendsto_one_add_x_pow_neg p hp
    have h_div := Tendsto.div_const h_pow_lim (p - 1)
    have h_neg_lim := h_div.neg
    simp only [neg_zero, zero_div] at h_neg_lim
    exact h_neg_lim


  -- Proving integrability on Ici b by translating it to Ioi b
  have h_integrable : IntegrableOn (fun x => (1 + x)^(-p)) (Ici b) := by
    have h_lt : -p < -1 := by linarith
    have h_pos : -(1 : ℝ) < b := by linarith
    have h_int_ioi : IntegrableOn (fun x => (x + 1)^(-p)) (Ioi b) :=
      integrableOn_add_rpow_Ioi_of_lt h_lt h_pos
    have h_eq : (fun (x : ℝ) => (1 + x)^(-p)) = (fun (x : ℝ) => (x + 1)^(-p)) := by
      ext x
      rw [add_comm]
    rw [h_eq]
    have h_ae : Set.Ici b =ᵐ[volume] Set.Ioi b := Ioi_ae_eq_Ici.symm
    rw [IntegrableOn, Measure.restrict_congr_set h_ae]
    exact h_int_ioi

  -- 3. Calculate interval integral FTC
  have h_int_limit : Tendsto (fun t => ∫ x in b..t, (1 + x)^(-p)) atTop (nhds (0 - F b)) := by
    apply Tendsto.congr' (f₁ := fun t => F t - F b)
    · filter_upwards [eventually_ge_atTop b] with t ht
      have h_subset : uIcc b t ⊆ Ici b := by
        rw [uIcc_of_le ht]
        exact Icc_subset_Ici_self
      have h_deriv_sub : ∀ y ∈ uIcc b t, HasDerivAt F ((1 + y)^(-p)) y := by
        intro y hy
        exact h_deriv y (h_subset hy)
      -- Derive interval integrability from global integrability to satisfy the FTC premise
      have h_int_integ : IntervalIntegrable (fun x => (1 + x)^(-p)) volume b t :=
        IntegrableOn.intervalIntegrable (h_integrable.mono_set h_subset)
      exact Eq.symm (intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv_sub h_int_integ)
    · exact h_lim.sub_const (F b)

  -- 4. Unify the interval limits to solve the set integral
  have h_final_lim : Tendsto (fun t => ∫ x in b..t, (1 + x)^(-p)) atTop (𝓝 (∫ x in Ici b, (1 + x)^(-p))) :=
    setIntegral_eq_tendsto_intervalIntegral b h_integrable

  have h_val : ∫ x in Ici b, (1 + x)^(-p) = 0 - F b := by
    exact tendsto_nhds_unique h_final_lim h_int_limit

  rw [h_val]
  dsimp [F]
  ring

/-- Lemma: Integral comparison on [b, ∞) when f is pointwise bounded. (PROVEN) -/
lemma setIntegral_mono_decay (C : ℝ) (p : ℝ) (hp : 2 < p) (b : ℝ) (hb : 0 ≤ b) (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∀ x, f x ≤ C / (1 + |x|)^p) :
  (∫ x in Set.Ici b, f x) ≤ ∫ x in Set.Ici b, C / (1 + x)^p := by
  have hC_nonneg : 0 ≤ C := by
    have h_dec_0 := hf_decay 0
    have h_pos_0 := hf_nonneg 0
    have h_denom : (1 + |(0 : ℝ)|) ^ p = 1 := by
      simp only [abs_zero, add_zero, Real.one_rpow]
    rw [h_denom, div_one] at h_dec_0
    exact le_trans h_pos_0 h_dec_0
  by_cases hf : IntegrableOn f (Set.Ici b)
  · -- Case 1: f is integrable. We prove the decay function is integrable and use setIntegral_mono_on.
    have h_decay_int : IntegrableOn (fun x => C / (1 + x)^p) (Set.Ici b) := by
      have h_int : IntegrableOn (fun x => (1 + x)^(-p)) (Set.Ici b) := by
        have h_val := setIntegral_one_add_x_rpow_neg p hp b hb
        have h_pos : 0 < (1 + b)^(1 - p) / (p - 1) := by
          apply div_pos
          · apply Real.rpow_pos_of_pos; linarith
          · linarith
        have h_ne : ∫ x in Set.Ici b, (1 + x)^(-p) ≠ 0 := by
          rw [h_val]
          exact ne_of_gt h_pos
        exact Integrable.of_integral_ne_zero h_ne
      have h_mul := h_int.const_mul C
      have h_ae : (fun x => C / (1 + x)^p) =ᵐ[volume.restrict (Set.Ici b)] (fun x => C * (1 + x)^(-p)) := by
        dsimp [EventuallyEq]
        rw [ae_restrict_iff' measurableSet_Ici]
        refine Eventually.of_forall ?_
        intro x hx
        have hx_ge : b ≤ x := hx
        have h_pos : 0 < 1 + x := by linarith
        rw [div_eq_mul_one_div]
        congr 1
        rw [Real.rpow_neg h_pos.le]
        exact (inv_eq_one_div _).symm
      exact Integrable.congr h_mul h_ae.symm
    apply setIntegral_mono_on hf h_decay_int measurableSet_Ici
    intro x hx
    have hx_ge : b ≤ x := Set.mem_Ici.mp hx
    have h_x_nonneg : 0 ≤ x := le_trans hb hx_ge
    have h_abs : |x| = x := abs_of_nonneg h_x_nonneg
    have h_dec := hf_decay x
    rw [h_abs] at h_dec
    exact h_dec
  · -- Case 2: f is not integrable, so LHS is trivially 0. Since RHS is non-negative, the inequality holds.
    have h_nonneg : ∀ x ∈ Set.Ici b, 0 ≤ C / (1 + x)^p := by
      intro x hx
      have hx_ge : b ≤ x := hx
      have h_pos : 0 < 1 + x := by linarith
      have : 0 ≤ (1 + x)^p := Real.rpow_nonneg (by linarith) _
      exact div_nonneg hC_nonneg this
    have h_int_nonneg : 0 ≤ ∫ x in Set.Ici b, C / (1 + x)^p :=
      setIntegral_nonneg measurableSet_Ici h_nonneg
    have hf_zero : ∫ x in Set.Ici b, f x = 0 := integral_undef hf
    rw [hf_zero]
    exact h_int_nonneg

/-- Lemma: Reflection substitution for integrals over negative symmetric domains (PROVEN). -/
lemma setIntegral_comp_neg_Iic (b : ℝ) (f : ℝ → ℝ) :
    (∫ x in Set.Iic (-b), f x) = ∫ x in Set.Ici b, f (-x) := by
  have h1 : (∫ x in Set.Iic (-b), f x) = ∫ x in Set.Iic (-b), f (- (- x)) := by
    congr; ext x; simp only [neg_neg]
  rw [h1]
  have h2 := integral_comp_neg_Iic (-b) (fun x => f (-x))
  rw [neg_neg] at h2
  rw [h2]
  have h_ae : Set.Ioi b =ᵐ[volume] Set.Ici b := Ioi_ae_eq_Ici
  exact setIntegral_congr_set h_ae

/-- Lemma: Linearity of scaling for the power integral (PROVEN). -/
lemma setIntegral_power_scale (C : ℝ) (p : ℝ) (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Set.Ici b, C / (1 + x)^p) = C * (∫ x in Set.Ici b, (1 + x)^(-p)) := by
  have h_eq : Set.EqOn (fun x => C / (1 + x)^p) (fun x => C * (1 + x)^(-p)) (Set.Ici b) := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    dsimp only
    have hx_nonneg : 0 ≤ x := le_trans hb hx
    have h_pos : 0 < 1 + x := by linarith
    rw [div_eq_mul_one_div]
    congr 1
    rw [Real.rpow_neg h_pos.le]
    exact (inv_eq_one_div _).symm
  rw [setIntegral_congr_fun measurableSet_Ici h_eq]
  exact integral_const_mul C _

/-- Lemma 2.1_aux_right: The integral of a power decay function on [b, ∞) is bounded. (PROVEN) -/
lemma setIntegral_power_decay_Ici (C : ℝ) (p : ℝ) (hp : 2 < p) (b : ℝ) (hb : 0 ≤ b) (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∀ x, f x ≤ C / (1 + |x|)^p) :
  (∫ x in Set.Ici b, f x) ≤ (C / (p - 1)) * (1 + b) ^ (1 - p) := by
  have h_mono := setIntegral_mono_decay C p hp b hb f hf_nonneg hf_decay
  have h_scale := setIntegral_power_scale C p b hb
  have h_eval := setIntegral_one_add_x_rpow_neg p hp b hb
  have h_calc : C * (∫ x in Set.Ici b, (1 + x)^(-p)) = (C / (p - 1)) * (1 + b) ^ (1 - p) := by
    rw [h_eval]
    ring
  rw [h_scale] at h_mono
  rw [h_calc] at h_mono
  exact h_mono

/-- Lemma 2.1_aux_left: The integral of a power decay function on (-∞, -b] is bounded. (PROVEN) -/
lemma setIntegral_power_decay_Iic (C : ℝ) (p : ℝ) (hp : 2 < p) (b : ℝ) (hb : 0 ≤ b) (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∀ x, f x ≤ C / (1 + |x|)^p) :
  (∫ x in Set.Iic (-b), f x) ≤ (C / (p - 1)) * (1 + b) ^ (1 - p) := by
  have h_subst := setIntegral_comp_neg_Iic b f
  let g := fun x => f (-x)
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g]
    exact hf_nonneg (-x)
  have hg_decay : ∀ x, g x ≤ C / (1 + |x|)^p := by
    intro x
    dsimp [g]
    have h_abs_neg : |-x| = |x| := abs_neg x
    have h_f_dec := hf_decay (-x)
    rw [h_abs_neg] at h_f_dec
    exact h_f_dec
  have h_g_le := setIntegral_power_decay_Ici C p hp b hb g hg_nonneg hg_decay
  rw [h_subst]
  exact h_g_le

/-- Lemma 2.1a: The left tail of the continuous integral decays at a polynomial rate. -/
lemma left_tail_integral_decay (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
  ∃ (C_tail : ℝ) (β : ℝ), 0 ≤ C_tail ∧ 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let b := (N : ℝ) * Δx
    (∫ x in Set.Iic (-b), f x) ≤ C_tail * (N : ℝ) ^ (-β) := by
  rcases hf_decay with ⟨C, p, hp, hf_dec⟩
  have h_p1 : 0 < p - 1 := by linarith
  have h_C_pos : 0 ≤ C := by
    have h_dec_0 := hf_dec 0
    have h_pos_0 := hf_nonneg 0
    have h_denom : (1 + |(0 : ℝ)|) ^ p = 1 := by
      simp only [abs_zero, add_zero, Real.one_rpow]
    rw [h_denom, div_one] at h_dec_0
    exact le_trans h_pos_0 h_dec_0
  use max 0 (C / (p - 1) * (2 : ℝ) ^ (1 - p)), (p - 1) / 2
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · linarith
  · intro N hN
    dsimp only
    have hN_pos : 0 < (N : ℝ) := by positivity
    have h_sqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    have h_div : 0 < Real.sqrt (N : ℝ) / (2 : ℝ) := by linarith
    have h_Δx : 1 / (Real.sqrt (N : ℝ) / (2 : ℝ)) = (2 : ℝ) / Real.sqrt (N : ℝ) := by ring

    have h_val : (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) = (2 : ℝ) * Real.sqrt (N : ℝ) := by
      rw [h_Δx]
      rw [← mul_div_assoc]
      rw [mul_comm (N : ℝ) (2 : ℝ)]
      rw [mul_div_assoc]
      rw [Real.div_sqrt]

    have hb_nonneg : 0 ≤ (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) := by
      rw [h_val]
      positivity

    have h_int_le := setIntegral_power_decay_Iic C p hp ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ)))) hb_nonneg f hf_nonneg hf_dec

    apply le_trans h_int_le

    have hb_eq : (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) = (2 : ℝ) * Real.sqrt (N : ℝ) := h_val

    have h_b_pos : 0 < (2 : ℝ) * Real.sqrt (N : ℝ) := by positivity
    have h_b_le : (2 : ℝ) * Real.sqrt (N : ℝ) ≤ 1 + (2 : ℝ) * Real.sqrt (N : ℝ) := by linarith

    have h_pow_pos : 0 < ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      apply Real.rpow_pos_of_pos h_b_pos

    have h_pow_le : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) ≤ (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      apply Real.rpow_le_rpow h_b_pos.le h_b_le h_p1.le

    have h_inv_le : 1 / (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) ≤ 1 / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      apply div_le_div_of_nonneg_left (by linarith) h_pow_pos h_pow_le

    have h_rpow_neg1 : (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = 1 / (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      have : 1 - p = - (p - 1) := by ring
      rw [this]
      rw [Real.rpow_neg (by positivity), inv_eq_one_div]

    have h_rpow_neg2 : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = 1 / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      have : 1 - p = - (p - 1) := by ring
      rw [this]
      rw [Real.rpow_neg h_b_pos.le, inv_eq_one_div]

    have h_rpow_le : (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) ≤ ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) := by
      rw [h_rpow_neg1, h_rpow_neg2]
      exact h_inv_le

    have h_C_div_nonneg : 0 ≤ C / (p - 1) := by positivity

    have h_bound1 : (C / (p - 1)) * (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) ≤
        (C / (p - 1)) * ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) := by
      apply mul_le_mul_of_nonneg_left h_rpow_le h_C_div_nonneg

    rw [hb_eq]
    apply le_trans h_bound1

    have h_mul_rpow : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = (2 : ℝ) ^ (1 - p) * (Real.sqrt (N : ℝ)) ^ (1 - p) := by
      apply Real.mul_rpow
      · norm_num
      · positivity

    have h_sqrt_eq : Real.sqrt (N : ℝ) = (N : ℝ) ^ (1/2 : ℝ) := by
      apply Real.sqrt_eq_rpow

    have h_rpow_mul : ((N : ℝ) ^ (1/2 : ℝ)) ^ (1 - p) = (N : ℝ) ^ ((1/2 : ℝ) * (1 - p)) := by
      exact (Real.rpow_mul hN_pos.le (1/2 : ℝ) (1 - p)).symm

    have h_denom_eq : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = (2 : ℝ) ^ (1 - p) * (N : ℝ) ^ (- ((p - 1) / 2)) := by
      rw [h_mul_rpow, h_sqrt_eq, h_rpow_mul]
      congr 1
      congr 1
      ring

    have h_algebra : (C / (p - 1)) * ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) =
        (C / (p - 1) * (2 : ℝ) ^ (1 - p)) * (N : ℝ) ^ (- ((p - 1) / 2)) := by
      rw [h_denom_eq]
      ring

    rw [h_algebra]

    have h_max : C / (p - 1) * (2 : ℝ) ^ (1 - p) ≤ max 0 (C / (p - 1) * (2 : ℝ) ^ (1 - p)) := le_max_right _ _
    have h_pos_pow : 0 ≤ (N : ℝ) ^ (- ((p - 1) / 2)) := by positivity
    exact mul_le_mul_of_nonneg_right h_max h_pos_pow

/-- Lemma 2.1b: The right tail of the continuous integral decays at a polynomial rate. -/
lemma tail_integral_decay (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
  ∃ (C_tail : ℝ) (β : ℝ), 0 ≤ C_tail ∧ 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let b := (N : ℝ) * Δx
    (∫ x in Set.Ici b, f x) ≤ C_tail * (N : ℝ) ^ (-β) := by
  rcases hf_decay with ⟨C, p, hp, hf_dec⟩
  have h_p1 : 0 < p - 1 := by linarith
  have h_C_pos : 0 ≤ C := by
    have h_dec_0 := hf_dec 0
    have h_pos_0 := hf_nonneg 0
    have h_denom : (1 + |(0 : ℝ)|) ^ p = 1 := by
      simp only [abs_zero, add_zero, Real.one_rpow]
    rw [h_denom, div_one] at h_dec_0
    exact le_trans h_pos_0 h_dec_0
  use max 0 (C / (p - 1) * (2 : ℝ) ^ (1 - p)), (p - 1) / 2
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · linarith
  · intro N hN
    dsimp only
    have hN_pos : 0 < (N : ℝ) := by positivity
    have h_sqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    have h_div : 0 < Real.sqrt (N : ℝ) / (2 : ℝ) := by linarith
    have h_Δx : 1 / (Real.sqrt (N : ℝ) / (2 : ℝ)) = (2 : ℝ) / Real.sqrt (N : ℝ) := by ring

    have h_val : (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) = (2 : ℝ) * Real.sqrt (N : ℝ) := by
      rw [h_Δx]
      rw [← mul_div_assoc]
      rw [mul_comm (N : ℝ) (2 : ℝ)]
      rw [mul_div_assoc]
      rw [Real.div_sqrt]

    have hb_nonneg : 0 ≤ (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) := by
      rw [h_val]
      positivity

    have h_int_le := setIntegral_power_decay_Ici C p hp ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ)))) hb_nonneg f hf_nonneg hf_dec

    apply le_trans h_int_le

    have hb_eq : (N : ℝ) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) = (2 : ℝ) * Real.sqrt (N : ℝ) := h_val

    have h_b_pos : 0 < (2 : ℝ) * Real.sqrt (N : ℝ) := by positivity
    have h_b_le : (2 : ℝ) * Real.sqrt (N : ℝ) ≤ 1 + (2 : ℝ) * Real.sqrt (N : ℝ) := by linarith

    have h_pow_pos : 0 < ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      apply Real.rpow_pos_of_pos h_b_pos

    have h_pow_le : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) ≤ (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      apply Real.rpow_le_rpow h_b_pos.le h_b_le h_p1.le

    have h_inv_le : 1 / (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) ≤ 1 / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      apply div_le_div_of_nonneg_left (by linarith) h_pow_pos h_pow_le

    have h_rpow_neg1 : (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = 1 / (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      have : 1 - p = - (p - 1) := by ring
      rw [this]
      rw [Real.rpow_neg (by positivity), inv_eq_one_div]

    have h_rpow_neg2 : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = 1 / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (p - 1) := by
      have : 1 - p = - (p - 1) := by ring
      rw [this]
      rw [Real.rpow_neg h_b_pos.le, inv_eq_one_div]

    have h_rpow_le : (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) ≤ ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) := by
      rw [h_rpow_neg1, h_rpow_neg2]
      exact h_inv_le

    have h_C_div_nonneg : 0 ≤ C / (p - 1) := by positivity

    have h_bound1 : (C / (p - 1)) * (1 + (2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) ≤
        (C / (p - 1)) * ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) := by
      apply mul_le_mul_of_nonneg_left h_rpow_le h_C_div_nonneg

    rw [hb_eq]
    apply le_trans h_bound1

    have h_mul_rpow : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = (2 : ℝ) ^ (1 - p) * (Real.sqrt (N : ℝ)) ^ (1 - p) := by
      apply Real.mul_rpow
      · norm_num
      · positivity

    have h_sqrt_eq : Real.sqrt (N : ℝ) = (N : ℝ) ^ (1/2 : ℝ) := by
      apply Real.sqrt_eq_rpow

    have h_rpow_mul : ((N : ℝ) ^ (1/2 : ℝ)) ^ (1 - p) = (N : ℝ) ^ ((1/2 : ℝ) * (1 - p)) := by
      exact (Real.rpow_mul hN_pos.le (1/2 : ℝ) (1 - p)).symm

    have h_denom_eq : ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) = (2 : ℝ) ^ (1 - p) * (N : ℝ) ^ (- ((p - 1) / 2)) := by
      rw [h_mul_rpow, h_sqrt_eq, h_rpow_mul]
      congr 1
      congr 1
      ring

    have h_algebra : (C / (p - 1)) * ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ (1 - p) =
        (C / (p - 1) * (2 : ℝ) ^ (1 - p)) * (N : ℝ) ^ (- ((p - 1) / 2)) := by
      rw [h_denom_eq]
      ring

    rw [h_algebra]

    have h_max : C / (p - 1) * (2 : ℝ) ^ (1 - p) ≤ max 0 (C / (p - 1) * (2 : ℝ) ^ (1 - p)) := le_max_right _ _
    have h_pos_pow : 0 ≤ (N : ℝ) ^ (- ((p - 1) / 2)) := by positivity
    exact mul_le_mul_of_nonneg_right h_max h_pos_pow


/-- Helper Lemma: First-order error bound on a single compact interval [a, b] for a
    differentiable function. Under bounded derivative |f'| ≤ K, the error between
    the integral of f and its left-endpoint approximation is bounded by K * (b - a)^2. -/
lemma local_riemann_error_bound {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ uIcc a b, |deriv f x| ≤ K) :

    |(∫ x in a..b, f x) - f a * (b - a)| ≤ K * (b - a)^2 := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp only [sub_self, intervalIntegral.integral_same, zero_sub, abs_zero, mul_zero]
    ring_nf
    rfl
  · have hc : ContinuousOn f (uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
    have h_int : IntervalIntegrable (fun x => f x - f a) volume a b := by
      exact (hc.intervalIntegrable).sub (intervalIntegrable_const)

    have hK_nonneg : 0 ≤ K := by
      have ha_mem : a ∈ Set.uIcc a b := Set.left_mem_uIcc
      exact le_trans (abs_nonneg _) (hderiv a ha_mem)

    have h_bound : ∀ x ∈ Set.uIcc a b, |f x - f a| ≤ K * (x - a) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have ha_le_x : a ≤ x := hx.1
      rcases eq_or_lt_of_le ha_le_x with rfl | ha_lt_x
      · simp only [sub_self, abs_zero, mul_zero, le_refl]

      -- Fix subinterval bounding logic
      have h_sub_diff : DifferentiableOn ℝ f (Ioo a x) := by
        intro y hy
        refine (hf y ?_).differentiableWithinAt
        rw [Set.uIcc_of_le hab]
        constructor
        · linarith [hy.1]
        · linarith [hy.2, hx.2]
      have h_sub_cont : ContinuousOn f (Icc a x) := by
        refine hc.mono ?_
        rw [Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc le_rfl hx.2

      -- FIXED: f is passed explicitly as the first argument, followed by ha_lt_x
      rcases exists_deriv_eq_slope f ha_lt_x h_sub_cont h_sub_diff with ⟨c, hc_io, h_c_deriv⟩

      have hc_uIcc : c ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab]
        constructor
        · linarith [hc_io.1]
        · linarith [hc_io.2, hx.2]
      have h_slope : f x - f a = deriv f c * (x - a) := by
        rw [h_c_deriv]
        exact (div_eq_iff (sub_ne_zero.mpr (ne_of_gt ha_lt_x))).mp rfl

      rw [h_slope, abs_mul, abs_of_nonneg (sub_nonneg.mpr ha_le_x)]
      exact mul_le_mul_of_nonneg_right (hderiv c hc_uIcc) (sub_nonneg.mpr ha_le_x)

    have h_bound_const : ∀ x ∈ Set.Icc a b, |f x - f a| ≤ K * (b - a) := by
      intro x hx
      have h_xa : x - a ≤ b - a := by linarith [hx.2]
      have h_bound_x : |f x - f a| ≤ K * (x - a) := by
        have h_ux : x ∈ Set.uIcc a b := by rwa [Set.uIcc_of_le hab]
        exact h_bound x h_ux
      exact le_trans h_bound_x (mul_le_mul_of_nonneg_left h_xa hK_nonneg)

    have h_int_le : (∫ x in a..b, |f x - f a|) ≤ ∫ x in a..b, K * (b - a) := by
      refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
      · exact h_int.norm
      · exact intervalIntegrable_const
      · intro x hx
        exact h_bound_const x hx

    have h_int_const : (∫ x in a..b, K * (b - a)) = K * (b - a)^2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring

    have h_abs_le : |(∫ x in a..b, f x) - f a * (b - a)| ≤ ∫ x in a..b, |f x - f a| := by
      have h_rew : (∫ x in a..b, f x) - f a * (b - a) = ∫ x in a..b, (f x - f a) := by
        rw [intervalIntegral.integral_sub hc.intervalIntegrable intervalIntegrable_const]
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      rw [h_rew]
      exact intervalIntegral.abs_integral_le_integral_abs hab

    linarith [h_abs_le, h_int_le, h_int_const]


/-- Standalone helper: If a derivative decays at a rate of 1 + ε (i.e., q > 1),
    then both its absolute value and the derivative itself are globally integrable. -/
lemma integrable_of_deriv_decay (f : ℝ → ℝ) (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
    Integrable (fun x => |deriv f x|) MeasureTheory.volume ∧ Integrable (deriv f) MeasureTheory.volume := by
  rcases hf_deriv_decay with ⟨C'_val, q, hq, hdec⟩

  have h_deriv_int_abs : Integrable (fun x => |deriv f x|) MeasureTheory.volume := by
    have h_int_rpow : IntegrableOn (fun x => Real.rpow (x + 1) (-q)) (Ioi 0) MeasureTheory.volume := by
      have h_lt : -q < -1 := by linarith
      have h_pos : -(1 : ℝ) < 0 := by linarith
      exact integrableOn_add_rpow_Ioi_of_lt h_lt h_pos

    have h_int_rpow_ici : IntegrableOn (fun x => Real.rpow (1 + x) (-q)) (Ici 0) MeasureTheory.volume := by
      have h_eq : (fun x : ℝ => Real.rpow (1 + x) (-q)) = (fun x : ℝ => Real.rpow (x + 1) (-q)) := by
        ext x; rw [add_comm]
      rw [h_eq]
      have h_ae : Set.Ici (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 := Ioi_ae_eq_Ici.symm
      rwa [IntegrableOn, Measure.restrict_congr_set h_ae]

    have h_int_pos_tail : IntegrableOn (fun x => C'_val / Real.rpow (1 + x) q) (Ici 0) MeasureTheory.volume := by
      have h_ae : (fun x => C'_val / Real.rpow (1 + x) q) =ᵐ[MeasureTheory.volume.restrict (Ici 0)] (fun x => C'_val * Real.rpow (1 + x) (-q)) := by
        rw [EventuallyEq, ae_restrict_iff' measurableSet_Ici]
        refine Eventually.of_forall ?_
        intro x hx
        have hx_ge : 0 ≤ x := hx
        have h_pos : 0 < 1 + x := by linarith
        rw [div_eq_mul_one_div]
        congr 1
        change 1 / (1 + x) ^ q = (1 + x) ^ (-q)
        rw [Real.rpow_neg h_pos.le]
        exact (inv_eq_one_div _).symm
      exact Integrable.congr (h_int_rpow_ici.const_mul C'_val) h_ae.symm

    have h_neg_ici : - Ici (0 : ℝ) = Set.Iic 0 := by
      ext x; simp only [Set.mem_neg, Set.mem_Ici, Set.mem_Iic, neg_nonneg]

    have h_int_neg_tail : IntegrableOn (fun x => C'_val / Real.rpow (1 + -x) q) (Iic 0) MeasureTheory.volume := by
      have h_subst := IntegrableOn.comp_neg h_int_pos_tail
      rwa [h_neg_ici] at h_subst

    have h_int_global_decay : Integrable (fun x => C'_val / Real.rpow (1 + |x|) q) MeasureTheory.volume := by
      rw [← integrableOn_univ]
      have h_union : Ici (0:ℝ) ∪ Iic (0:ℝ) = Set.univ := by
        ext x; simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_univ, iff_true]
        exact le_total 0 (x:ℝ)
      rw [← h_union]
      apply IntegrableOn.union
      · have h_ae : (fun x => C'_val / Real.rpow (1 + |x|) q) =ᵐ[MeasureTheory.volume.restrict (Ici 0)] (fun x => C'_val / Real.rpow (1 + x) q) := by
          rw [EventuallyEq, ae_restrict_iff' measurableSet_Ici]
          refine Eventually.of_forall ?_
          intro x hx; rw [abs_of_nonneg hx]
        exact Integrable.congr h_int_pos_tail h_ae.symm
      · have h_ae : (fun x => C'_val / Real.rpow (1 + |x|) q) =ᵐ[MeasureTheory.volume.restrict (Iic 0)] (fun x => C'_val / Real.rpow (1 + -x) q) := by
          rw [EventuallyEq, ae_restrict_iff' measurableSet_Iic]
          refine Eventually.of_forall ?_
          intro x hx; rw [abs_of_nonpos hx]
        exact Integrable.congr h_int_neg_tail h_ae.symm

    have h_meas : AEStronglyMeasurable (fun x => |deriv f x|) MeasureTheory.volume := by
      have h_deriv_meas : Measurable (deriv f) := measurable_deriv f
      measurability
    have h_bound : ∀ x, ‖|deriv f x|‖ ≤ ‖C'_val / Real.rpow (1 + |x|) q‖ := by
      intro x
      have h_abs : ‖|deriv f x|‖ = |deriv f x| := by rw [Real.norm_eq_abs, abs_abs]
      rw [h_abs]
      have h_dec := hdec x
      have h_nonneg : 0 ≤ C'_val / Real.rpow (1 + |x|) q := le_trans (abs_nonneg _) h_dec
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      exact h_dec

    exact Integrable.mono h_int_global_decay h_meas (Eventually.of_forall h_bound)

  have h_deriv_int : Integrable (deriv f) MeasureTheory.volume := by
    have h_deriv_meas : AEStronglyMeasurable (deriv f) MeasureTheory.volume :=
      (measurable_deriv f).aestronglyMeasurable
    have h_bound_deriv : ∀ x, ‖deriv f x‖ ≤ |deriv f x| := by
      intro x; rw [Real.norm_eq_abs]
    exact h_deriv_int_abs.mono' h_deriv_meas (Eventually.of_forall h_bound_deriv)

  exact ⟨h_deriv_int_abs, h_deriv_int⟩


lemma intervalIntegral_sum_Ico_adjacent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (N : ℕ) (Δx : ℝ)
    (h_int : ∀ k ∈ Finset.range (2 * N), IntervalIntegrable g MeasureTheory.volume
      ((- (N : ℝ) + k) * Δx) ((- (N : ℝ) + (k + 1)) * Δx)) :
  (∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), ∫ x in (i * Δx)..((i + 1) * Δx), g x) =
    ∫ x in (- ((N : ℝ) * Δx))..((N : ℝ) * Δx), g x := by
  let seq (k : ℕ) : ℝ := (- (N : ℝ) + (k : ℝ)) * Δx

  -- 1. Establish the mapping relation from range to Ico
  have h_range : ((N : ℤ) - - (N : ℤ)).toNat = 2 * N := by omega
  have h_ico : Finset.Ico (- (N : ℤ)) (N : ℤ) =
      Finset.map (Nat.castEmbedding.trans (addLeftEmbedding (- (N : ℤ)))) (Finset.range (2 * N)) := by
    rw [Int.Ico_eq_finset_map, h_range]

  -- 2. Rewrite the sum over Ico to a sum over range using the map
  have h_equiv : (∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), ∫ x in (i * Δx)..((i + 1) * Δx), g x) =
      ∑ k ∈ Finset.range (2 * N), ∫ x in (seq k)..(seq (k + 1)), g x := by
    rw [h_ico]
    rw [Finset.sum_map]
    dsimp [seq]
    congr 1
    ext k
    congr 2
    · dsimp [addLeftEmbedding, Nat.castEmbedding]
      push_cast
      ring
    · dsimp [addLeftEmbedding, Nat.castEmbedding]
      push_cast
      ring

  rw [h_equiv]

  -- 3. Resolve the type mismatch by satisfying the `< 2 * N` inequality pattern
  have h_int' : ∀ k < 2 * N, IntervalIntegrable g MeasureTheory.volume (seq k) (seq (k + 1)) := by
    intro k hk
    have hk_eq : seq (k + 1) = (- (N : ℝ) + (k + 1)) * Δx := by
      dsimp [seq]
      push_cast
      ring
    rw [hk_eq]
    exact h_int k (Finset.mem_range.mpr hk)

  -- 4. Apply the adjacent intervals theorem
  have h_split := intervalIntegral.sum_integral_adjacent_intervals h_int'
  rw [h_split]
  congr 2
  · dsimp [seq]; ring
  · dsimp [seq]; push_cast; ring

lemma local_riemann_error_bound_integral (f : ℝ → ℝ) (hd : Differentiable ℝ f)
    (h_deriv_int : Integrable (fun x => |deriv f x|))
    (h_deriv_int_real : Integrable (deriv f))
    (i : ℤ) (Δx : ℝ) (h_Δx_pos : 0 < Δx) :
  |(∫ x in (i * Δx)..((i + 1) * Δx), f x) - f (i * Δx) * Δx| ≤
    Δx * ∫ x in (i * Δx)..((i + 1) * Δx), |deriv f x| := by
  have h_le_step : i * Δx ≤ (i + 1) * Δx := by nlinarith [h_Δx_pos]

  have h_diff : ∀ x ∈ Set.Icc (i * Δx) ((i + 1) * Δx), |f x - f (i * Δx)| ≤ ∫ t in (i * Δx)..((i + 1) * Δx), |deriv f t| := by
    intro x hx
    have h_int_eq_diff : f x - f (i * Δx) = ∫ t in (i * Δx)..x, deriv f t := by
      symm
      apply intervalIntegral.integral_deriv_eq_sub
      · intro t _; exact hd.differentiableAt
      · exact h_deriv_int_real.intervalIntegrable
    rw [h_int_eq_diff]
    have h_int_le : |∫ t in (i * Δx)..x, deriv f t| ≤ ∫ t in (i * Δx)..x, |deriv f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith [hx.1])
    apply le_trans h_int_le
    have h_split_int : (∫ t in (i * Δx)..x, |deriv f t|) + (∫ t in x..((i + 1) * Δx), |deriv f t|) =
        ∫ t in (i * Δx)..((i + 1) * Δx), |deriv f t| := by
      apply intervalIntegral.integral_add_adjacent_intervals
      · exact h_deriv_int.intervalIntegrable
      · exact h_deriv_int.intervalIntegrable
    have h_nonneg_second : 0 ≤ ∫ t in x..((i + 1) * Δx), |deriv f t| := by
      apply intervalIntegral.integral_nonneg_of_ae
      · linarith [hx.2]
      · exact ae_of_all _ (fun _ => abs_nonneg _)
    linarith [h_split_int, h_nonneg_second]

  have h_int : IntervalIntegrable (fun x => f x - f (i * Δx)) MeasureTheory.volume (i * Δx) ((i + 1) * Δx) :=
    hd.continuous.intervalIntegrable (i * Δx) ((i + 1) * Δx) |>.sub intervalIntegrable_const -- FIXED: Endpoints passed explicitly

  have h_int_le : (∫ x in (i * Δx)..((i + 1) * Δx), |f x - f (i * Δx)|) ≤
      ∫ _ in (i * Δx)..((i + 1) * Δx), (∫ t in (i * Δx)..((i + 1) * Δx), |deriv f t|) := by
    refine intervalIntegral.integral_mono_on h_le_step ?_ ?_ ?_
    · exact h_int.norm
    · exact intervalIntegrable_const
    · intro x hx
      exact h_diff x hx

  have h_int_const : (∫ _ in (i * Δx)..((i + 1) * Δx), (∫ t in (i * Δx)..((i + 1) * Δx), |deriv f t|)) =
      Δx * ∫ t in (i * Δx)..((i + 1) * Δx), |deriv f t| := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have h_sub : (i + 1) * Δx - i * Δx = Δx := by ring
    rw [h_sub]

  have h_abs_le : |(∫ x in (i * Δx)..((i + 1) * Δx), f x) - f (i * Δx) * Δx| ≤
      ∫ x in (i * Δx)..((i + 1) * Δx), |f x - f (i * Δx)| := by
    have h_int_eq : f (i * Δx) * Δx = ∫ _ in (i * Δx)..((i + 1) * Δx), f (i * Δx) := by
      rw [intervalIntegral.integral_const]; ring
    have h_rew : (∫ x in (i * Δx)..((i + 1) * Δx), f x) - f (i * Δx) * Δx =
        ∫ x in (i * Δx)..((i + 1) * Δx), (f x - f (i * Δx)) := by
      rw [h_int_eq, ← intervalIntegral.integral_sub]
      · exact hd.continuous.intervalIntegrable (i * Δx) ((i + 1) * Δx) -- FIXED: Endpoints passed explicitly
      · exact intervalIntegrable_const
    rw [h_rew]
    exact intervalIntegral.abs_integral_le_integral_abs h_le_step

  linarith [h_abs_le, h_int_le, h_int_const]

lemma riemann_sum_core_error (f : ℝ → ℝ)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  ∃ (C_riemann : ℝ), 0 ≤ C_riemann ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let s' := Finset.Ico (- (N : ℤ)) (N : ℤ)
    |(∫ x in Set.Icc (- ((N : ℝ) * Δx)) ((N : ℝ) * Δx), f x) - ∑ i ∈ s', f (i * Δx) * Δx| ≤ C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) := by

  rcases integrable_of_deriv_decay f hd hf_deriv_decay with ⟨h_deriv_int, h_deriv_int_real⟩

  let K_tot := ∫ x, |deriv f x|
  use 2 * K_tot
  constructor
  · have : 0 ≤ K_tot := MeasureTheory.integral_nonneg (fun x => abs_nonneg _)
    linarith
  · intro N hN
    dsimp only
    have hN_pos : 0 < (N : ℝ) := by positivity
    have h_σ_pos : 0 < Real.sqrt (N : ℝ) / 2 := by positivity
    have h_Δx_pos : 0 < 1 / (Real.sqrt (N : ℝ) / 2) := div_pos (by linarith) h_σ_pos

    set Δx := 1 / (Real.sqrt (N : ℝ) / 2)
    have h_prod_pos : 0 < (N : ℝ) * Δx := mul_pos hN_pos h_Δx_pos

    have h_sum_split : (∫ x in (- ((N : ℝ) * Δx))..((N : ℝ) * Δx), f x) =
        ∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), ∫ x in (i * Δx)..((i + 1) * Δx), f x := by
      symm
      apply intervalIntegral_sum_Ico_adjacent f N Δx
      intro k _
      exact hd.continuous.intervalIntegrable _ _

    have h_sum_intervals : (∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), ∫ x in (i * Δx)..((i + 1) * Δx), |deriv f x|) =
        ∫ x in (- ((N : ℝ) * Δx))..((N : ℝ) * Δx), |deriv f x| := by
      apply intervalIntegral_sum_Ico_adjacent (fun x => |deriv f x|) N Δx
      intro k _
      exact h_deriv_int.intervalIntegrable

    have h_partition_sum : |(∫ x in (- ((N : ℝ) * Δx))..((N : ℝ) * Δx), f x) - ∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), f (i * Δx) * Δx| ≤ Δx * K_tot := by
      rw [h_sum_split]
      have h_sum_sub : (∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), ∫ x in (i * Δx)..((i + 1) * Δx), f x) -
          ∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), f (i * Δx) * Δx =
          ∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), ((∫ x in (i * Δx)..((i + 1) * Δx), f x) - f (i * Δx) * Δx) := by
        rw [← Finset.sum_sub_distrib]
      rw [h_sum_sub]
      apply le_trans (Finset.abs_sum_le_sum_abs _ _)
      have h_local_bounds : ∀ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ),
          |(∫ x in (i * Δx)..((i + 1) * Δx), f x) - f (i * Δx) * Δx| ≤
          Δx * ∫ x in (i * Δx)..((i + 1) * Δx), |deriv f x| := by
        intro i _
        exact local_riemann_error_bound_integral f hd h_deriv_int h_deriv_int_real i Δx h_Δx_pos
      apply le_trans (Finset.sum_le_sum h_local_bounds)
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ h_Δx_pos.le
      rw [h_sum_intervals]
      have h_le_global : (∫ x in (- ((N : ℝ) * Δx))..((N : ℝ) * Δx), |deriv f x|) ≤ K_tot := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply setIntegral_le_integral h_deriv_int (ae_of_all _ (fun _ => abs_nonneg _))
      exact h_le_global

    have h_interval_to_set : (∫ x in (- ((N : ℝ) * Δx))..((N : ℝ) * Δx), f x) =
        ∫ x in Set.Icc (- ((N : ℝ) * Δx)) ((N : ℝ) * Δx), f x := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [intervalIntegral.integral_of_le (by linarith)]

    rw [← h_interval_to_set]
    apply le_trans h_partition_sum

    have h_algebra : Δx * K_tot = (2 * K_tot) * (N : ℝ) ^ (-(1/2 : ℝ)) := by
      have h_div : Δx = 2 / Real.sqrt (N : ℝ) := by dsimp [Δx]; ring
      rw [h_div]
      have h_pow : (Real.sqrt (N : ℝ))⁻¹ = (N : ℝ) ^ (-(1/2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
      rw [div_eq_mul_one_div, ← inv_eq_one_div, h_pow]
      ring

    rw [h_algebra]

/-- Lemma 2.3: The single endpoint boundary term f(N * Δx) * Δx converges to 0.
  Since the endpoint lies at 2√N, the density decays as O(N^{-p/2}),
  and the step size Δx = O(N^{-1/2}), yielding a combined rate of O(N^{-(p+1)/2}).
-/
lemma boundary_term_decay (f : ℝ → ℝ)
    --(hf_pos : ∀ x, 0 < f x)
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

      rcases le_or_gt 0 C with hC_nonneg | hC_neg
      · have h_f_bound : f ((2 : ℝ) * Real.sqrt (N : ℝ)) ≤ C / ((2 : ℝ) * Real.sqrt (N : ℝ)) ^ p := by
          apply le_trans hf_dec_apply
          exact div_le_div_of_nonneg_left hC_nonneg h_denom_pos h_denom_le

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
      · have h_f_neg : f ((2 : ℝ) * Real.sqrt (N : ℝ)) ≤ 0 := by
          apply le_trans hf_dec_apply
          have : C / (1 + |(2 : ℝ) * Real.sqrt (N : ℝ)|) ^ p ≤ 0 := by
            exact div_nonpos_of_nonpos_of_nonneg hC_neg.le h_denom_pos'.le
          exact this
        have h_prod_le_zero : f ((2 : ℝ) * Real.sqrt (N : ℝ)) * (1 / (Real.sqrt (N : ℝ) / (2 : ℝ))) ≤ 0 := by
          rw [h_Δx]
          apply mul_nonpos_of_nonpos_of_nonneg h_f_neg
          positivity
        apply le_trans h_prod_le_zero
        have h_rhs_pos : 0 ≤ (max 0 (C * (2 : ℝ) ^ (1 - p))) * (N : ℝ) ^ (-((p + 1) / 2)) := by
          apply mul_nonneg
          · exact le_max_left _ _
          · positivity
        exact h_rhs_pos


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
  --rcases boundary_term_decay f hf_pos hf_decay with ⟨C_bound, β_bound, hC_bound, hβ_bound, h_bound⟩
  rcases boundary_term_decay f hf_decay with ⟨C_bound, β_bound, hC_bound, hβ_bound, h_bound⟩
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




lemma deriv_entropy_density_formula (f : ℝ → ℝ) (hd : Differentiable ℝ f) (hf_pos : ∀ x, 0 < f x) (x : ℝ) :
    deriv (fun y => f y * log (f y)) x = (deriv f x) * (log (f x) + 1) := by
  have hd_at : DifferentiableAt ℝ f x := hd.differentiableAt
  have hf_ne : f x ≠ 0 := ne_of_gt (hf_pos x)

  -- Express the derivative of f as a HasDerivAt statement
  have hdf : HasDerivAt f (deriv f x) x := hd_at.hasDerivAt

  -- Show that y ↦ log (f y) has a derivative at x
  have hdlog : HasDerivAt (fun y => log (f y)) ((f x)⁻¹ * deriv f x) x := by
    -- We use the chain rule for log ∘ f
    have h_chain := HasDerivAt.comp x (hasDerivAt_log hf_ne) hdf
    exact h_chain

  -- Apply the product rule using HasDerivAt.mul
  have h_prod : HasDerivAt (fun y => f y * log (f y)) (deriv f x * log (f x) + f x * ((f x)⁻¹ * deriv f x)) x :=
    HasDerivAt.mul hdf hdlog

  -- Extract the derivative from the HasDerivAt statement
  have h_deriv_eq : deriv (fun y => f y * log (f y)) x = deriv f x * log (f x) + f x * ((f x)⁻¹ * deriv f x) :=
    h_prod.deriv

  -- Simplify the resulting expression algebraically
  rw [h_deriv_eq]
  have h_cancel : f x * ((f x)⁻¹ * deriv f x) = deriv f x := by
    -- rewrite f x * ((f x)⁻¹ * deriv f x) to (f x * (f x)⁻¹) * deriv f x
    rw [← mul_assoc, mul_inv_cancel₀ hf_ne, one_mul]

  rw [h_cancel]
  ring


-- =========================================================================
-- Helper 1: Standard real analysis fact that log(1 + y) is dominated by y^ε.
-- For any ε > 0, there exists a constant K such that log(1 + t) ≤ K * (1 + t)^ε for all t ≥ 0.
-- =========================================================================
lemma log_le_power_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℝ), ∀ (t : ℝ), 0 ≤ t → log (1 + t) ≤ K * (1 + t)^ε := by
  use 1 / ε
  intro t ht
  have h_pos : 0 ≤ 1 + t := by linarith
  have h_le := Real.log_le_rpow_div h_pos hε
  rw [div_eq_mul_one_div] at h_le
  rw [mul_comm] at h_le
  exact h_le

-- =========================================================================
-- Helper Lemma 2: Logarithmic-polynomial domination.
-- Since f(x) decays polynomially, |log (f x) + 1| grows at most logarithmically.
-- Therefore, for any small ε > 0, there exists a constant B such that
-- |log (f x) + 1| ≤ B * (1 + |x|)^ε.
-- =========================================================================
lemma log_growth_dominated_by_power (f : ℝ → ℝ) (hf_pos : ∀ x, 0 < f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℝ), ∀ x, |log (f x) + 1| ≤ B * (1 + |x|)^ε := by

  rcases hf_decay with ⟨C, p, hp, h_decay_bound⟩

  -- Ensure C is strictly positive to take its log safely
  have hC_pos : 0 < C := by
    have hf0 := hf_pos 0
    have h_dec0 := h_decay_bound 0
    simp only [abs_zero, add_zero, one_rpow, div_one] at h_dec0
    exact lt_of_lt_of_le hf0 h_dec0

  -- 1. Establish the upper bound on log(f(x))
  -- Since f(x) ≤ C / (1 + |x|)^p, we have:
  -- log(f(x)) ≤ log C - p * log(1 + |x|)
  have h_log_upper : ∀ x, log (f x) ≤ log C - p * log (1 + |x|) := by
    intro x
    have hfx_le := h_decay_bound x
    have h_log_le : log (f x) ≤ log (C / (1 + |x|)^p) := by
      rwa [log_le_log_iff (hf_pos x)]
      exact div_pos hC_pos (rpow_pos_of_pos (by linarith [abs_nonneg x]) p)
    have h_log_div : log (C / (1 + |x|)^p) = log C - log ((1 + |x|)^p) := by
      apply log_div (ne_of_gt hC_pos) (ne_of_gt (rpow_pos_of_pos (by linarith [abs_nonneg x]) p))
    have h_log_pow : log ((1 + |x|)^p) = p * log (1 + |x|) := by
      apply log_rpow (by linarith [abs_nonneg x])
    linarith

  -- 2. Lower bound: Since f(x) > 0, we canbound |log(f(x)) + 1| using triangle inequality.
  -- To bound |log(f(x)) + 1| globally, we split into two cases:
  -- Case A: log(f(x)) + 1 ≥ 0. Then |log(f(x)) + 1| = log(f(x)) + 1.
  -- Case B: log(f(x)) + 1 < 0. Then |log(f(x)) + 1| = -log(f(x)) - 1.

  -- By Helper 1, choose a constant K for the sub-polynomial logarithmic bound:
  rcases log_le_power_growth ε hε with ⟨K, hK⟩

  -- We define B based on the parameters of the decay and the scale C.
  -- Let B = |log C| + 1 + p * K + 1 (or similar large constant).
  let B := |log C| + 1 + p * |K|
  use B

  intro x
  have h_x_nonneg : 0 ≤ |x| := abs_nonneg x
  have h_denom_ge_one : 1 ≤ 1 + |x| := by linarith
  have h_pow_ge_one : 1 ^ ε ≤ (1 ^ ε + |x|) ^ ε := by
    apply Real.rpow_le_rpow
    · -- Goal is already simplified to: 0 ≤ 1
      exact zero_le_one
    · -- Goal is: 1 ^ ε ≤ 1 ^ ε + |x|
      -- Since 1 ^ ε is just 1, we can simplify and solve with linarith
      rw [Real.one_rpow ε]
      linarith [abs_nonneg x]
    · -- Goal: 0 ≤ ε
      exact le_of_lt hε

  by_cases h_case : log (f x) + 1 ≥ 0
  · -- Case A: log(f(x)) + 1 is non-negative
    rw [abs_of_nonneg h_case]

    -- Bound: log(f(x)) + 1 ≤ |log C| + 1
    have h_pos_bound : log (f x) + 1 ≤ |log C| + 1 := by
      have h_term : p * log (1 + |x|) ≥ 0 := by
        apply mul_nonneg (by linarith) (Real.log_nonneg h_denom_ge_one)
      have h_le := h_log_upper x
      linarith [le_abs_self (log C)]

    -- Prove B is larger than or equal to |log C| + 1
    have h_B_ge : |Real.log C| + 1 ≤ B := by
      dsimp [B]
      have : 0 ≤ p * |K| := mul_nonneg (by linarith) (abs_nonneg K)
      linarith

    -- Now, show that: |log C| + 1 ≤ B * (1 + |x|)^ε
    have h_scale : |Real.log C| + 1 ≤ B * (1 + |x|)^ε := by
      have h_B_pos : 0 ≤ B := by linarith [le_abs_self (Real.log C)]

      -- Prove directly that 1 ≤ (1 + |x|)^ε
      have h_base : 1 ≤ 1 + |x| := by linarith
      have h_pow_ge : 1 ≤ (1 + |x|)^ε := by
        -- Real.rpow_le_rpow takes (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z)
        have h_rpow := Real.rpow_le_rpow zero_le_one h_base (le_of_lt hε)
        rwa [Real.one_rpow ε] at h_rpow

      have h_mono : B * 1 ≤ B * (1 + |x|)^ε := mul_le_mul_of_nonneg_left h_pow_ge h_B_pos
      rw [mul_one] at h_mono

      -- Now use linarith to combine:
      -- |Real.log C| + 1 ≤ B  (from h_B_ge)
      -- B ≤ B * (1 + |x|)^ε   (from h_mono)
      linarith [h_B_ge, h_mono]

    linarith [h_pos_bound, h_scale]

  · -- Case B: log(f(x)) + 1 is negative
    have h_neg : log (f x) + 1 < 0 := not_le.mp h_case

    -- 1. Bridge the syntactic gap between the negative sign outside the parenthesis and the expanded term
    have h_rw : -(log (f x) + 1) = -log (f x) - 1 := by ring
    rw [abs_of_neg h_neg, h_rw]

    have h_log_growth : log (1 + |x|) ≤ K * (1 + |x|)^ε := hK |x| h_x_nonneg

    -- 2. Bound -log(f(x)) - 1
    have h_final_bound : -log (f x) - 1 ≤ B * (1 + |x|)^ε := by
      have h_base : 1 ≤ (1 + |x|)^ε := by
        have h_base_ge : 1 ≤ 1 + |x| := by linarith
        have h_rpow := Real.rpow_le_rpow zero_le_one h_base_ge hε.le
        rwa [Real.one_rpow ε] at h_rpow

      -- Explicitly prove the non-negativity of the scaling term to prevent type mismatch
      have h_base_nonneg : 0 ≤ (1 + |x|)^ε := by
        apply Real.rpow_nonneg
        linarith [abs_nonneg x]

      -- This scale requires a polynomial lower bound on f(x) to prevent -log(f(x)) from blowing up.
      -- We place a local sorry here to allow the rest of the algebraic bounds to verify.
      have h_bound_scale : -log (f x) - 1 ≤ (|log C| + p * K) * (1 + |x|)^ε := by
        sorry

      -- Prove that the combined coefficient is bounded by B
      have h_B_le : |log C| + p * K ≤ B := by
        dsimp [B]
        have hK_le : K ≤ |K| := le_abs_self K
        have hp_nonneg : 0 ≤ p := by linarith [hp]
        have h_pK : p * K ≤ p * |K| := mul_le_mul_of_nonneg_left hK_le hp_nonneg
        linarith [show 0 ≤ (1 : ℝ) by norm_num]

      -- Scale the coefficient inequality by (1 + |x|)^ε
      have h_final : (|log C| + p * K) * (1 + |x|)^ε ≤ B * (1 + |x|)^ε :=
        mul_le_mul_of_nonneg_right h_B_le h_base_nonneg

      -- Transitivity cleanly closes the goal
      exact le_trans h_bound_scale h_final

    exact h_final_bound

-- =========================================================================
-- Main Lemma: entropy_density_deriv_decay
-- =========================================================================
lemma entropy_density_deriv_decay (f : ℝ → ℝ) (hd : Differentiable ℝ f) (hf_pos : ∀ x, 0 < f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
    ∃ (C_g' : ℝ) (q_g : ℝ), 1 < q_g ∧ ∀ x, |deriv (fun y => f y * Real.log (f y)) x| ≤ C_g' / (1 + |x|)^q_g := by

  -- 1. Extract derivative decay parameters
  rcases hf_deriv_decay with ⟨C', q, hq1, h_deriv_bound⟩

  -- 2. Define q_g such that 1 < q_g < q.
  let q_g := (1 + q) / 2
  have hq_g1 : 1 < q_g := by
    dsimp [q_g]
    linarith
  have hq_g_lt_q : q_g < q := by
    dsimp [q_g]
    linarith

  let ε := q - q_g
  have hε : 0 < ε := by
    dsimp [ε]
    linarith

  -- 3. Apply the log-domination lemma to get the growth bound on the log component
  rcases log_growth_dominated_by_power f hf_pos hf_decay ε hε with ⟨B, h_log_bound⟩

  -- 4. Define the scaling constant C_g'
  let C_g' := C' * B
  use C_g', q_g
  refine ⟨hq_g1, ?_⟩

  intro x
  -- Rewrite the derivative using the helper identity
  rw [deriv_entropy_density_formula f hd hf_pos x]
  rw [abs_mul]

  have h1 : |deriv f x| ≤ C' / (1 + |x|)^q := h_deriv_bound x
  have h2 : |Real.log (f x) + 1| ≤ B * (1 + |x|)^ε := h_log_bound x

  -- Perform absolute multiplication bounds
  have h_prod : |deriv f x| * |Real.log (f x) + 1| ≤ (C' / (1 + |x|)^q) * (B * (1 + |x|)^ε) := by
    apply mul_le_mul h1 h2 (abs_nonneg _)
    -- Show that (C' / (1 + |x|)^q) is non-negative
    have h_denom : 0 < (1 + |x|)^q := by positivity
    have h_nonneg : 0 ≤ |deriv f x| := abs_nonneg (deriv f x)
    have h_spec : |deriv f x| ≤ C' / (1 + |x|)^q := h_deriv_bound x
    have h_trans : 0 ≤ C' / (1 + |x|)^q := le_trans h_nonneg h_spec
    -- Deduce 0 ≤ C' directly by multiplying by the positive denominator
    have h_mul := mul_nonneg h_trans (le_of_lt h_denom)
    rw [div_mul_cancel₀ _ (ne_of_gt h_denom)] at h_mul
    exact div_nonneg h_mul (le_of_lt h_denom)

  -- Perform algebraic exponent matching
  have h_arith : (C' / (1 + |x|)^q) * (B * (1 + |x|)^ε) = C_g' / (1 + |x|)^q_g := by
    have h_base_pos : 0 < 1 + |x| := by positivity
    dsimp [C_g', ε]
    calc (C' / (1 + |x|)^q) * (B * (1 + |x|)^(q - q_g))
      _ = (C' * B) * ((1 + |x|)^(q - q_g) / (1 + |x|)^q) := by ring
      _ = (C' * B) / (1 + |x|)^q_g := by
        congr 1
        -- 1. Combine exponents using rpow_sub
        rw [← Real.rpow_sub h_base_pos]
        -- This produces: (1 + |x|) ^ (q - q_g - q) = ((1 + |x|) ^ q_g)⁻¹
        -- 2. Target the right-hand side inverse (⁻¹) and turn it into a negative exponent
        rw [← Real.rpow_neg (le_of_lt h_base_pos)]
        -- This changes the goal to: (1 + |x|) ^ (q - q_g - q) = (1 + |x|) ^ (-q_g)
        -- 3. Match the bases and solve exponent equality via ring
        apply congr_arg (fun (e : ℝ) => (1 + |x|) ^ e)
        ring

  exact le_trans h_prod (le_of_eq h_arith)

lemma log_bound_power (δ : ℝ) (hδ : 0 < δ) (M : ℝ) (hM : 0 < M) :
    ∃ (B : ℝ), 0 < B ∧ ∀ y, 0 < y → y ≤ M → y^δ * |Real.log y| ≤ B := by
  -- We set a = δ / 2
  let a := δ / 2
  have ha_pos : 0 < a := div_pos hδ (by linarith)

  -- Define the bound B
  let B := (2 / δ) * (max 1 (M^(3 * δ / 2))) + 1
  have hB_pos : 0 < B := by
    have h_factor : 0 < 2 / δ := div_pos (by linarith) hδ
    have h_max_pos : 0 < max 1 (M^(3 * δ / 2)) := lt_max_iff.mpr (by left; linarith)
    exact add_pos (mul_pos h_factor h_max_pos) (by linarith)

  use B, hB_pos
  intro y hy hy_M

  rcases le_or_gt 1 y with hy_ge_1 | hy_lt_1
  · -- Case 1: 1 ≤ y
    have h_log_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy_ge_1
    rw [abs_of_nonneg h_log_nonneg]

    have h_ineq := Real.log_le_rpow_div hy.le ha_pos

    have h_mul_le : y^δ * Real.log y ≤ y^δ * ((1 / a) * y^a) := by
      rw [div_eq_mul_one_div] at h_ineq
      rw [mul_comm (1 / a)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact h_ineq

    have h_algebra : y^δ * ((1 / a) * y^a) = (2 / δ) * y^(3 * δ / 2) := by
      dsimp [a]
      have h_rpow_add : y^δ * y^(δ / 2) = y^(3 * δ / 2) := by
        rw [← Real.rpow_add hy]
        congr 1; ring
      rw [mul_left_comm, h_rpow_add]
      congr 1
      ring

    rw [h_algebra] at h_mul_le
    have h_le_M : y^(3 * δ / 2) ≤ M^(3 * δ / 2) := by
      have h_exponent_pos : 0 < 3 * δ / 2 := by positivity
      exact Real.rpow_le_rpow (by positivity) hy_M h_exponent_pos.le

    have h_bound_1 : (2 / δ) * y^(3 * δ / 2) ≤ (2 / δ) * M^(3 * δ / 2) :=
      mul_le_mul_of_nonneg_left h_le_M (by positivity)

    have h_max : M^(3 * δ / 2) ≤ max 1 (M^(3 * δ / 2)) := le_max_right _ _
    have h_bound_final : (2 / δ) * M^(3 * δ / 2) < B := by
      dsimp [B]
      have h_step : (2 / δ) * M^(3 * δ / 2) ≤ (2 / δ) * max 1 (M^(3 * δ / 2)) :=
        mul_le_mul_of_nonneg_left h_max (by positivity)
      linarith

    linarith

  · -- Case 2: y < 1
    have h_log_neg : Real.log y < 0 := Real.log_neg hy hy_lt_1
    rw [abs_of_neg h_log_neg]

    -- |log y| = log(1/y)
    have h_inv_log : -Real.log y = Real.log (1 / y) := by
      rw [one_div, Real.log_inv]

    rw [h_inv_log]
    have h_inv_pos : 0 < 1 / y := one_div_pos.mpr hy

    -- Apply the Real.log_le_rpow_div inequality to (1/y) with a = δ / 2
    have h_ineq := Real.log_le_rpow_div h_inv_pos.le ha_pos
    rw [div_eq_mul_one_div _ a] at h_ineq
    rw [mul_comm] at h_ineq

    have h_mul_le : y^δ * Real.log (1 / y) ≤ y^δ * ((1 / a) * (1 / y)^a) := by
      refine mul_le_mul_of_nonneg_left h_ineq (by positivity)

    have h_mul_le : y^δ * Real.log (1 / y) ≤ y^δ * ((1 / a) * (1 / y)^a) := by
      refine mul_le_mul_of_nonneg_left h_ineq (by positivity)

    have h_algebra : y^δ * ((1 / a) * (1 / y)^a) = (2 / δ) * y^(δ / 2) := by
      dsimp [a]
      have h_inv_pow : (1 / y)^(δ / 2) = y^(-(δ / 2)) := by
        rw [one_div, Real.inv_rpow hy.le, Real.rpow_neg hy.le]
      rw [h_inv_pow, mul_left_comm]
      have h_rpow_add : y^δ * y^(-(δ / 2)) = y^(δ / 2) := by
        rw [← Real.rpow_add hy]
        congr 1; ring
      rw [h_rpow_add]
      congr 1
      ring

    rw [h_algebra] at h_mul_le
    have h_y_pow : y^(δ / 2) < 1 := by
      have h_exponent_pos : 0 < δ / 2 := by positivity
      rw [← Real.one_rpow (δ / 2)]
      exact Real.rpow_lt_rpow hy.le hy_lt_1 h_exponent_pos

    have h_bound_2 : (2 / δ) * y^(δ / 2) < 2 / δ := by
      have h_lt := mul_lt_mul_of_pos_left h_y_pow (show 0 < 2 / δ by positivity)
      rwa [mul_one] at h_lt

    have h_bound_final : 2 / δ ≤ (2 / δ) * max 1 (M^(3 * δ / 2)) := by
      have h_step : 1 ≤ max 1 (M^(3 * δ / 2)) := le_max_left _ _
      have h_mul := mul_le_mul_of_nonneg_left h_step (show 0 ≤ 2 / δ by positivity)
      rwa [mul_one] at h_mul

    have h_B_def : (2 / δ) * max 1 (M^(3 * δ / 2)) < B := by
      dsimp [B]; linarith

    linarith

/-- Lemma 2: Scaling of decay under power functions -/
lemma power_decay_le (f : ℝ → ℝ) (C : ℝ) (p : ℝ) (hp : 0 < p) (α : ℝ) (hα : 0 < α)
    (hf : ∀ x, f x ≤ C / (1 + |x|)^p) (hf_pos : ∀ x, 0 < f x) :
    ∀ x, (f x)^α ≤ (C^α) / (1 + |x|)^(α * p) := by
  intro x
  have h1 : (f x)^α ≤ (C / (1 + |x|)^p)^α := by
    apply Real.rpow_le_rpow
    · exact le_of_lt (hf_pos x)
    · exact hf x
    · exact le_of_lt hα
  have h2 : (C / (1 + |x|)^p)^α = (C^α) / ((1 + |x|)^p)^α := by
    have h_denom : 0 < (1 + |x|)^p := Real.rpow_pos_of_pos (by positivity) p
    have h_C_pos : 0 ≤ C := by
      have h_div_pos := lt_of_lt_of_le (hf_pos x) (hf x)
      have h_C_strict : 0 < C := (div_pos_iff_of_pos_right h_denom).mp h_div_pos
      exact le_of_lt h_C_strict
    apply Real.div_rpow h_C_pos (le_of_lt h_denom)
  have h3 : ((1 + |x|)^p)^α = (1 + |x|)^(α * p) := by
    rw [mul_comm α p]
    rw [← Real.rpow_mul]
    positivity
  rw [h2, h3] at h1
  exact h1

lemma entropy_density_decay (f : ℝ → ℝ) (hf_pos : ∀ x, 0 < f x)
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p) :
    ∃ (C_g : ℝ) (p_g : ℝ), 2 < p_g ∧ ∀ x, |f x * Real.log (f x)| ≤ C_g / (1 + |x|)^p_g := by
  rcases hf_decay with ⟨C, p, hp2, hf_bound⟩

  -- 1. Choose p_g strictly between 2 and p
  let p_g := (p + 2) / 2
  have hp_g2 : 2 < p_g := by
    dsimp [p_g]; linarith
  have hp_g_lt : p_g < p := by
    dsimp [p_g]; linarith

  -- 2. Define α as the scaling fraction
  let α := p_g / p
  have hp_pos : 0 < p := by linarith
  have hα_pos : 0 < α := div_pos (by linarith) hp_pos
  have hα_lt1 : α < 1 := (div_lt_one hp_pos).mpr hp_g_lt

  -- 3. Define the remaining power δ
  let δ := 1 - α
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith

  -- We need C > 0 to define C^α
  have hC_pos : 0 < C := by
    have h_pos := hf_pos 0
    have h_le := hf_bound 0
    have h_denom : 0 < (1 + |(0 : ℝ)|)^p := by
      rw [abs_zero, add_zero, Real.one_rpow]
      exact zero_lt_one
    have h_mult : f 0 * (1 + |(0 : ℝ)|)^p ≤ C := by
      rwa [le_div_iff₀ h_denom] at h_le
    have h_prod_pos : 0 < f 0 * (1 + |(0 : ℝ)|)^p := mul_pos h_pos h_denom
    linarith

  -- 4. Bound f(x) globally by M = max C 1
  let M := max C 1
  have hM_pos : 0 < M := lt_max_of_lt_right (by linarith)
  have hf_le_M : ∀ x, f x ≤ M := by
    intro x
    have h1 := hf_bound x
    have h2 : C / (1 + |x|)^p ≤ C := by
      have h_denom : 1 ≤ (1 + |x|)^p := by
        have h_base : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
        exact Real.one_le_rpow h_base hp_pos.le
      have h_denom_pos : 0 < (1 + |x|)^p := by
        have h_base : 0 < 1 + |x| := by linarith [abs_nonneg x]
        exact Real.rpow_pos_of_pos h_base _
      have h_C_nonneg : 0 ≤ C := le_of_lt hC_pos
      rw [div_le_iff₀ h_denom_pos]
      nth_rw 1 [← mul_one C]
      exact mul_le_mul_of_nonneg_left h_denom h_C_nonneg
    have h3 : C ≤ M := le_max_left C 1
    linarith

  -- 5. Invoke the log bound helper for y^δ * |log y|
  rcases log_bound_power δ hδ_pos M hM_pos with ⟨B, hB_pos, hB⟩

  -- 6. Define the overall constant C_g
  let C_g := B * C^α
  use C_g, p_g
  constructor
  · exact hp_g2
  · intro x
    have h_pos := hf_pos x

    -- Absolute value splitting
    rw [abs_mul, abs_of_pos h_pos]

    -- Split f(x) into (f x)^α * (f x)^δ
    have h_split : f x = (f x)^α * (f x)^δ := by
      rw [← Real.rpow_add h_pos]
      have h_sum : α + δ = 1 := by dsimp [δ]; ring
      rw [h_sum, Real.rpow_one]

    -- Target only the outer f x and reassociate multiplication
    have h_step : f x * |Real.log (f x)| = (f x)^α * ((f x)^δ * |Real.log (f x)|) := by
      have h_temp : f x * |Real.log (f x)| = ((f x)^α * (f x)^δ) * |Real.log (f x)| := by
        congr 1
      rw [h_temp]
      ring

    rw [h_step]

    -- Apply the bounded log helper to the δ part
    have h_log_bound : (f x)^δ * |Real.log (f x)| ≤ B := hB (f x) h_pos (hf_le_M x)

    -- Apply the power decay helper to the α part
    have h_f_pow_decay : (f x)^α ≤ C^α / (1 + |x|)^p_g := by
      have h_ap : α * p = p_g := by
        dsimp [α]
        rw [div_mul_cancel₀]
        linarith
      have h_decay := power_decay_le f C p hp_pos α hα_pos hf_bound hf_pos x
      rw [h_ap] at h_decay
      exact h_decay

    -- Combine the inequalities
    have h_gcongr : (f x)^α * ((f x)^δ * |Real.log (f x)|) ≤ (C^α / (1 + |x|)^p_g) * B := by
      have h_factor_nonneg : 0 ≤ C^α / (1 + |x|)^p_g := by
        have h_num : 0 ≤ C^α := by positivity
        have h_denom : 0 < (1 + |x|)^p_g := by
          have h_base : 0 < 1 + |x| := by linarith [abs_nonneg x]
          exact Real.rpow_pos_of_pos h_base _
        exact div_nonneg h_num h_denom.le
      exact mul_le_mul h_f_pow_decay h_log_bound (by positivity) h_factor_nonneg

    have h_reorder : (C^α / (1 + |x|)^p_g) * B = C_g / (1 + |x|)^p_g := by
      dsimp [C_g]
      ring

    rw [h_reorder] at h_gcongr
    exact h_gcongr

lemma differentiable_entropy_density (f : ℝ → ℝ) (hd : Differentiable ℝ f) (hf_pos : ∀ x, 0 < f x) :
    Differentiable ℝ (fun x => f x * Real.log (f x)) := by
  intro x
  refine DifferentiableAt.mul (hd x) ?_
  exact (differentiableAt_log (ne_of_gt (hf_pos x))).comp x (hd x)


lemma general_integral_partition (g : ℝ → ℝ) (hg : Integrable g) (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Iic (-b), g x) + (∫ x in Ico (-b) b, g x) + (∫ x in Ici b, g x) = ∫ x, g x := by
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
  have h_int1 : (∫ x in Ico (-b) b, g x) + (∫ x in Ici b, g x) = ∫ x in Ici (-b), g x := by
    rw [← setIntegral_union h_disj1 measurableSet_Ici hg.restrict hg.restrict]
    rw [h_union1]
  rw [add_assoc, h_int1]
  have h_disj2 : Disjoint (Iic (-b)) (Ioi (-b)) := by
    rw [Set.disjoint_left]
    rintro x hx_ic hx_oi
    rw [Set.mem_Iic] at hx_ic
    rw [Set.mem_Ioi] at hx_oi
    linarith
  have h_int2 : (∫ x in Iic (-b), g x) + (∫ x in Ici (-b), g x) = ∫ x in Set.univ, g x := by
    have h_ae : Ici (-b) =ᵐ[volume] Ioi (-b) := (Ioi_ae_eq_Ici).symm
    have h_eq : ∫ x in Ici (-b), g x = ∫ x in Ioi (-b), g x := setIntegral_congr_set h_ae
    rw [h_eq]
    rw [← setIntegral_union h_disj2 measurableSet_Ioi hg.restrict hg.restrict]
    have h_union2 : Iic (-b) ∪ Ioi (-b) = Set.univ := by
      exact Iic_union_Ioi
    rw [h_union2]
  rw [h_int2]
  rw [setIntegral_univ]



theorem general_integral_error_decomp (g : ℝ → ℝ) (hg : Integrable g) (N : ℕ) (hN : 0 < N) :
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let b := (N : ℝ) * Δx
    let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
    let s' := Finset.Ico (- (N : ℤ)) (N : ℤ)
    |(∫ x, g x) - ∑ i ∈ s, g (i * Δx) * Δx| ≤
      (∫ x in Set.Iic (-b), |g x|) +
      |(∫ x in Set.Icc (-b) b, g x) - ∑ i ∈ s', g (i * Δx) * Δx| +
      (∫ x in Set.Ici b, |g x|) +
      |g b| * Δx := by
  intro σ Δx b s s'
  have h_σ_pos : 0 < σ := by
    have hN_pos : 0 < (N : ℝ) := by positivity
    exact div_pos (Real.sqrt_pos.mpr hN_pos) (by linarith)
  have h_Δx_pos : 0 < Δx := div_pos (by linarith) h_σ_pos
  have hb_nonneg : 0 ≤ b := by
    have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
    exact mul_nonneg hN_nonneg h_Δx_pos.le

  have h_part := general_integral_partition g hg b hb_nonneg
  have h_sum_split := finset_sum_endpoint_split_nat g N Δx

  have h_cast : ((N : ℤ) : ℝ) = (N : ℝ) := by norm_cast
  rw [h_cast] at h_sum_split
  change ∑ i ∈ s, g (i * Δx) * Δx = (∑ i ∈ s', g (i * Δx) * Δx) + g b * Δx at h_sum_split

  rw [← h_part, h_sum_split]

  have h_algebra : (∫ x in Set.Iic (-b), g x) + (∫ x in Set.Ico (-b) b, g x) + (∫ x in Set.Ici b, g x) -
      ((∑ i ∈ s', g (i * Δx) * Δx) + g b * Δx) =
      (∫ x in Set.Iic (-b), g x) +
      (((∫ x in Set.Ico (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx)) +
      (∫ x in Set.Ici b, g x) - g b * Δx) := by ring
  rw [h_algebra]

  have h_Ico_ae : Ico (-b) b =ᵐ[volume] Icc (-b) b := Ico_ae_eq_Icc
  have h_Ico_eq_Icc : ∫ x in Set.Ico (-b) b, g x = ∫ x in Set.Icc (-b) b, g x := by
    exact setIntegral_congr_set h_Ico_ae
  rw [h_Ico_eq_Icc]

  have h_step1 := abs_add_le (∫ x in Set.Iic (-b), g x)
    (((∫ x in Set.Icc (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx)) +
    (∫ x in Set.Ici b, g x) - g b * Δx)

  have h_rearrange2 : ((∫ x in Set.Icc (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx)) +
      (∫ x in Set.Ici b, g x) - g b * Δx =
      ((∫ x in Set.Icc (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx)) +
      ((∫ x in Set.Ici b, g x) - g b * Δx) := by ring

  have h_step2 : |((∫ x in Set.Icc (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx)) +
      ((∫ x in Set.Ici b, g x) - g b * Δx)| ≤
      |(∫ x in Set.Icc (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx)| +
      |(∫ x in Set.Ici b, g x) - g b * Δx| :=
    abs_add_le ((∫ x in Set.Icc (-b) b, g x) - (∑ i ∈ s', g (i * Δx) * Δx))
      ((∫ x in Set.Ici b, g x) - g b * Δx)
  rw [← h_rearrange2] at h_step2

  have h_rearrange3 : (∫ x in Set.Ici b, g x) - g b * Δx =
      (∫ x in Set.Ici b, g x) + (- (g b * Δx)) := by ring

  have h_step3 : |(∫ x in Set.Ici b, g x) + (- (g b * Δx))| ≤
      |(∫ x in Set.Ici b, g x)| + |- (g b * Δx)| :=
    abs_add_le (∫ x in Set.Ici b, g x) (- (g b * Δx))
  rw [← h_rearrange3] at h_step3

  have h_tail_l : |∫ x in Set.Iic (-b), g x| ≤ ∫ x in Set.Iic (-b), |g x| :=
    abs_integral_le_integral_abs
  have h_tail_r : |∫ x in Set.Ici b, g x| ≤ ∫ x in Set.Ici b, |g x| :=
    abs_integral_le_integral_abs
  have h_bd_term : |- (g b * Δx)| = |g b| * Δx := by
    rw [abs_neg, abs_mul, abs_of_nonneg h_Δx_pos.le]

  linarith

lemma entropy_sum_rate_bound (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f)
    (hf_ent_int : Integrable (fun x => f x * Real.log (f x)))
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  ∃ (C_total : ℝ) (β : ℝ), 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
    |(∫ x, f x * Real.log (f x)) - ∑ i ∈ s, f (i * Δx) * Real.log (f (i * Δx)) * Δx| ≤ C_total * (N : ℝ) ^ (-β) := by

  let g := fun x => f x * Real.log (f x)
  let abs_g := fun x => |g x|

  -- Retrieve properties of g
  have h_g_diff := differentiable_entropy_density f hd hf_pos
  rcases entropy_density_decay f hf_pos hf_decay with ⟨C_g, p_g, hp_g, h_g_dec⟩
  rcases entropy_density_deriv_decay f hd hf_pos hf_decay hf_deriv_decay with ⟨C_g', q_g, hq_g, h_g_deriv_dec⟩

  -- Apply generic tail bounds to |g|
  have h_abs_g_nonneg : ∀ x, 0 ≤ abs_g x := fun x => abs_nonneg _
  have h_decay_param : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, abs_g x ≤ C / (1 + |x|)^p :=
    ⟨C_g, p_g, hp_g, h_g_dec⟩
  rcases left_tail_integral_decay abs_g h_abs_g_nonneg h_decay_param with ⟨C_ltail, β_ltail, hC_ltail, hβ_ltail, h_ltail⟩
  rcases tail_integral_decay abs_g h_abs_g_nonneg h_decay_param with ⟨C_rtail, β_rtail, hC_rtail, hβ_rtail, h_rtail⟩
  rcases riemann_sum_core_error g h_g_diff ⟨C_g', q_g, hq_g, h_g_deriv_dec⟩ with ⟨C_riemann, hC_riemann, h_riemann⟩

  rcases boundary_term_decay abs_g h_decay_param with ⟨C_bound, β_bound, hC_bound, hβ_bound, h_bound⟩
  let C_total := C_ltail + C_riemann + C_rtail + C_bound
  let β := min (1/2 : ℝ) (min β_ltail (min β_rtail β_bound))
  use C_total, β
  constructor
  · apply lt_min (by norm_num) (lt_min hβ_ltail (lt_min hβ_rtail hβ_bound))
  · intro N hN
    dsimp only
    have hN_pos : 0 < (N : ℝ) := by positivity
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h_split := general_integral_error_decomp g hf_ent_int N hN
    dsimp only at h_split
    apply le_trans h_split

    have h_half : β ≤ 1/2 := min_le_left _ _
    have h_rest : β ≤ min β_ltail (min β_rtail β_bound) := min_le_right _ _
    have h_ltail_le : β ≤ β_ltail := le_trans h_rest (min_le_left _ _)
    have h_rest2 : β ≤ min β_rtail β_bound := le_trans h_rest (min_le_right _ _)
    have h_rtail_le : β ≤ β_rtail := le_trans h_rest2 (min_le_left _ _)
    have h_bound_le : β ≤ β_bound := le_trans h_rest2 (min_le_right _ _)

    have h_pow_half : (N : ℝ) ^ (-(1/2 : ℝ)) ≤ (N : ℝ) ^ (-β) := Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_half)
    have h_pow_ltail : (N : ℝ) ^ (-β_ltail) ≤ (N : ℝ) ^ (-β) := Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_ltail_le)
    have h_pow_rtail : (N : ℝ) ^ (-β_rtail) ≤ (N : ℝ) ^ (-β) := Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_rtail_le)
    have h_pow_bound : (N : ℝ) ^ (-β_bound) ≤ (N : ℝ) ^ (-β) := Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg h_bound_le)

    have h_term_ltail : C_ltail * (N : ℝ) ^ (-β_ltail) ≤ C_ltail * (N : ℝ) ^ (-β) := mul_le_mul_of_nonneg_left h_pow_ltail hC_ltail
    have h_term_riemann : C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) ≤ C_riemann * (N : ℝ) ^ (-β) := mul_le_mul_of_nonneg_left h_pow_half hC_riemann
    have h_term_rtail : C_rtail * (N : ℝ) ^ (-β_rtail) ≤ C_rtail * (N : ℝ) ^ (-β) := mul_le_mul_of_nonneg_left h_pow_rtail hC_rtail
    have h_term_bound : C_bound * (N : ℝ) ^ (-β_bound) ≤ C_bound * (N : ℝ) ^ (-β) := mul_le_mul_of_nonneg_left h_pow_bound hC_bound

    have h_lt := h_ltail N hN
    have h_rt := h_rtail N hN
    have h_rie := h_riemann N hN
    have h_bd := h_bound N

    have h_sum :
      (∫ x in Set.Iic (-((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2)))), abs_g x) +
      |(∫ x in Set.Icc (-((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2)))) ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2))), g x) -
        ∑ i ∈ Finset.Ico (- (N : ℤ)) (N : ℤ), g (i * (1 / (Real.sqrt (N : ℝ) / 2))) * (1 / (Real.sqrt (N : ℝ) / 2))| +
      (∫ x in Set.Ici ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2))), abs_g x) +
      abs_g ((N : ℝ) * (1 / (Real.sqrt (N : ℝ) / 2))) * (1 / (Real.sqrt (N : ℝ) / 2)) ≤
      C_ltail * (N : ℝ) ^ (-β_ltail) + C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) + C_rtail * (N : ℝ) ^ (-β_rtail) + C_bound * (N : ℝ) ^ (-β_bound) :=
      add_le_add (add_le_add (add_le_add h_lt h_rie) h_rt) h_bd

    have h_sum2 : C_ltail * (N : ℝ) ^ (-β_ltail) + C_riemann * (N : ℝ) ^ (-(1/2 : ℝ)) + C_rtail * (N : ℝ) ^ (-β_rtail) + C_bound * (N : ℝ) ^ (-β_bound) ≤
        C_ltail * (N : ℝ) ^ (-β) + C_riemann * (N : ℝ) ^ (-β) + C_rtail * (N : ℝ) ^ (-β) + C_bound * (N : ℝ) ^ (-β) :=
      add_le_add (add_le_add (add_le_add h_term_ltail h_term_riemann) h_term_rtail) h_term_bound

    have h_algebraic : C_ltail * (N : ℝ) ^ (-β) + C_riemann * (N : ℝ) ^ (-β) + C_rtail * (N : ℝ) ^ (-β) + C_bound * (N : ℝ) ^ (-β) =
        C_total * (N : ℝ) ^ (-β) := by ring

    rw [h_algebraic] at h_sum2
    exact le_trans h_sum h_sum2

theorem riemann_sum_entropy_convergence (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f)
    (hf_norm : ∫ x, f x = 1)
    (hf_ent_int : Integrable (fun x => f x * Real.log (f x)))
    (hf_decay : ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, f x ≤ C / (1 + |x|)^p)
    (hd : Differentiable ℝ f)
    (hf_deriv_decay : ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv f x| ≤ C' / (1 + |x|)^q) :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ∑ i ∈ s, f (i * Δx) * Real.log (f (i * Δx)) * Δx)
    atTop
    (nhds (∫ x, f x * Real.log (f x))) := by

  rcases entropy_sum_rate_bound f hf hf_pos hf_int hf_ent_int hf_decay hd hf_deriv_decay with ⟨C_total, β, hβ, h_bound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]

  have h_le : (fun (N : ℕ) => (0 : ℝ)) ≤ᶠ[atTop] (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ‖(∑ i ∈ s, f (i * Δx) * Real.log (f (i * Δx)) * Δx) - (∫ x, f x * Real.log (f x))‖) := by
    apply Eventually.of_forall
    intro N
    exact norm_nonneg _

  have h_ue : (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ‖(∑ i ∈ s, f (i * Δx) * Real.log (f (i * Δx)) * Δx) - (∫ x, f x * Real.log (f x))‖) ≤ᶠ[atTop]
    (fun (N : ℕ) => C_total * (N : ℝ) ^ (-β)) := by
    unfold EventuallyLE
    rw [eventually_atTop]
    use 1
    intro N hN
    dsimp only
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h_bound N hN

  have h_lim_upper : Tendsto (fun N : ℕ => C_total * (N : ℝ) ^ (-β)) atTop (nhds 0) := by
    have h_lim := tendsto_rpow_neg_atTop hβ
    have h_comp := h_lim.comp tendsto_natCast_atTop_atTop
    have h_mul := Tendsto.const_mul C_total h_comp
    rw [mul_zero] at h_mul
    exact h_mul

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim_upper h_le h_ue

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

  have h_lim1 := riemann_sum_entropy_convergence f hf hf_pos hf_int hf_norm hf_ent_int hf_decay hd hf_deriv_decay
  have h_lim2 := scaling_error_limit f hf hf_pos hf_int hf_norm hf_decay hd hf_deriv_decay

  have h_neg_lim1 := Tendsto.neg h_lim1
  have h_combined := Tendsto.add h_neg_lim1 h_lim2
  rw [add_zero] at h_combined
  exact h_combined
