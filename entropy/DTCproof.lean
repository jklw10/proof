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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Basic
import entropy.GaussianBase
import entropy.GaussianEntropy
import entropy.GaussianDecay

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

lemma hasDerivAt_one_add_x_pow (p : ℝ) (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun y => (1 + y)^(1 - p)) ((1 - p) * (1 + x)^(-p)) x := by
  have h_pos : 0 < 1 + x := by linarith
  have h_inner : HasDerivAt (fun y => 1 + y) 1 x := by
    simpa using hasDerivAt_id' x |>.const_add 1
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

  have h_lower : ∀ᶠ x : ℝ in atTop, 0 ≤ (1 + x)^(1 - p) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have : 0 ≤ 1 + x := by linarith
    exact Real.rpow_nonneg this _

  have h_upper : ∀ᶠ x : ℝ in atTop, (1 + x)^(1 - p) ≤ x^(1 - p) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h_pos_x : 0 < x := by linarith
    have h_pos_one_add : 0 < 1 + x := by linarith
    rw [h_neg_eq, Real.rpow_neg h_pos_one_add.le, Real.rpow_neg h_pos_x.le]
    gcongr
    linarith

  have h_lim_base : Tendsto (fun x : ℝ => x^(1 - p)) atTop (nhds 0) := by
    rw [h_neg_eq]
    exact tendsto_rpow_neg_atTop hp_pos

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    h_lim_base
    h_lower
    h_upper


lemma setIntegral_eq_tendsto_intervalIntegral {f : ℝ → ℝ} (b : ℝ) (hf : IntegrableOn f (Ici b)) :
    Tendsto (fun t => ∫ x in b..t, f x) atTop (nhds (∫ x in Ici b, f x)) := by
  have h_union : (⋃ t : ℝ, Ioc b t) = Ioi b := by
    ext x
    simp only [mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨t, hbx, _⟩; exact hbx
    · intro hx
      have h_lt : x < x + 1 := by linarith
      exact ⟨x + 1, hx, h_lt.le⟩

  have h_set_lim : Tendsto (fun t => ∫ x in Ioc b t, f x) atTop (nhds (∫ x in Ioi b, f x)) := by
    have h_mono : Monotone (fun t : ℝ => Ioc b t) := by
      intro t₁ t₂ h_le
      exact Ioc_subset_Ioc_right h_le
    have h_meas : ∀ t, MeasurableSet (Ioc b t) := fun _ => measurableSet_Ioc
    have h_union_eq : (⋃ t, Ioc b t) = Ioi b := h_union
    have hfi : IntegrableOn f (⋃ t, Ioc b t) := by
      rw [h_union_eq]
      exact hf.mono_set Ioi_subset_Ici_self

    have h_tendsto := tendsto_setIntegral_of_monotone h_meas h_mono hfi
    rwa [h_union_eq] at h_tendsto

  have h_eq : (fun t => ∫ x in b..t, f x) =ᶠ[atTop] (fun t => ∫ x in Ioc b t, f x) := by
    filter_upwards [eventually_ge_atTop b] with t ht
    rw [intervalIntegral.integral_of_le ht]

  have h_integral_eq : (∫ x in Ici b, f x) = ∫ x in Ioi b, f x := by
    have h_ae : Ici b =ᵐ[volume] Ioi b := by
      simp only [ae_eq_set]
      constructor
      · have h_diff1 : (Ici b \ Ioi b) = {b} := by
          ext x
          simp only [mem_diff, Set.mem_Ici, Set.mem_Ioi, mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩; linarith
          · rintro rfl; exact ⟨by linarith, by linarith⟩
        rw [h_diff1]
        exact volume_singleton
      · have h_diff2 : (Ioi b \ Ici b) = ∅ := by
          ext x
          simp only [mem_diff, Set.mem_Ioi, Set.mem_Ici, mem_empty_iff_false, iff_false]
          rintro ⟨h1, h2⟩; linarith
        rw [h_diff2]
        exact measure_empty

    exact setIntegral_congr_set h_ae

  rw [tendsto_congr' h_eq, h_integral_eq]
  exact h_set_lim


lemma setIntegral_one_add_x_rpow_neg (p : ℝ) (hp : 2 < p) (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Ici b, (1 + x)^(-p)) = (1 + b)^(1 - p) / (p - 1) := by
  have hp_sub_pos : 0 < p - 1 := by linarith
  have h_neg : 1 - p < 0 := by linarith
  have hp1 : p ≠ 1 := by linarith

  let F : ℝ → ℝ := fun x => - ((1 + x)^(1 - p) / (p - 1))

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

  have h_lim : Tendsto F atTop (nhds 0) := by
    have h_pow_lim := tendsto_one_add_x_pow_neg p hp
    have h_div := Tendsto.div_const h_pow_lim (p - 1)
    have h_neg_lim := h_div.neg
    simp only [neg_zero, zero_div] at h_neg_lim
    exact h_neg_lim

  have h_integrable : IntegrableOn (fun x => (1 + x)^(-p)) (Ici b) := by
    have h_lt : -p < -1 := by linarith
    have h_pos : -(1 : ℝ) < b := by linarith
    have h_int_ioi : IntegrableOn (fun x => (x + 1)^(-p)) (Ioi b) :=
      integrableOn_add_rpow_Ioi_of_lt h_lt h_pos
    have h_eq : (fun (x : ℝ) => (1 + x)^(-p)) = (fun (x : ℝ) => (x + 1)^(-p)) := by
      ext x; rw [add_comm]
    rw [h_eq]
    have h_ae : Set.Ici b =ᵐ[volume] Set.Ioi b := Ioi_ae_eq_Ici.symm
    rw [IntegrableOn, Measure.restrict_congr_set h_ae]
    exact h_int_ioi

  have h_int_limit : Tendsto (fun t => ∫ x in b..t, (1 + x)^(-p)) atTop (nhds (0 - F b)) := by
    apply Tendsto.congr' (f₁ := fun t => F t - F b)
    · filter_upwards [eventually_ge_atTop b] with t ht
      have h_subset : uIcc b t ⊆ Ici b := by
        rw [uIcc_of_le ht]
        exact Icc_subset_Ici_self
      have h_deriv_sub : ∀ y ∈ uIcc b t, HasDerivAt F ((1 + y)^(-p)) y := by
        intro y hy
        exact h_deriv y (h_subset hy)
      have h_int_integ : IntervalIntegrable (fun x => (1 + x)^(-p)) volume b t :=
        IntegrableOn.intervalIntegrable (h_integrable.mono_set h_subset)
      exact Eq.symm (intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv_sub h_int_integ)
    · exact h_lim.sub_const (F b)

  have h_final_lim : Tendsto (fun t => ∫ x in b..t, (1 + x)^(-p)) atTop (𝓝 (∫ x in Ici b, (1 + x)^(-p))) :=
    setIntegral_eq_tendsto_intervalIntegral b h_integrable

  have h_val : ∫ x in Ici b, (1 + x)^(-p) = 0 - F b := by
    exact tendsto_nhds_unique h_final_lim h_int_limit

  rw [h_val]
  dsimp [F]
  ring


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
  · have h_decay_int : IntegrableOn (fun x => C / (1 + x)^p) (Set.Ici b) := by
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
  · have h_nonneg : ∀ x ∈ Set.Ici b, 0 ≤ C / (1 + x)^p := by
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

    exact le_trans h_abs_le (le_trans h_int_le (le_of_eq h_int_const))


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

  have h_range : ((N : ℤ) - - (N : ℤ)).toNat = 2 * N := by omega
  have h_ico : Finset.Ico (- (N : ℤ)) (N : ℤ) =
      Finset.map (Nat.castEmbedding.trans (addLeftEmbedding (- (N : ℤ)))) (Finset.range (2 * N)) := by
    rw [Int.Ico_eq_finset_map, h_range]

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

  have h_int' : ∀ k < 2 * N, IntervalIntegrable g MeasureTheory.volume (seq k) (seq (k + 1)) := by
    intro k hk
    have hk_eq : seq (k + 1) = (- (N : ℝ) + (k + 1)) * Δx := by
      dsimp [seq]
      push_cast
      ring
    rw [hk_eq]
    exact h_int k (Finset.mem_range.mpr hk)

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
    hd.continuous.intervalIntegrable (i * Δx) ((i + 1) * Δx) |>.sub intervalIntegrable_const

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
      · exact hd.continuous.intervalIntegrable (i * Δx) ((i + 1) * Δx)
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


lemma boundary_term_decay (f : ℝ → ℝ)
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
          intro h
          linarith
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

lemma integral_partition_of_one (f : ℝ → ℝ) (hf_integrable : Integrable f) (hf_norm : ∫ x, f x = 1) (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Iic (-b), f x) + (∫ x in Ico (-b) b, f x) + (∫ x in Ici b, f x) = 1 := by
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

  rw [add_assoc, h_int1]
  have h_disj2 : Disjoint (Iic (-b)) (Ioi (-b)) := by
    rw [Set.disjoint_left]
    rintro x hx_ic hx_oi
    rw [Set.mem_Iic] at hx_ic
    rw [Set.mem_Ioi] at hx_oi
    linarith

  have h_int2 : (∫ x in Iic (-b), f x) + (∫ x in Ici (-b), f x) = ∫ x in Set.univ, f x := by
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

  have h_ne_zero : ∫ x, f x ≠ 0 := by
    rw [hf_norm]
    norm_num
  have hf_int : Integrable f := MeasureTheory.Integrable.of_integral_ne_zero h_ne_zero

  have h_σ_pos : 0 < σ := by
    have hN_pos : 0 < (N : ℝ) := by positivity
    exact div_pos (Real.sqrt_pos.mpr hN_pos) (by linarith)
  have h_Δx_pos : 0 < Δx := div_pos (by linarith) h_σ_pos
  have hb_nonneg : 0 ≤ b := by
    have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
    exact mul_nonneg hN_nonneg h_Δx_pos.le

  have h_part := integral_partition_of_one f hf_int hf_norm b hb_nonneg
  have h_sum_split := finset_sum_endpoint_split_nat f N Δx

  have h_cast : ((N : ℤ) : ℝ) = (N : ℝ) := by norm_cast
  rw [h_cast] at h_sum_split
  change ∑ i ∈ s, f (i * Δx) * Δx = (∑ i ∈ s', f (i * Δx) * Δx) + f b * Δx at h_sum_split

  rw [← h_part, h_sum_split]

  have h_algebra : (∫ x in Set.Iic (-b), f x) + (∫ x in Set.Ico (-b) b, f x) + (∫ x in Set.Ici b, f x) -
      ((∑ i ∈ s', f (i * Δx) * Δx) + f b * Δx) =
      (∫ x in Set.Iic (-b), f x) +
      (((∫ x in Set.Ico (-b) b, f x) - (∑ i ∈ s', f (i * Δx) * Δx)) +
      (∫ x in Set.Ici b, f x) - f b * Δx) := by ring
  rw [h_algebra]

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

  have h_abs_Iic : |∫ x in Set.Iic (-b), f x| = ∫ x in Set.Iic (-b), f x :=
    abs_of_nonneg h_nonneg_Iic

  have h_abs_Ici : |∫ x in Set.Ici b, f x| = ∫ x in Set.Ici b, f x :=
    abs_of_nonneg h_nonneg_Ici

  have h_abs_neg_bound : |- (f b * Δx)| = f b * Δx := by
    rw [abs_neg, abs_of_nonneg h_nonneg_bound]

  have h_Ico_ae : Ico (-b) b =ᵐ[volume] Icc (-b) b := by
    exact Ico_ae_eq_Icc
  have h_Ico_eq_Icc : ∫ x in Set.Ico (-b) b, f x = ∫ x in Set.Icc (-b) b, f x := by
    exact setIntegral_congr_set h_Ico_ae
  rw [h_Ico_eq_Icc]

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
-- PART 5: Analytical Limit and Derivation Helpers
-- =========================================================================

lemma deriv_entropy_density_formula (f : ℝ → ℝ) (hd : Differentiable ℝ f) (hf_pos : ∀ x, 0 < f x) (x : ℝ) :
    deriv (fun y => f y * log (f y)) x = (deriv f x) * (log (f x) + 1) := by
  have hd_at : DifferentiableAt ℝ f x := hd.differentiableAt
  have hf_ne : f x ≠ 0 := ne_of_gt (hf_pos x)

  have hdf : HasDerivAt f (deriv f x) x := hd_at.hasDerivAt

  have hdlog : HasDerivAt (fun y => log (f y)) ((f x)⁻¹ * deriv f x) x := by
    have h_chain := HasDerivAt.comp x (hasDerivAt_log hf_ne) hdf
    exact h_chain

  have h_prod : HasDerivAt (fun y => f y * log (f y)) (deriv f x * log (f x) + f x * ((f x)⁻¹ * deriv f x)) x :=
    HasDerivAt.mul hdf hdlog

  have h_deriv_eq : deriv (fun y => f y * log (f y)) x = deriv f x * log (f x) + f x * ((f x)⁻¹ * deriv f x) :=
    h_prod.deriv

  rw [h_deriv_eq]
  have h_cancel : f x * ((f x)⁻¹ * deriv f x) = deriv f x := by
    rw [← mul_assoc, mul_inv_cancel₀ hf_ne, one_mul]

  rw [h_cancel]
  ring



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


-- =========================================================================
-- PART 6: Emerging Entropy Core Decay and Squeeze Core (Proven)
-- =========================================================================

/-- Specialized Gaussian Rate Bound: Bounds error of Gaussian entropy Riemann sum. -/
theorem gaussian_entropy_sum_rate_bound :
  ∃ (C_total : ℝ) (β : ℝ), 0 < β ∧ ∀ (N : ℕ), 0 < N →
    let σ := Real.sqrt (N : ℝ) / 2
    let Δx := 1 / σ
    let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
    |(∫ x, standard_normal_pdf x * Real.log (standard_normal_pdf x)) -
     ∑ i ∈ s, standard_normal_pdf (i * Δx) * Real.log (standard_normal_pdf (i * Δx)) * Δx| ≤ C_total * (N : ℝ) ^ (-β) := by

  let f := standard_normal_pdf
  let g := fun x => f x * Real.log (f x)
  let abs_g := fun x => |g x|

  have h_g_diff : Differentiable ℝ g := differentiable_entropy_density f standard_normal_differentiable standard_normal_pos
  rcases gaussian_entropy_density_decay with ⟨C_g, p_g, hp_g, h_g_dec⟩
  rcases gaussian_entropy_density_deriv_decay with ⟨C_g', q_g, hq_g, h_g_deriv_dec⟩

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
    have h_split := general_integral_error_decomp g integrable_standard_normal_entropy N hN
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


/-- Specialized Gaussian Riemann Sum Convergence: Continuous Gaussian entropy converges. -/
theorem gaussian_riemann_sum_entropy_convergence :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ∑ i ∈ s, standard_normal_pdf (i * Δx) * Real.log (standard_normal_pdf (i * Δx)) * Δx)
    atTop
    (nhds (∫ x, standard_normal_pdf x * Real.log (standard_normal_pdf x))) := by

  rcases gaussian_entropy_sum_rate_bound with ⟨C_total, β, hβ, h_bound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]

  have h_le : (fun (N : ℕ) => (0 : ℝ)) ≤ᶠ[atTop] (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ‖(∑ i ∈ s, standard_normal_pdf (i * Δx) * Real.log (standard_normal_pdf (i * Δx)) * Δx) - (∫ x, standard_normal_pdf x * Real.log (standard_normal_pdf x))‖) := by
    apply Eventually.of_forall
    intro N
    exact norm_nonneg _

  have h_ue : (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      ‖(∑ i ∈ s, standard_normal_pdf (i * Δx) * Real.log (standard_normal_pdf (i * Δx)) * Δx) - (∫ x, standard_normal_pdf x * Real.log (standard_normal_pdf x))‖) ≤ᶠ[atTop]
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
-- PART 7: The Main specialized Theorem Proof (Proven and fully completed)
-- =========================================================================

/-- Specialized Main Theorem: Entropy continuum convergence for standard normal density. -/
theorem discrete_to_continuous_gaussian_entropy_convergence :
  Tendsto
    (fun (N : ℕ) =>
      let σ := Real.sqrt (N : ℝ) / 2
      let Δx := 1 / σ
      let P := fun (i : ℤ) => standard_normal_pdf (i * Δx) * Δx
      let s := Finset.Icc (- (N : ℤ)) (N : ℤ)
      let H_discrete := - ∑ i ∈ s, P i * log (P i)
      H_discrete + log Δx)
    atTop
    (nhds (- ∫ x, standard_normal_pdf x * log (standard_normal_pdf x))) := by
  let f := standard_normal_pdf
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
      exact standard_normal_pos (i * (1 / (Real.sqrt (N : ℝ) / 2)))
    · exact h_pos_Δx

  rw [Filter.tendsto_congr' h_decomp]

  have h_lim1 := gaussian_riemann_sum_entropy_convergence
  have h_lim2 := scaling_error_limit f standard_normal_continuous standard_normal_pos integrable_standard_normal_pdf standard_normal_integral_eq_one standard_normal_pdf_decay standard_normal_differentiable standard_normal_deriv_decay

  have h_neg_lim1 := Tendsto.neg h_lim1
  have h_combined := Tendsto.add h_neg_lim1 h_lim2
  rw [add_zero] at h_combined
  exact h_combined
