import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceTubeBandAbsEnergy
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBandEnergy
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceBandAbsEnergy

variable {n e : ℕ}

open Classical in

theorem energyDens_mono (hNN : LogNormEnergyDensNonneg.Statement) (h : HermNorm n)
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}
    {f₁ f₂ : (Fin n → ℂ) → ℝ} (hf : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), f₁ x ≤ f₂ x)
    {y : Fin (e + 1) → ℂ} (hfin : (fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y).Finite) :
    chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A f₁
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => f₁ x * Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y ≤
    chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A f₂
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => f₂ x * Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y := by
  rw [SliceBandEnergy.chartDens_energy h f₁ hfin, SliceBandEnergy.chartDens_energy h f₂ hfin]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · obtain ⟨U, hU, hxU, hd, hsx, -⟩ := hs.choose_spec
    have han := FormIntegralPositivity.analyticAt_sheet hs.choose_spec
    rw [hx.2] at han hsx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := SliceBandEnergy.linEval_eq_one hx.1
      simp [linEval] at this
    have hG := hNN n e h hs.choose y ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) han
      (by rw [hsx]; exact hx0)
    exact mul_le_mul_of_nonneg_right (hf x hx.1) hG
  · exact le_rfl

open Classical in

theorem energyDens_sum (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    {A : Matrix (Fin (e + 1)) (Fin n) ℂ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ℂ) → ℝ)
    {y : Fin (e + 1) → ℂ} (hfin : (fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y).Finite) :
    chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => ∑ k ∈ s, f k x)
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => (∑ k ∈ s, f k x) * Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y =
    ∑ k ∈ s, (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (f k)
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => f k x * Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y) := by
  have e0 := SliceBandEnergy.chartDens_energy h (fun x => ∑ k ∈ s, f k x) hfin
  beta_reduce at e0
  rw [e0, Finset.sum_congr rfl fun k _ => SliceBandEnergy.chartDens_energy h (f k) hfin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Finset.sum_mul]
  · simp

theorem neg_log_norm_le {h : HermNorm n} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) :
    -Real.log (h.norm ℓ) ≤ Real.log (h.dualNorm x) := by
  have h1 := h.norm_pairing_le ℓ x
  have h2 : ∑ j, ℓ j * x j = 1 := SliceBandEnergy.linEval_eq_one hx
  rw [h2, norm_one] at h1
  have hn0 : 0 ≤ h.norm ℓ := Real.sqrt_nonneg _
  have hd0 : 0 ≤ h.dualNorm x := Real.sqrt_nonneg _
  have hnp : 0 < h.norm ℓ := lt_of_le_of_ne hn0 (by rintro h0; rw [← h0, zero_mul] at h1; linarith)
  have hdp : 0 < h.dualNorm x := lt_of_le_of_ne hd0 (by rintro h0; rw [← h0, mul_zero] at h1; linarith)
  have := Real.log_le_log one_pos h1
  rw [Real.log_one, Real.log_mul hnp.ne' hdp.ne'] at this
  linarith

theorem integrable_band (hLI : LogIntegrable.Statement) (h : HermNorm n)
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {u ℓ : Fin n → ℂ} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}
    (hprime : (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = (e + 1 : ℕ))
    (hAp : IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A)
    (huS : linForm u ∉ J ⊔ Ideal.span {linForm ℓ - 1}) (a b : ℝ) :
    Integrable (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A
        (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
          {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x)
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x))) ∧
    Integrable (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A
        (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
          {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x *
            Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x))) := by
  have hsm := smoothNear_log_dualNorm_slice h J ℓ
  have hΦ : ∀ k, SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}))
      (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k) := by
    intro k
    refine Fin.cases ?_ (fun _ => hsm) k
    obtain ⟨U, hU, hSU, hT⟩ := hsm
    exact ⟨U, hU, hSU, (hT.pow 2).div_const 2⟩
  have hω : ∀ k : Fin (e + 1), SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}))
      ((fun _ x => Real.log (h.dualNorm x)) k) := fun _ => hsm
  set c : ℂ := ((Real.exp 1 : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast (Real.exp_pos 1).ne'
  have hℓ1 : linForm ℓ - 1 ∈ J ⊔ Ideal.span {linForm ℓ - 1} :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hcS : linForm (fun j => c * ℓ j) ∉ J ⊔ Ideal.span {linForm ℓ - 1} := by
    intro hmem
    have h1 : linForm (fun j => c * ℓ j) = C c * linForm ℓ := by
      simp [linForm, Finset.mul_sum, mul_assoc]
    have h2 : (C c : MvPolynomial (Fin n) ℂ) ∈ J ⊔ Ideal.span {linForm ℓ - 1} := by
      have := Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ (C c) hℓ1)
      rwa [h1, ← mul_sub, sub_sub_cancel, mul_one] at this
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 ((Ne.isUnit hc0).map C))
  obtain ⟨R, hR⟩ := (SliceCut.isCompact_sublevel h (Real.exp b)).isBounded.subset_closedBall 0
  set B : Set (Fin n → ℂ) := {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} with hBdef
  have key : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), x ∈ B →
      (Metric.closedBall 0 R).indicator (fun x => Real.log ‖linEval (fun j => c * ℓ j) x‖) x = 1 ∧
        (Metric.closedBall 0 R).indicator (fun x => Real.log ‖linEval u x‖) x = Real.log ‖linEval u x‖ ∧
        |Real.log (h.dualNorm x)| ≤ |a| + |b| := by
    intro x hx hxB
    have hball : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
      refine hR ?_
      show h.dualNorm x ≤ Real.exp b
      have hnn : 0 ≤ h.dualNorm x := Real.sqrt_nonneg _
      rcases hnn.eq_or_lt with h0 | h0
      · rw [← h0]; exact (Real.exp_pos b).le
      · exact (Real.log_le_iff_le_exp h0).mp hxB.2
    refine ⟨?_, Set.indicator_of_mem hball _, abs_le.mpr ⟨?_, ?_⟩⟩
    · rw [Set.indicator_of_mem hball]
      have hl : linEval (fun j => c * ℓ j) x = c * linEval ℓ x := by
        simp [linEval, Finset.mul_sum, mul_assoc]
      rw [hl, SliceBandEnergy.linEval_eq_one hx, mul_one, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos 1), Real.log_exp]
    · linarith [neg_abs_le a, abs_nonneg b, hxB.1]
    · linarith [le_abs_self b, abs_nonneg a, hxB.2]
  set f₁ := (Metric.closedBall (0 : Fin n → ℂ) R).indicator
    (fun x => Real.log ‖linEval (fun j => c * ℓ j) x‖) with hf₁
  set f₂ := (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun x => Real.log ‖linEval u x‖) with hf₂
  have hTm : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  have hLm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    unfold linEval
    fun_prop
  have hBm : MeasurableSet B :=
    (measurableSet_le measurable_const hTm).inter (measurableSet_le hTm measurable_const)
  have hgam : Measurable fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| :=
    continuous_abs.measurable.comp (hTm.sub hLm)
  have hIm : Measurable (B.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hBm
  have hK2 : 0 ≤ (1 + 1) * (|a| + |b| + 1) ^ 2 := by positivity
  have hb3 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      |(|Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x)| ≤
        (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x| := by
    intro x hx
    by_cases hxB : x ∈ B
    · obtain ⟨e1, e2, hTx⟩ := key x hx hxB
      rw [e1, e2, abs_one, mul_one, Set.indicator_of_mem hxB, mul_one, abs_abs]
      have := (SliceBandEnergy.weight_bound (v := 1) (M := 1) (L := Real.log ‖linEval u x‖) hTx (by norm_num)).1
      rwa [abs_one, mul_one] at this
    · rw [Set.indicator_of_notMem hxB, mul_zero, abs_zero]
      exact add_nonneg (mul_nonneg hK2 (abs_nonneg _)) (mul_nonneg hK2 (abs_nonneg _))
  have hb4 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      |(|Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x *
          Real.log (h.dualNorm x))| ≤
        (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x| := by
    intro x hx
    by_cases hxB : x ∈ B
    · obtain ⟨e1, e2, hTx⟩ := key x hx hxB
      rw [e1, e2, abs_one, mul_one, Set.indicator_of_mem hxB, mul_one, abs_mul, abs_abs]
      have := (SliceBandEnergy.weight_bound (v := 1) (M := 1) (L := Real.log ‖linEval u x‖) hTx (by norm_num)).2
      rwa [abs_one, mul_one] at this
    · rw [Set.indicator_of_notMem hxB, mul_zero, zero_mul, abs_zero]
      exact add_nonneg (mul_nonneg hK2 (abs_nonneg _)) (mul_nonneg hK2 (abs_nonneg _))
  exact ⟨SliceBandEnergy.integrable_chartDens hprime hdim hAp f₁ f₂ (hgam.mul hIm) hΦ hb3
      (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hΦ) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hΦ),
    SliceBandEnergy.integrable_chartDens hprime hdim hAp f₁ f₂ ((hgam.mul hIm).mul hTm) hω hb4
      (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hω) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hω)⟩

end SliceBandAbsEnergy

theorem SliceBandAbsEnergy.proof (hLI : LogIntegrable.Statement) (hNN : LogNormEnergyDensNonneg.Statement)
    (hTube : SliceTubeBandAbsEnergy.Statement) : SliceBandAbsEnergy.Statement := by
  classical
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨r₀, C₁, hC₁⟩ := hTube n e h J F u ℓ hJ hF hu hℓ hℓW
  by_cases hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A
  swap
  · refine ⟨0, fun a b _ => ?_⟩
    simp only [varInt, dif_neg hA, sub_zero, zero_mul, le_refl]
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ
  have huS := (SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ).2.2 u hu
  have hAp := hA.choose_spec
  have hfin : ∀ y, (fibre (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose y).Finite := fun y =>
    (FibreBound.proof n (e + 1) _ _ hprime hdim hAp y).2.1
  have hint := SliceBandAbsEnergy.integrable_band hLI h hprime hdim hAp huS

  have hE : ∀ a b : ℝ,
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) =
      ∫ y, (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y) := by
    intro a b
    simp only [varInt, dif_pos hA, chartInt]
    rw [integral_sub (hint a b).1 (hint a b).2]

  have hwmono : ∀ a b a' b' : ℝ, (∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      a ≤ Real.log (h.dualNorm x) → Real.log (h.dualNorm x) ≤ b →
        a' ≤ Real.log (h.dualNorm x) ∧ Real.log (h.dualNorm x) ≤ b') →
      ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
        |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x ≤
          |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a' ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b'}.indicator (fun _ => 1) x := by
    intro a b a' b' hsub x hx
    by_cases hxB : a ≤ Real.log (h.dualNorm x) ∧ Real.log (h.dualNorm x) ≤ b
    · have hxB' := hsub x hx hxB.1 hxB.2
      rw [Set.indicator_of_mem (show x ∈ {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} from hxB),
        Set.indicator_of_mem (show x ∈ {y | a' ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b'} from hxB')]
    · rw [Set.indicator_of_notMem (show x ∉ {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} from hxB),
        mul_zero]
      exact mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

  set L := -Real.log (h.norm ℓ) with hL
  have hunit : ∀ r : ℝ,
      ∫ y, (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | r ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r + 1}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | r ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r + 1}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y) ≤
      max C₁ (∫ y, (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | L ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r₀ + 1}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | L ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r₀ + 1}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y)) := by
    intro r
    rcases le_or_gt r₀ r with hr | hr
    · rw [← hE]
      exact (hC₁ r hr).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      refine integral_mono ((hint r (r + 1)).1.sub (hint r (r + 1)).2)
        ((hint L (r₀ + 1)).1.sub (hint L (r₀ + 1)).2) fun y => ?_
      refine SliceBandAbsEnergy.energyDens_mono hNN h (hwmono r (r + 1) L (r₀ + 1) ?_) (hfin y)
      intro x hx _ h2
      exact ⟨SliceBandAbsEnergy.neg_log_norm_le hx, by linarith⟩
  set C₂ := max C₁ (∫ y, (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | L ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r₀ + 1}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | L ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r₀ + 1}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y)) with hC₂
  refine ⟨max C₂ 0, fun a b hab => ?_⟩
  rw [hE]
  set N := ⌊b - a⌋₊ with hN

  have hcover : ∀ x,
      |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
          {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x ≤
        ∑ k ∈ Finset.range (N + 1), |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
          {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x := by
    intro x
    have hnn : ∀ k ∈ Finset.range (N + 1), 0 ≤ |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
        {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x :=
      fun k _ => mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    by_cases hxB : a ≤ Real.log (h.dualNorm x) ∧ Real.log (h.dualNorm x) ≤ b
    · set k := ⌊Real.log (h.dualNorm x) - a⌋₊ with hk
      have hk0 : 0 ≤ Real.log (h.dualNorm x) - a := by linarith [hxB.1]
      have hkN : k ≤ N := Nat.floor_le_floor (by linarith [hxB.2])
      have hk1 : (k : ℝ) ≤ Real.log (h.dualNorm x) - a := Nat.floor_le hk0
      have hk2 : Real.log (h.dualNorm x) - a < k + 1 := Nat.lt_floor_add_one _
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN)))
      rw [Set.indicator_of_mem (show x ∈ {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} from hxB),
        Set.indicator_of_mem (show x ∈ {y | a + (k : ℝ) ≤ Real.log (h.dualNorm y) ∧
          Real.log (h.dualNorm y) ≤ a + k + 1} from ⟨by linarith, by linarith⟩)]
    · rw [Set.indicator_of_notMem (show x ∉ {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} from hxB),
        mul_zero]
      exact Finset.sum_nonneg hnn

  have hpt : ∀ y,
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y ≤
      ∑ k ∈ Finset.range (N + 1),
        (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y) := by
    intro y
    have hs := SliceBandAbsEnergy.energyDens_sum h (Finset.range (N + 1))
      (fun (k : ℕ) x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
        {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x)
      (hfin y)
    beta_reduce at hs
    rw [← hs]
    exact SliceBandAbsEnergy.energyDens_mono hNN h (fun x _ => hcover x) (hfin y)
  have hsumint : ∀ k ∈ Finset.range (N + 1), Integrable fun y =>
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x)
          (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
          (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
            {y | a + k ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ a + k + 1}.indicator (fun _ => 1) x *
              Real.log (h.dualNorm x))
          (fun _ x => Real.log (h.dualNorm x)) y :=
    fun k _ => (hint (a + k) (a + k + 1)).1.sub (hint (a + k) (a + k + 1)).2
  refine (integral_mono ((hint a b).1.sub (hint a b).2) (integrable_finsetSum _ hsumint) hpt).trans ?_
  rw [integral_finsetSum _ hsumint]
  refine (Finset.sum_le_sum fun (k : ℕ) _ => (hunit (a + (k : ℝ))).trans (le_max_left C₂ 0)).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ b - a + 1 := by
    push_cast
    linarith [Nat.floor_le (show 0 ≤ b - a by linarith)]
  exact mul_le_mul_of_nonneg_right hN1 (le_max_right _ _) |>.trans_eq (mul_comm _ _)

end

end GroundTheory.Heights₂.Heights
