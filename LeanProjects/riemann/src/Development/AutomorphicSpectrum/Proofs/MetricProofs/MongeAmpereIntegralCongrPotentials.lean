import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SamePotInt

variable {D : ℕ}

theorem exists_fderiv_fderiv_re {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    ∃ B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ, ∀ v w,
      fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w = (B v w).re := by
  let Φ : ((Fin D → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ)
  have hev : (fderiv ℝ fun z => (H z).re) =ᶠ[𝓝 y] fun z => Φ (fderiv ℂ H z) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have h1 : HasFDerivAt H ((fderiv ℂ H z).restrictScalars ℝ) z :=
      hz.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact (Complex.reCLM.hasFDerivAt.comp z h1).fderiv
  have hd : DifferentiableAt ℂ (fderiv ℂ H) y := hH.fderiv.differentiableAt
  refine ⟨fderiv ℂ (fderiv ℂ H) y, fun v w => ?_⟩
  have h2 : HasFDerivAt (fun z => Φ (fderiv ℂ H z))
      (Φ.comp ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hd.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem hessC_re_eq_zero {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    hessC (fun z => (H z).re) y = 0 := by
  obtain ⟨B, hB⟩ := exists_fderiv_fderiv_re hH
  ext i j
  simp only [hessC, Matrix.zero_apply, hB, map_smul, _root_.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

theorem hessC_eq_of_eventuallyEq_add_re {a a' : (Fin D → ℂ) → ℝ} {H : (Fin D → ℂ) → ℂ}
    {y : Fin D → ℂ} (ha : ContDiffAt ℝ 2 a y) (hH : AnalyticAt ℂ H y)
    (hev : a' =ᶠ[𝓝 y] fun z => a z + (H z).re) : hessC a' y = hessC a y := by
  have hb : ContDiffAt ℝ 2 (fun z => (H z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hH.contDiffAt.restrict_scalars ℝ)
  have h2 : fderiv ℝ (fderiv ℝ a') y =
      fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ fun z => (H z).re) y := by
    have hda : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ a z :=
      (ha.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hdb : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => (H z).re) z :=
      (hb.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have h1 : fderiv ℝ a' =ᶠ[𝓝 y] fun z => fderiv ℝ a z + fderiv ℝ (fun z => (H z).re) z := by
      filter_upwards [hev.eventuallyEq_nhds, hda, hdb] with z hz hza hzb
      rw [hz.fderiv_eq]
      exact fderiv_add hza hzb
    rw [h1.fderiv_eq]
    exact fderiv_add ((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have h0 := hessC_re_eq_zero hH
  rw [← add_zero (hessC a y), ← h0]
  ext i j
  simp only [hessC, Matrix.add_apply, h2, _root_.add_apply]
  push_cast
  ring

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_eq_of_samePot (A : FinHolAtlas e X) {U : Set X} {P Q : Fin e → LocPot X}
    (hPQ : ∀ i, SamePot A U (P i) (Q i)) (hC : ∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ U) :
    locDens A P j y = locDens A Q j y := by
  have key : ∀ i, hessC (fun y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro i
    obtain ⟨V, hVo, hxV, G, hG, hPQV⟩ := hPQ i _ hU
    have hsrc : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    have ha : ContDiffAt ℝ 2 (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      have h := hC i _ hU j hsrc
      rw [(A.chart j).right_inv hy] at h
      exact h
    have hH : AnalyticAt ℂ (fun y' => G ((A.chart j).symm y')) y := hG j y ⟨hy, hxV⟩
    refine hessC_eq_of_eventuallyEq_add_re ha hH ?_
    have hV : (A.chart j).symm ⁻¹' V ∈ 𝓝 y :=
      ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hVo.mem_nhds hxV)
    filter_upwards [hV] with z hz
    exact sub_eq_iff_eq_add'.mp (hPQV _ hz)
  simp only [locDens, maDens, key]

end SamePotInt

theorem mInt_congr_samePot : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ →
    (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) →
    mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  intro e X _ _ _ A U P Q g g' hN hPQ hC hg
  have hpt : ∀ (j : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart j).target → (A.chart j).symm y ∈ U →
      g ((A.chart j).symm y) = g' ((A.chart j).symm y) ∧ locDens A P j y = locDens A Q j y :=
    fun j y hy hU => ⟨hg _ hU, SamePotInt.locDens_eq_of_samePot A hPQ hC j hy hU⟩
  have hae : ∀ (j : Fin A.n), ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin e → ℂ)),
      y ∈ (A.chart j).target → (A.chart j).symm y ∈ U := by
    intro j
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (hN j)
    intro y hy
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  constructor
  · by_cases h : Nonempty (ChartPartition A)
    · simp only [mInt, dif_pos h, integralWith]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine MeasureTheory.setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      obtain ⟨h1, h2⟩ := hpt j y hyt (hy hyt)
      simp only [h1, h2]
    · simp only [mInt, dif_neg h]
  · unfold MIntegrable
    refine forall_congr' fun j => forall_congr' fun K => forall_congr' fun hK =>
      forall_congr' fun hKc => ?_
    refine MeasureTheory.integrableOn_congr_fun_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hKc.isClosed.measurableSet]
    filter_upwards [hae j] with y hy hyK
    obtain ⟨h1, h2⟩ := hpt j y (hK hyK) (hy (hK hyK))
    simp only [h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB
