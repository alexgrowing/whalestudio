import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.CplxDC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldDCUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldMult
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TranslationIndependent

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.PoincareSeriesInner.W

universe u

theorem fold_L2_complex_of (hc : CplxDC.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesInner G μ := by
  intro Γ S S' hΓ hS hS' Ω hΩ h1 a a' Ph Ph' hP hP' F F' hF hF' hm hm' D D' hD hD' R hR Fs hFs FΓ hFΓ
  haveI : Countable Γ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  obtain ⟨hPm, hPinv, hPb⟩ := hP
  obtain ⟨hPm', hPinv', hPb'⟩ := hP'
  have hΩm : MeasurableSet Ω := hΩ.isClosed.measurableSet
  obtain ⟨hM1, hMfin, hMinv, hMm⟩ := overlapMultiplicityProperties G Γ hΓ Ω hΩ h1
  have hbd := foldBound_holds G μ Γ S hΓ hS Ω hΩm a Ph hPm hPinv hPb F hF D hD
  have hbd' := foldBound_holds G μ Γ S' hΓ hS' Ω hΩm a' Ph' hPm' hPinv' hPb' F' hF' D' hD'
  have hQf : quotientLIntegral μ F Ph < ∞ := by
    refine lt_of_le_of_lt ?_ hm
    exact lintegral_mono fun y => le_mul_of_one_le_left zero_le' (hM1 y)
  have hQf' : quotientLIntegral μ F' Ph' < ∞ := by
    refine lt_of_le_of_lt ?_ hm'
    exact lintegral_mono fun y => le_mul_of_one_le_left zero_le' (hM1 y)
  have hK : ∫⁻ x in FΓ, mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ ∂μ = multiplicityLIntegral μ Γ Ω F' Ph' := by
    have hfun : (fun x => mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ)
        = fun x => ∑' δ' : D', mult Γ Ω (δ' * x) * ‖Ph' (δ' * x)‖ₑ := by
      funext x
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun δ' => ?_
      rw [hMinv δ' (hD'.1 δ'.2) x]
    rw [hfun]
    exact lintegralTransversalSum G μ Γ S' hS' F' hF' FΓ hFΓ D' hD' (fun y => mult Γ Ω y * ‖Ph' y‖ₑ)
      (hMm.mul hPm'.enorm) (fun s hs y => by simp only [hMinv s (hS' hs) y, hPinv' s hs y])
  have hne : (a : ℝ≥0∞) * quotientLIntegral μ F Ph ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hQf.ne
  have hfin : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hQf) hm'
  have hI : ∫⁻ x in FΓ, (∑' δ : D, ‖Ph (δ * x)‖ₑ) * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ ∂μ
      ≤ a * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' := by
    calc _ ≤ ∫⁻ x in FΓ, ((a : ℝ≥0∞) * quotientLIntegral μ F Ph) * (mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc (∑' δ : D, ‖Ph (δ * x)‖ₑ) * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ
              ≤ (a * mult Γ Ω x * quotientLIntegral μ F Ph) * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ := mul_le_mul' (hbd x) le_rfl
            _ = _ := by ring
      _ = ((a : ℝ≥0∞) * quotientLIntegral μ F Ph) * ∫⁻ x in FΓ, mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ ∂μ :=
          lintegral_const_mul' _ _ hne
      _ = _ := by rw [hK]
  have hunf := fold_dc_unfold G μ Γ S S' hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ
    (fun x => ‖Ph x‖ₑ) (fun x => ‖Ph' x‖ₑ) hPm.enorm hPm'.enorm
    (fun s hs y => by simp only [hPinv s hs y]) (fun s hs y => by simp only [hPinv' s hs y])
  have h2 : ∑' r : R, ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' ((r : G)⁻¹ * x)‖ₑ ∂μ < ∞ := by
    rw [← hunf]
    exact hI.trans_lt hfin
  have hconj : Measurable (fun z : ℂ => (starRingEnd ℂ) z) := Complex.continuous_conj.measurable
  have henc : ∀ z : ℂ, ‖(starRingEnd ℂ) z‖ₑ = ‖z‖ₑ := fun z => by simp
  refine ⟨?_, h2, ?_, ?_⟩
  · calc ∫⁻ x in F', ‖Ph' x‖ₑ * ∑' δ : D, ‖Ph (δ * x)‖ₑ ∂μ
        ≤ ∫⁻ x in F', ((a : ℝ≥0∞) * quotientLIntegral μ F Ph) * (mult Γ Ω x * ‖Ph' x‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc ‖Ph' x‖ₑ * ∑' δ : D, ‖Ph (δ * x)‖ₑ ≤ ‖Ph' x‖ₑ * (a * mult Γ Ω x * quotientLIntegral μ F Ph) :=
                mul_le_mul' le_rfl (hbd x)
            _ = _ := by ring
      _ = a * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' := by
          rw [lintegral_const_mul' _ _ hne]
          rfl
  · intro r hr
    have hle : ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' (r⁻¹ * x)‖ₑ ∂μ < ∞ :=
      (ENNReal.le_tsum (f := fun r : R => ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' ((r : G)⁻¹ * x)‖ₑ ∂μ)
        ⟨r, hr⟩).trans_lt h2
    refine ⟨(hPm.mul (hconj.comp (hPm'.comp (measurable_const_mul _)))).aestronglyMeasurable, ?_⟩
    simpa [HasFiniteIntegral, enorm_mul, henc] using hle
  · have hψm : Measurable (fun x => (starRingEnd ℂ) (Ph' x)) := hconj.comp hPm'
    have hpc : ∀ x, poinc D' (fun y => (starRingEnd ℂ) (Ph' y)) x = (starRingEnd ℂ) (poinc D' Ph' x) :=
      fun x => by simp only [poinc, Complex.conj_tsum]
    have key := hc G μ Γ S S' hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ Ph (fun x => (starRingEnd ℂ) (Ph' x))
      hPm hψm hPinv (fun s hs y => by simp only [hPinv' s hs y])
      (fun x => ((hbd x).trans_lt (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.coe_lt_top (hMfin x)) hQf)).ne)
      (fun x => by
        simp only [henc]
        exact ((hbd' x).trans_lt (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.coe_lt_top (hMfin x)) hQf')).ne)
      (by
        simp only [henc]
        exact (hI.trans_lt hfin).ne)
    simp only [hpc] at key
    exact key

end PI.PoincareSeriesInner.W
