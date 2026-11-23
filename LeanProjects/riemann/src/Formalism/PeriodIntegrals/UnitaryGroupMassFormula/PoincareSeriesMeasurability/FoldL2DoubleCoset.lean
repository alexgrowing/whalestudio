import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldMult

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PI.PoincareSeriesMemLp.UnitaryGroupMassFormula

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

theorem measurable_poinc {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (D : Set G) [Countable D] (Ph : G → ℂ) (hPh : Measurable Ph)
    (hs : ∀ x, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) ≠ ⊤) : Measurable (poinc D Ph) := by
  have hsum : ∀ x, Summable (fun δ : D => Ph ((δ : G) * x)) := by
    intro x
    have h1 : Summable (fun δ : D => ‖Ph ((δ : G) * x)‖₊) := by
      have h2 := hs x
      simp only [enorm_eq_nnnorm] at h2
      exact ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    exact Summable.of_norm (by simpa using NNReal.summable_coe.mpr h1)
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset D))
    (f := fun (s : Finset D) x => ∑ δ ∈ s, Ph ((δ : G) * x)) (fun s => ?_) ?_
  · exact Finset.measurable_sum _ (fun δ _ => hPh.comp (measurable_const_mul _))
  · rw [tendsto_pi_nhds]
    intro x
    unfold poinc
    exact (hsum x).hasSum

theorem fold_L2_double_coset (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesMemLp G μ := by
  intro Γ S hΓ hSΓ Ω hΩ h1 a Ph hdat F hF hI D hD FΓ hFΓ
  obtain ⟨hPh, hinv, hrep⟩ := hdat
  have hcΓ : Countable Γ :=
    (TopologicalSpace.separableSpace_iff_countable (α := Γ)).mp inferInstance
  have hcD : Countable D := by
    have hinj : Function.Injective (fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ)) := by
      intro d e h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    exact hinj.countable
  obtain ⟨hm1, hmtop, hminv, hmmeas⟩ := overlapMultiplicityProperties G Γ hΓ Ω hΩ h1

  have hqI : quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph := by
    unfold quotientLIntegral multiplicityLIntegral
    exact lintegral_mono fun y => le_mul_of_one_le_left (by simp) (hm1 y)
  have hq : quotientLIntegral μ F Ph < ⊤ := lt_of_le_of_lt hqI hI

  have hT : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤ (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph :=
    fun x => foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.measurableSet a Ph hPh hinv hrep F hF D hD x
  have hTfin : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hmtop x).ne) hq.ne) (hT x)
  set g : G → ℝ≥0∞ := fun y => mult Γ Ω y * ‖Ph y‖ₑ with hgdef
  have hpt : ∀ x : G, ‖poinc D Ph x‖ₑ ^ 2
      ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x) := by
    intro x
    have hP : ‖poinc D Ph x‖ₑ ≤ ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := enorm_tsum_le_tsum_enorm
    have hg : ∑' δ : D, g ((δ : G) * x) = mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun δ => ?_
      simp only [hgdef]
      rw [hminv δ (hD.1 δ.2) x]
    rw [hg, pow_two]
    calc ‖poinc D Ph x‖ₑ * ‖poinc D Ph x‖ₑ
        ≤ (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := mul_le_mul' hP hP
      _ ≤ (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) * ((a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph) :=
          mul_le_mul' le_rfl (hT x)
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * (mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) := by ring

  have hgm : Measurable g := hmmeas.mul hPh.enorm
  have hginv : ∀ s ∈ S, ∀ y : G, g (s * y) = g y := by
    intro s hs y
    simp only [hgdef]
    rw [hminv s (hSΓ hs) y, hinv s hs y]
  have hunf : (∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ) = multiplicityLIntegral μ Γ Ω F Ph :=
    lintegralTransversalSum G μ Γ S hSΓ F hF FΓ hFΓ D hD g hgm hginv
  have hbound : (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ)
      ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph := by
    calc (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ)
        ≤ ∫⁻ x in FΓ, (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x) ∂μ :=
          lintegral_mono hpt
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hq.ne)
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph := by rw [hunf]

  have hlast : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph
      ≤ (a : ℝ≥0∞) * multiplicityLIntegral μ Γ Ω F Ph ^ 2 := by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul' (mul_le_mul' le_rfl hqI) le_rfl

  have hfin : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hq) hI
  have hPm : Measurable (poinc D Ph) := measurable_poinc D Ph hPh hTfin
  refine ⟨⟨hPm.aestronglyMeasurable, ?_⟩, hbound, hlast⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have h2 : ∀ x, ‖poinc D Ph x‖ₑ ^ ((2 : ℝ≥0∞).toReal) = ‖poinc D Ph x‖ₑ ^ 2 := by
    intro x
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
    norm_num
  simp_rw [h2]
  exact lt_of_le_of_lt hbound hfin

end PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
