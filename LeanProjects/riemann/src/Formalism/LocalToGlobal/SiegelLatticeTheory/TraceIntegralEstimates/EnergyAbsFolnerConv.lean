import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def cnt (μS : Measure G) (Ω : Set G) (q : G) : ℝ≥0∞ := μS {t | t ∈ Ω ∧ q * t ∈ Ω}

theorem cnt_measurable {μS : Measure G} [SFinite μS] {Ω : Set G} (hΩ : MeasurableSet Ω) :
    Measurable (cnt μS Ω) := by
  have hT : MeasurableSet {p : G × G | p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} :=
    (measurable_snd hΩ).inter ((measurable_fst.mul measurable_snd) hΩ)
  exact measurable_measure_prodMk_left hT

theorem cnt_le (μS : Measure G) (Ω : Set G) (q : G) : cnt μS Ω q ≤ μS Ω := measure_mono fun t ht => ht.1

theorem conv_map {S : Set G} {μS : Measure G} [SFinite μS] (hS : IsHaarSub S μS) {Ω : Set G}
    (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) :
    ((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹) = μS.withDensity (cnt μS Ω) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hright, -⟩ := hS
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ hA]
  set P : Set (G × G) := {p | p.1 ∈ A ∧ p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} with hPdef
  have hP : MeasurableSet P :=
    (measurable_fst hA).inter ((measurable_snd hΩm).inter ((measurable_fst.mul measurable_snd) hΩm))
  have h1 : (μS.prod μS) P = ∫⁻ q in A, cnt μS Ω q ∂μS := by
    rw [Measure.prod_apply hP, ← lintegral_indicator hA]
    refine lintegral_congr fun q => ?_
    rw [Set.indicator_apply]
    by_cases hq : q ∈ A
    · rw [if_pos hq]
      unfold cnt
      congr 1
      ext t
      simp [hPdef, hq]
    · rw [if_neg hq]
      have hempty : Prod.mk q ⁻¹' P = ∅ := by
        ext t
        simp [hPdef, hq]
      rw [hempty, measure_empty]
  have h2 : (μS.prod μS) P =
      ((μS.restrict Ω).prod (μS.restrict Ω)) ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) := by
    rw [Measure.prod_apply_symm hP, Measure.prod_apply_symm (hg hA), ← lintegral_indicator hΩm]
    refine lintegral_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ Ω
    · rw [if_pos ht]
      have hBt : MeasurableSet
          ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A)) :=
        (measurable_mul_const t⁻¹) hA
      rw [Measure.restrict_apply hBt]
      have hmt := hright t (hΩS ht)
      calc μS ((fun x => (x, t)) ⁻¹' P)
          = μS ((fun x => x * t) ⁻¹'
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω)) := by
            congr 1
            ext q
            simp [hPdef, ht]
        _ = (μS.map (fun x => x * t))
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) :=
            (Measure.map_apply (measurable_mul_const t) (hBt.inter hΩm)).symm
        _ = μS ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) := by
            rw [hmt]
    · rw [if_neg ht]
      have hempty : (fun x => (x, t)) ⁻¹' P = ∅ := by
        ext q
        simp [hPdef, ht]
      rw [hempty, measure_empty]
  exact h2.symm.trans h1

theorem conv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set G} {μS : Measure G} [SFinite μS]
    (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hfin : μS Ω < ⊤) (f : G → E)
    (hf : StronglyMeasurable f)
    (hint : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω))) :
    ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS = ∫ q, (cnt μS Ω q).toReal • f q ∂μS := by
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  have hI : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω)) := by
    assumption
  have h1 : ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS
      = ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω)) :=
    (integral_prod (fun p : G × G => f (p.1 * p.2⁻¹)) hI).symm
  have h2 : ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω))
      = ∫ q, f q ∂(((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹)) :=
    (integral_map_of_stronglyMeasurable hg hf).symm
  rw [h1, h2, conv_map hS hΩm hΩS]
  exact integral_withDensity_eq_integral_toReal_smul (cnt_measurable hΩm)
    (ae_of_all _ fun q => (cnt_le μS Ω q).trans_lt hfin) f

end Formalism.L2.S.Pv.EnergyAbs
