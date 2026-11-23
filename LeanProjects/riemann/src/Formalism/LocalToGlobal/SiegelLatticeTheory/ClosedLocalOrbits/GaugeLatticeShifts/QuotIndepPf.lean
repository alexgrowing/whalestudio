import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.QuotIndepStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.WeilIndicatorMeasures.MeasurableUnitMulIndicator

open MeasureTheory Measure
open scoped ENNReal

namespace Formalism.L2.SG.Pf.QuotIndep

namespace QuotIndepPf

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

lemma exists_bruhat (S : Subgroup G) (hS : IsClosed (S : Set G)) (μS : Measure S)
    [μS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS] [IsOpenPosMeasure μS] [SFinite μS] :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ x : G, ∫⁻ s, b ((s : G) * x) ∂μS = 1 := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨β, hβm, hβ1⟩ := Formalism.L2.SG.Pf.Weil.QuotInt.exists_fib_eq_one hS μS.inv
  refine ⟨fun z => β z⁻¹, hβm.comp measurable_inv, fun x => ?_⟩
  have h := hβ1 x⁻¹
  unfold Formalism.L2.SG.Pf.Weil.QuotInt.fib at h
  rw [Measure.inv, lintegral_map (f := fun s : S => β (x⁻¹ * s)) (hβm.comp
    ((measurable_const_mul _).comp measurable_subtype_coe)) measurable_inv] at h
  simpa [mul_inv_rev] using h

lemma lintegral_eq_bruhat (S : Subgroup G) (μS : Measure S) (μ ν : Measure G) (b : G → ℝ≥0∞)
    (hbm : Measurable b) (hb1 : ∀ x : G, ∫⁻ s, b ((s : G) * x) ∂μS = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ (s : S) (x : G), f ((s : G) * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, b x * f x ∂μ := by
  have h := hν (fun x => b x * f x) (hbm.mul hf)
  rw [h]
  refine lintegral_congr fun x => ?_
  simp_rw [hinv]
  rw [lintegral_mul_const (f x) (show Measurable fun s : S => b ((s : G) * x) from
    hbm.comp (measurable_subtype_coe.mul_const x)), hb1, one_mul]

end QuotIndepPf

open QuotIndepPf in

theorem quotIndep : QuotIndep := by
  intro G _ _ _ _ _ _ _ _ S hS μS _ _ _ _ _ μ ν₁ ν₂ h₁ h₂ f hf hinv
  obtain ⟨b, hbm, hb1⟩ := exists_bruhat S hS μS
  rw [lintegral_eq_bruhat S μS μ ν₁ b hbm hb1 h₁ f hf hinv,
    lintegral_eq_bruhat S μS μ ν₂ b hbm hb1 h₂ f hf hinv]

end Formalism.L2.SG.Pf.QuotIndep
