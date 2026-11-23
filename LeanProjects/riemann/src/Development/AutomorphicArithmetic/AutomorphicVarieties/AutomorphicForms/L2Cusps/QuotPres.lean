import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BandDom
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

private theorem measurableSet_band' (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    MeasurableSet (band E a) := by
  have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  have h := hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))
  exact (MeasurableSet.const (a = 0)).union h

theorem UpperTheory.V.KernelIndexFullLattice.quotPres_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotPres := by
  intro E _ _ _ a μ _
  have hr : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable
  have hD := RightCosetSpace.measurableSet_fundamentalDomain (Γ1 E a)
  have hmk : Measurable (RightCosetSpace.mk (Γ1 E a)) := RightCosetSpace.measurable_mk _
  have hcomp : quotMap E a ∘ mk (latticeGL E a) = RightCosetSpace.mk (Γ1 E a) ∘ retractOne :=
    funext fun g => quotMk_holds E a g
  have hq : Measurable (quotMap E a) := by
    refine measurable_from_quotient.2 ?_
    change Measurable (quotMap E a ∘ mk (latticeGL E a))
    rw [hcomp]
    exact hmk.comp hr
  have hF : IsFundamentalDomain (latticeGL E a)
      (retractOne ⁻¹' RightCosetSpace.fundamentalDomain (Γ1 E a) ∩ band E a) μ :=
    IsFundamentalDomain.mk' ((hr hD).inter (measurableSet_band' E a)).nullMeasurableSet
      (bandDom_holds E a _ (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (Γ1 E a)))
  refine ⟨hq, ?_⟩
  rw [quotMeasure_eq hF, Measure.map_map hq measurable_mk, hcomp, RightCosetSpace.quotientMeasure, muOne,
    Measure.restrict_map hr hD, Measure.restrict_restrict (hr hD), Measure.map_map hmk hr]
