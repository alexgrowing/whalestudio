import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP.WhittakerBoundEstimates

def realHomeoQ : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toEquiv := RationalIdeles.realEquiv.toEquiv
  continuous_toFun := RationalIdeles.continuous_realEquiv
  continuous_invFun := RationalIdeles.continuous_realEquiv_symm

instance : ((infiniteAdeleMeasure ℚ).map realHomeoQ).IsAddHaarMeasure :=
  RationalIdeles.realEquiv.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure ℚ)
    RationalIdeles.continuous_realEquiv RationalIdeles.continuous_realEquiv_symm

end Ad3.GP.WhittakerBoundEstimates
