import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StdCoordMapInjective
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField TensorProduct GroundTheory.Heights₂.Heights

noncomputable section

theorem HermitianExtension.degree_range_incl {K : Type} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle.{0} K} (Y : HermitianExtension E' E E'') :
    E.degree (LinearMap.range Y.incl) = E'.arithDegree := by
  rw [HermitianBundle.degree_eq_arithDegree]
  symm
  refine LatticeLemmas.arithDegree_congr _ _ (LinearEquiv.ofInjective Y.incl Y.incl_injective)
    fun σ x y ↦ ?_
  rw [HermitianMetric.comap_inner, fibreMap_tmul, fibreMap_tmul]
  have h := Y.incl_isometric σ ((1 : ComplexAt σ) ⊗ₜ x) ((1 : ComplexAt σ) ⊗ₜ y)
  simp only [LinearMap.lTensor_tmul] at h
  exact h.symm

theorem S6.ExtensionDegree.proof : S6.ExtensionDegree.Statement := by
  intro K _ _ E' E E'' Y
  rw [HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.degree_top_eq_arithDegree,
    HermitianExtension.degree_range_incl, Y.arithDegree_eq_add]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
