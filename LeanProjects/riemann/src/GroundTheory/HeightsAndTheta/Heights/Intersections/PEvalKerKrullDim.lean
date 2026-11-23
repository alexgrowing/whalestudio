import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IntermediateField.algebraAdjoinAdjoin

theorem EvalKerKrullDim.proof : EvalKerKrullDim.Statement := by
  intro K _ ι _ F L _ _ _ y

  let f : MRingOver F ι →ₐ[F] Algebra.adjoin F (Set.range y) :=
    (Subalgebra.equivOfEq _ _ (MvPolynomial.aeval_range y)).toAlgHom.comp (aeval y).rangeRestrict
  have hf : Function.Surjective f :=
    (Subalgebra.equivOfEq _ _ (MvPolynomial.aeval_range y)).surjective.comp
      (AlgHom.rangeRestrict_surjective _)
  have hker : RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L) = RingHom.ker f := by
    ext p
    simp [f, RingHom.mem_ker, Subtype.ext_iff]
  let e : (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) ≃ₐ[F]
      Algebra.adjoin F (Set.range y) :=
    (Ideal.quotientEquivAlgOfEq F hker).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  have _ : Algebra.FiniteType F (Algebra.adjoin F (Set.range y)) :=
    Algebra.FiniteType.of_surjective f hf
  exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing F
    (IntermediateField.adjoin F (Set.range y))

end GroundTheory.Heights₂.Heights.Inter
