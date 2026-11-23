import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdImageBot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualGraphModel

open StandardDualImageBottom

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem mConeMap_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (q : Σ _ : Unit, Fin i) :
    mConeMap (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) =
      C (aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q)) * X () := by
  simp only [linForm, map_sum, map_mul, Finset.sum_mul, mConeMap, aeval_X, eq_intCast, map_intCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

def coneLift (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MRing (dualBlocks T) ⧸ dualIdeal b →+* MvPolynomial Unit (ProjField K i) :=
  Ideal.Quotient.lift (dualIdeal b)
    (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) fun _ ha => ha

omit [Fintype T] in
theorem coneLift_mk (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (dualBlocks T)) :
    coneLift b (Ideal.Quotient.mk _ f) = mConeMap (dualLatticeCoord b) f :=
  rfl

omit [Fintype T] in
theorem coneLift_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (coneLift b) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun _ ha => ha

def modelMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp (MvPolynomial.map (coneLift b))

omit [Fintype T] in
theorem modelMap_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (modelMap b) :=
  (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i)).comp
    (MvPolynomial.map_injective _ (coneLift_injective b))

theorem modelMap_comp_graphMap [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    (modelMap b).comp (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) =
      (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) := by
  refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
  rintro ⟨(u | u), j⟩ <;> cases u
  · simp [graphMap, modelMap, coneLift_mk, dualStdModelPt, dualStdModelEmb, dualStdModelS,
      mConeMap]
  · have h := mConeMap_linForm b ⟨(), j⟩
    rw [aeval_linForm] at h
    simp only [RingHom.comp_apply, graphMap, eval₂Hom_X', modelMap, map_mul, map_C, map_X, coneLift_mk, h,
      dualStdModelPt, dualStdModelEmb, dualStdModelS, dualStdModelT, genPt]

end StandardDualGraphModel

open StandardDualGraphModel in

theorem DualStdGraphModel.proof : DualStdGraphModel.Statement := by
  intro K _ _ i T _ _ b
  rw [← modelMap_comp_graphMap b]
  ext f
  rw [graphIdeal, RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (modelMap_injective b)]

end

end GroundTheory.Heights₂.Heights
