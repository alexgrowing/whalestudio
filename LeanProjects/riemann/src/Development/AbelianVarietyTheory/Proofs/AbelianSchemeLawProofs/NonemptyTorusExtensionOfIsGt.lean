import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem nonempty_torusExtension_of_isGt {K : Type} [Field K] (E : SplitExt (Spec (.of K)))
    (G : Over (Spec (.of K))) [GrpObj G] (h : E.IsGt G) : Nonempty (TorusExtension G) := by
  obtain ⟨d⟩ := h
  have := E.free
  have := E.finite
  have := d.q_affine
  exact ⟨
    { X := E.X
      B := E.B
      isAbelian := E.isAbelian
      q := d.q
      q_hom := d.q_hom
      q_flat := d.q_flat
      q_surjective := d.q_surjective
      q_quasiCompact := inferInstance
      i := d.i
      i_hom := d.i_hom
      isKernel := d.isKernel }⟩

theorem isSemiAbelian_of_isGt : ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G],
    E.IsGt G → IsSemiAbelian G := by
  intro S E G _ hc h
  obtain ⟨hs, hg⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  obtain ⟨d⟩ := h
  have := d.q_affine
  have := E.isAbelian.proper
  refine ⟨hc, hs, ?_, ?_, hg, fun Ω _ _ p => ?_⟩
  · rw [← Over.w d.q]
    infer_instance
  · rw [← Over.w d.q]
    infer_instance
  · exact nonempty_torusExtension_of_isGt _ _ (GtBaseChange.isGt_extBC p E G d)

end GlobalTheory
