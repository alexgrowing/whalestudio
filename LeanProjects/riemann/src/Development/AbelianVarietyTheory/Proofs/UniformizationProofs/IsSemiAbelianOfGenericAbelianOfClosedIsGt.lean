import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isSemiAbelian_of_grpIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] [hc : IsCommMonObj G₂]
    (e : G₂ ≅ G₁) [IsMonHom e.hom] (h : IsSemiAbelian G₁) : IsSemiAbelian G₂ := by
  have hi : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hw : G₂.hom = e.hom.left ≫ G₁.hom := (Over.w e.hom).symm
  have := h.smooth
  have := h.separated
  have := h.quasiCompact
  have hg := h.geomConnected
  refine ⟨hc, ?_, ?_, ?_, ?_, fun Ω _ _ q => ?_⟩
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩
    have hi' : IsIso ((Over.pullback q).map e.hom).left :=
      ((Over.pullback q ⋙ Over.forget _).mapIso e).isIso_hom
    have h1 : ConnectedSpace ((Over.pullback q).obj G₁).left := pullback_of_geometrically hg.1 K q
    exact (((Over.pullback q).map e.hom).left.homeomorph.connectedSpace_iff).2 h1
  · obtain ⟨E⟩ := h.fibres Ω q
    have : IsMonHom ((Over.pullback q).mapIso e).hom := inferInstanceAs (IsMonHom ((Over.pullback q).map e.hom))
    have : IsMonHom ((Over.pullback q).mapIso e).symm.hom :=
      inferInstanceAs (IsMonHom ((Over.pullback q).mapIso e).inv)
    exact ⟨torusExtOfIso ((Over.pullback q).mapIso e).symm E⟩

end GlobalTheory
