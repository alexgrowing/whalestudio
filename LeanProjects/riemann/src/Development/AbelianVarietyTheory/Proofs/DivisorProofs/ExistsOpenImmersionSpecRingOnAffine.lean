import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.AffChart

open GlobalTheory.Points

theorem exists_openImm_spec_ringOn (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω)
    (W : M.Z.Opens) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty) :
    ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧
      spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  let φ : Γ(M.Z, W) ⟶ CommRingCat.of (M.ringOn W) := (M.sectionsEquiv W hne).toCommRingCatIso.hom
  haveI : IsIso φ := inferInstanceAs (IsIso (M.sectionsEquiv W hne).toCommRingCatIso.hom)
  refine ⟨Spec.map φ ≫ hW.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, hW.opensRange_fromSpec]
  · have hp := M.top_le_preimage_pt hne
    have e : φ ≫ CommRingCat.ofHom (algebraMap (M.ringOn W) Ω) = valMap M.pt W hp := by
      ext f
      exact (M.coe_sectionsEquiv W hne f).trans (M.res_apply W hne f).symm
    rw [spMap, ← Category.assoc, ← Spec.map_comp, e, specMap_valMap_fromSpec]

end GlobalTheory.Div.AffChart
