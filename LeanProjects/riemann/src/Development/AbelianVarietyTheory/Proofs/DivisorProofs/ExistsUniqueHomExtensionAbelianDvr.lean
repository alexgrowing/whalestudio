import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbHomExtDvr

theorem existsUnique_hom_extension_abelian_dvr :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G G' : Over (Sp W)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ (Over.pullback (spMap (algebraMap W L))).obj G', IsMonHom f → ∃! F : G ⟶ G', (Over.pullback (spMap (algebraMap W L))).map F = f := by
  intro W L _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have hsm : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, by have := hG.proper; infer_instance,
    by have := hG.proper; infer_instance, hG.geomConnected⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr W L G G' hsm
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme G' hG') f hf
  have := hG.smooth
  have := hG'.proper
  have : Flat G.hom := inferInstance
  refine ⟨F, hF, fun F' hF' => ?_⟩
  exact GlobalTheory.KernelNoTorsion.eq_of_generic W L (hF'.trans hF.symm)

end GlobalTheory.AbHomExtDvr
