import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAbStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

theorem exists_ample_symmetric : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  intro R _ _ _ G _ hG hab
  obtain ⟨M₀, s₀, hM, ha, hy₀⟩ := GlobalTheory.T.exists_affine_nonzeroLocus_unit_closedFibre_semiAb R G hG hab
  have hpt := GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange GlobalTheory.T.exists_theorem_of_square_semiAbelian_genericAbelian R G hG hab M₀ hM s₀ ha hy₀
  have := hG.quasiCompact
  have := hG.separated
  have hcs : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hamp : IsAmpleLB M₀ := ⟨hM, hcs, fun y => by
    obtain ⟨R', _, ρ, hρ, x', hx', hs⟩ := hpt y
    have h := GlobalTheory.T.exists_affine_nonzeroLocus_descend_flat_baseChange R R' ρ hρ G.left G.hom inferInstance inferInstance M₀ hM x' hs
    rwa [hx'] at h⟩
  exact GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme (Sp R) G M₀ hamp

end GlobalTheory.SymAmple
