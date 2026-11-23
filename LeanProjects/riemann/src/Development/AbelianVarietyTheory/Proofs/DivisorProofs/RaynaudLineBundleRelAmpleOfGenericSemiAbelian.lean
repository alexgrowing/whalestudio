import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfLbPowLbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverSymmBundlePowerDecompositStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGenericSemiAb

theorem isAmpleLB_of_generic_of_symm (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R]
    (hc : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (hA : IsAbelianScheme ((Over.pullback (jK R)).obj G)) (L : LB G.left) (hL : L.IsLB)
    (hLK : RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))))
    (hs : LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L) : IsAmpleLB L := by
  obtain ⟨M, hMa, hMs⟩ := GlobalTheory.T.exists_ample_symmetric_lineBundle_semiAbelian R G hG hA
  have hMK : RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) := by
    have : IsProper ((Over.pullback (jK R)).obj G).hom := hA.proper
    have h1 : IsAffineHom (jK R) := by unfold jK; infer_instance
    have : IsAffineHom (pullback.fst G.hom (jK R)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback G.hom (jK R)).flip h1
    exact (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_linComb hMa.isLB _ _)).2
      (hMa.pull_of_isAffineHom _)
  obtain ⟨R', _, _, _, _, _, ρ, G', _, π, hinj, hfin, hpb, N, a₀, r, a, β, hN, ha₀, -, hiso⟩ :=
    GlobalTheory.T.exists_finiteNormalCover_symmBundle_power_decomposition R hc G hG hA L M hL hMa.isLB hLK hMK hs hMs
  have : IsFinite π := by
    have : IsFinite (spMap ρ) := by
      unfold spMap
      rw [IsFinite.SpecMap_iff]; exact hfin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.1.flip this
  have hamp := GlobalTheory.AmplePowLinComb.isAmpleLB_of_lbPow_lbIso_linComb _ (L.pull π) (M.pull π)
    (hMa.pull_of_isFinite π) (LB.isLB_linComb hL _ _) N a₀ r a (fun i => (β i).left) hN ha₀ hiso
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  exact GlobalTheory.AmpleFiniteBase.isAmpleLB_of_pull R R' ρ hinj hfin G G' π hG hpb L hL hamp

theorem isAmpleLB_of_generic : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R],
    IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB →
    RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) →
    LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L :=
  fun R _ _ _ _ hc G _ hG hA L hL hLK hs => isAmpleLB_of_generic_of_symm R hc G hG hA L hL hLK hs

end GlobalTheory.AmpleGenericSemiAb
