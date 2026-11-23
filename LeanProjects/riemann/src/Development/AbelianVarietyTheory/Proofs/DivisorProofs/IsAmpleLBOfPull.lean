import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteBase

theorem isAmpleLB_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) π → ∀ L : LB G.left, L.IsLB → IsAmpleLB (L.pull π) → IsAmpleLB L := by
  intro R R' _ _ _ _ _ _ _ _ _ _ ρ hinj hfin G _ G' _ π hG h L hL hA
  have := hG.smooth
  have := hG.quasiCompact
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hfin
  have hS : Surjective (spMap ρ) := ⟨hfin.to_isIntegral.comap_surjective hinj⟩
  have : IsFinite π := MorphismProperty.of_isPullback (P := @IsFinite) h.1.flip hF
  have hs : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hS
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hN : GlobalTheory.IsNormalScheme G.left := isNormalScheme_of_smooth G.hom
  exact GlobalTheory.NormalDescent.isAmpleLB_of_pull G.left G'.left π ⟨⟩
    (fun x => ⟨hN.1 x, hN.2 x⟩) inferInstance hs.surj L hL hA

end GlobalTheory.AmpleFiniteBase
