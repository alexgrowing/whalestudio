import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareDecompositionFiniteExtensionAmpleBunStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalNoetherianCoverFractionFieldExStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseChangeGrpPullbackDomainsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionOfBaseChangeAlongIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAbStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.CoverDec

theorem exists_cover_sqDec : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (L M : LB G.left), L.IsLB → M.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (π : G'.left ⟶ G.left), Function.Injective ρ ∧ ρ.Finite ∧ IsGrpPullback G' G (spMap ρ) π ∧ SqDec G' (L.pull π) (M.pull π) := by
  intro R _ _ _ _ hc G _ hG hAb L M hL hM hAL hAM hSL hSM
  have sL := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) L hL hSL
  have sM := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) M hM hSM
  obtain ⟨K', _, _, _, hD⟩ := GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle (FractionRing R) ((Over.pullback (jK R)).obj G) hAb _ _
    (pull_isLB hL _) (pull_isLB hM _) hAL hAM sL sM
  obtain ⟨R', _, _, _, _, _, ρ, τ, hinj, hfin, hcomp⟩ := GlobalTheory.T.exists_finite_normal_noetherian_cover_fractionFieldExt R hc K'
  obtain ⟨π₀, hP, hLL⟩ := GlobalTheory.T.genericFibre_baseChange_grpPullback_domains R R' ρ (τ.comp (algebraMap (FractionRing R) K')) hcomp G
  have hD' := GlobalTheory.SqDecTransport.transport (FractionRing R) (FractionRing R') K' (FractionRing R')
    (τ.comp (algebraMap (FractionRing R) K')) (algebraMap (FractionRing R) K') (RingHom.id _) τ rfl
    ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) π₀ hP _ _ _ _
    (pull_isLB hL _) (pull_isLB hM _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (hLL L hL) (hLL M hM) hD
  have h1 := GlobalTheory.T.squareDecomposition_of_baseChange_along_identity _ _ _ _ (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _) hD'
  have h2 := GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian R' ((Over.pullback (spMap ρ)).obj G) (IsSemiAbelian.pullback (spMap ρ) G hG) _ _
    (pull_isLB hL _) (pull_isLB hM _) h1
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    (Over.pullback (spMap ρ)).obj G, inferInstance, pullback.fst G.hom (spMap ρ), hinj, hfin,
    isGrpPullback_pullback G (spMap ρ), h2⟩

end GlobalTheory.CoverDec
