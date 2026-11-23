import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.PrincSubring

theorem isPrincipal_of_subring : ∀ (h : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsSymmetricPair h A₁ P₁ → Out.RelAmple A₁ (diagPull A₁ P₁) → IsGrpPullback A A₁ (spMap R₁.subtype) φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsPrincipal A P → IsPrincipal A₁ P₁ := by
  intro h R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hS hamp hpb hsq hiso hpr
  haveI : IsAbelianScheme A₁ := hS.1
  haveI : IsCommMonObj A₁ := IsAbelianScheme.comm
  obtain ⟨hG, hL, hLa, hrig, hsym⟩ := GlobalTheory.T.eighth_power_symmetric_ample h A₁ P₁ hS hamp
  have hf : KerAlong A₁ P₁ (spMap R₁.subtype) := GlobalTheory.T.kernel_condition_along_baseChange_of_pullback _ A P A₁ P₁ φ φ₂ hS.2.2.1 hpb hsq hiso hpr.2
  have hfT := (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp _).1 hf
  have hK : Out.KTriv (Out.powObj A₁ 8) (powLB A₁ P₁) := by
    refine GlobalTheory.KTrivSpread.kTriv_of_primes GlobalTheory.abelianSchemeLaws_all.1.globalFns R₁ _ hG _ hL hLa fun p => ?_
    rcases GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr R R₁ p with hp | ⟨Q, k, _, i, j, V, _, _, _, ρ, e, h1, h2, hp⟩
    · exact ⟨R, inferInstance, R₁.subtype, hp, hfT⟩
    · refine ⟨V, inferInstance, ρ, hp, ?_⟩
      refine GlobalTheory.T.kGroup_trivial_spreads_from_dvr_generic_point _ _ hG hL hLa hrig hsym V (spMap ρ) ?_
      have t1 := hfT.comp (spMap (algebraMap R Q.asIdeal.ResidueField))
      have e1 : spMap (algebraMap R Q.asIdeal.ResidueField) ≫ spMap R₁.subtype = spMap j ≫ spMap i := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h1]
      rw [e1] at t1
      have t2 := (GlobalTheory.T.kGroup_trivial_descends_flat_surjective _ _ (spMap i) (spMap j) hL t1).comp (spMap e)
      have e2 : spMap e ≫ spMap i = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h2]
      rwa [e2] at t2
  have hT : GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A₁ 8) (powLB A₁ P₁) (𝟙 _) :=
    fun T a ha x hx => GlobalTheory.UU.kTriv_iff_forall.1 hK T x hx
  exact ⟨hamp, fun T x hx => (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp (𝟙 _)).2 hT T T.hom (Category.comp_id _) x hx⟩

end GlobalTheory.PrincSubring
