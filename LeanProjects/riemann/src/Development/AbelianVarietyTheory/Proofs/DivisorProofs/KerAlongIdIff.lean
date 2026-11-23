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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section
namespace GlobalTheory.PrincSubring

def powLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : LB (Out.powObj A 8).left :=
  LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (Out.powPr A uv.1) (Out.powPr A uv.2)).left)
    fun uv => GlobalTheory.W8 uv.1 uv.2

def KerAlong {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (g : S' ⟶ S) : Prop :=
  ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A, IsTrivial (slice A P x) → x = 1

theorem KerAlong.comp {S S' S'' : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (A ⊗ A).left} {g : S' ⟶ S}
    (h : KerAlong A P g) (f : S'' ⟶ S') : KerAlong A P (f ≫ g) :=
  fun T a ha => h T (a ≫ f) ((Category.assoc _ _ _).trans ha)

end GlobalTheory.PrincSubring
