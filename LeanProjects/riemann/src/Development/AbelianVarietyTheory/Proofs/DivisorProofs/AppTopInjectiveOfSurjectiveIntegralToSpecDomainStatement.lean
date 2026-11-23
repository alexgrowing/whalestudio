import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appTop_injective_of_surjective_integral_toSpecDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  first | exact @GlobalTheory.appTop_injective_of_surjective_toSpec_domain | exact GlobalTheory.appTop_injective_of_surjective_toSpec_domain | (intros; apply GlobalTheory.appTop_injective_of_surjective_toSpec_domain <;> assumption)
