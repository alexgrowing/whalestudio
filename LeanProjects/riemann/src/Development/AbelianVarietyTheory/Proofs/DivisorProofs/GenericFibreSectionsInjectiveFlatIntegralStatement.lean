import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSectionsInjectiveFlatIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_sections_injective_flat_integral : ∀ {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S) (a : Y ⟶ X) (t : Y ⟶ Sp F), IsPullback a t f gp → Flat f → IsIntegral S → IsDominant gp → ∀ U : X.Opens, Function.Injective (a.app U).hom := by
  first | exact @GlobalTheory.Mum.genFib_app_injective | exact GlobalTheory.Mum.genFib_app_injective | (intros; apply GlobalTheory.Mum.genFib_app_injective <;> assumption)
