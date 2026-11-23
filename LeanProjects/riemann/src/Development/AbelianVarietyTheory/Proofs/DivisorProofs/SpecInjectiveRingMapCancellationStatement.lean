import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_injectiveRingMap_cancellation : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') := by
  first | exact @GlobalTheory.Nef.spMap_injective_cancel | exact GlobalTheory.Nef.spMap_injective_cancel | (intros; apply GlobalTheory.Nef.spMap_injective_cancel <;> assumption)
