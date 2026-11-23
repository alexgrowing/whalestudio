import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeEndProductPowers_transport_grpPullback : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  first | (exact @GlobalTheory.ActFin.prod_zpow_transport) | (exact GlobalTheory.ActFin.prod_zpow_transport) | (intros; apply GlobalTheory.ActFin.prod_zpow_transport  <;> assumption)
