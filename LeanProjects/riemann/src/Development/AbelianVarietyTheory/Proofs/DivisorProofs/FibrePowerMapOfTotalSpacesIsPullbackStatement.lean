import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f → ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  first | (exact @GlobalTheory.KS.PowPB.powMap_isPullback) | (exact GlobalTheory.KS.PowPB.powMap_isPullback) | (intros; apply GlobalTheory.KS.PowPB.powMap_isPullback  <;> assumption)
