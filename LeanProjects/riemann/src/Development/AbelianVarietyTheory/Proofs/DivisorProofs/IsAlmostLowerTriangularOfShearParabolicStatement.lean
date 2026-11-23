import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L, Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  first | exact @GlobalTheory.FlagPush.almostLow_of_shear | exact GlobalTheory.FlagPush.almostLow_of_shear | (intros; apply GlobalTheory.FlagPush.almostLow_of_shear <;> assumption)
