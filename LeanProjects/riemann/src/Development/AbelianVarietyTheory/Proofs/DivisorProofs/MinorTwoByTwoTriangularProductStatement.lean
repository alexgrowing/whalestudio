import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_two_by_two_triangular_product : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  first | exact @GlobalTheory.FlagPush.almostLow_mul_entries | exact GlobalTheory.FlagPush.almostLow_mul_entries | (intros; apply GlobalTheory.FlagPush.almostLow_mul_entries <;> assumption)
