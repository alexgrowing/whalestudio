import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFunc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc : ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L) (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L → j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d → Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  first | exact @GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc | exact GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc | (intros; apply GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc <;> assumption)
