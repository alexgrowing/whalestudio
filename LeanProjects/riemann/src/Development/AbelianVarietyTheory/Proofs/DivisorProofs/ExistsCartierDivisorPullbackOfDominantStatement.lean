import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant : ∀ (Z V : Scheme.{0}) [IsIntegral Z] [IsIntegral V] (q : Z ⟶ V) [IsDominant q] (E : CartierDiv V), ∃ D : CartierDiv Z, IsPull q D E := by
  first | exact @GlobalTheory.FlagPush.exists_isPull | exact GlobalTheory.FlagPush.exists_isPull | (intros; apply GlobalTheory.FlagPush.exists_isPull <;> assumption)
