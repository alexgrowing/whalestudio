import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_point_residue_nonzero : ∀ (X Y₁ Y₂ : Scheme.{0}) (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (y₁ : Y₁) (y₂ : Y₂), f y₁ = g y₂ → f.residueDegree y₁ ≠ 0 → g.residueDegree y₂ ≠ 0 → ∃ z : ↥(Limits.pullback f g), (Limits.pullback.fst f g) z = y₁ ∧ (Limits.pullback.snd f g) z = y₂ ∧ (Limits.pullback.fst f g).residueDegree z ≠ 0 ∧ (Limits.pullback.snd f g).residueDegree z ≠ 0 := by
  first | exact @GlobalTheory.PullbackFinitePoint.exists_point | exact GlobalTheory.PullbackFinitePoint.exists_point | (intros; apply GlobalTheory.PullbackFinitePoint.exists_point <;> assumption)
