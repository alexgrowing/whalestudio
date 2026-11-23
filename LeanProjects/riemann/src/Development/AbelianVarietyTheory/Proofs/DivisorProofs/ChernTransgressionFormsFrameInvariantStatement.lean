import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTransgression_forms_frame_invariant : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' G₂ G₂' T K K' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K' u a b) x) → IsUnit (K' v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ ∧ G₂' x = T x * G' x * (K' x)ᴴ) → ∀ k, powAt G₂ v k = powAt G v k ∧ chernAt G₂ v k = chernAt G v k ∧ transAt G₂ G₂' v k = transAt G G' v k := by
  first | exact @GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame | exact GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame | (intros; apply GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame <;> assumption)
