import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwist
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_divSupp_twist_eq_image : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (P : Ideal (MRing ι)) (s : MRing ι), (∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) → {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} = twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist <;> assumption)
