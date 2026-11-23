import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralConjLineEq
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_conjLine_eq : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine | exact GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine <;> assumption)
