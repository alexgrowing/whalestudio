import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEq
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multAt_twist_quad_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (J W : Ideal (MRing ι)), W ∈ J.minimalPrimes → (twist p W).IsPrime → multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist <;> assumption)
