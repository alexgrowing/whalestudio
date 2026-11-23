import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSucc
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_twist_succ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist <;> assumption)
