import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPower
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
open GlobalTheory.MomN Formalism.L2.Th1.H
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ)) (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomRoot.jets_root | exact GlobalTheory.MomRoot.jets_root | (intros; apply GlobalTheory.MomRoot.jets_root <;> assumption)
