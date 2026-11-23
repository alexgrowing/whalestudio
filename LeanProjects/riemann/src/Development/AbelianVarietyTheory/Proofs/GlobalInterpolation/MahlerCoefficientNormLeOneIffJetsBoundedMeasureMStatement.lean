import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureM
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ : Type) [Fintype κ] (v : κ → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (MomInt ι v G ↔ ∀ n, ‖ι (mahler v G n)‖ ≤ 1) := by
  first | exact @GlobalTheory.MomCrit.momInt_iff_norm_mahler_le | exact GlobalTheory.MomCrit.momInt_iff_norm_mahler_le | (intros; apply GlobalTheory.MomCrit.momInt_iff_norm_mahler_le <;> assumption)
