import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChange
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q]) (G : V → ℂ), (∀ i j, ι (c i j) = zc (a i j)) → (∀ i, w i = ∑ j, c i j • v j) → MomInt ι v G → MomInt ι w G := by
  first | exact @GlobalTheory.MomN.momInt_push | exact GlobalTheory.MomN.momInt_push | (intros; apply GlobalTheory.MomN.momInt_push <;> assumption)
