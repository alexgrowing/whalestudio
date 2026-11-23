import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.IsLowUnitH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DsigWSubAvg
open Formalism.MainNotions.S

namespace GlobalTheory.KFinDenseDS

theorem kFin_dense : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ := by
  intro k r ε lam H _ _ _ σ hl hds v hv Ws hWs δ hδ
  obtain ⟨a, ha, hs⟩ := GlobalTheory.KFinAvg.kDense k r ε lam H σ hl hds v hv Ws hWs δ hδ
  refine ⟨a, ha, ?_⟩
  simpa only [Formalism.MainNotions.BridgeCS3d.dsigW_eq] using hs

end GlobalTheory.KFinDenseDS
