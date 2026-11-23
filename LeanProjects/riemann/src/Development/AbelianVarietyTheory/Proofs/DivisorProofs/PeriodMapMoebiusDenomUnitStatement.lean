import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_map_moebius_denom_unit : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B (fun b => moeb γ (τ b)) → ∀ b ∈ B, IsUnit (den γ (τ b)) := by
  first | exact @GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap | exact GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap | (intros; apply GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap <;> assumption)
