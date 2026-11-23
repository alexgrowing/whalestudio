import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlatStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem thetaMetric_isMetric_chernFlat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → IsMetric B τ (stdLat g) (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) ∧ ChernIsFlat B τ (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) :=
  @GlobalTheory.T.theta_metric_chern_flat

end GlobalTheory
