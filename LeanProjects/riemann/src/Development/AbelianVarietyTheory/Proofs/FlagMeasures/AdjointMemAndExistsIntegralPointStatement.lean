import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_mem_and_exists_integral_point : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  first | exact @GlobalTheory.RadCov.RatElt.adj_mem_and_exists_latGroup | exact GlobalTheory.RadCov.RatElt.adj_mem_and_exists_latGroup | (intros; apply GlobalTheory.RadCov.RatElt.adj_mem_and_exists_latGroup <;> assumption)
