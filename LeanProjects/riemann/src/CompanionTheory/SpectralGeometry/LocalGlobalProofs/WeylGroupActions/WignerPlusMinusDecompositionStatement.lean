import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigLower_of_adjoint_norm_sq_lower_bound : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg | exact GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg | (intros; apply GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg <;> assumption)
