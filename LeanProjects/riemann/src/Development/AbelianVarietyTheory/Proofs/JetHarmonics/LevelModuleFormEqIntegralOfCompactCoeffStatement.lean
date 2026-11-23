import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeff
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (j : ℕ) (h : C.LPt), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → j ≤ P.r → D.IsLocPt h j → Integrable (fun t : ℂ => (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)])) ∧ p.RR H j w h h = ∫ t : ℂ, (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
  first | exact @GlobalTheory.LevelIntegralStep.levelForm_eq_integral | exact GlobalTheory.LevelIntegralStep.levelForm_eq_integral | (intros; apply GlobalTheory.LevelIntegralStep.levelForm_eq_integral <;> assumption)
