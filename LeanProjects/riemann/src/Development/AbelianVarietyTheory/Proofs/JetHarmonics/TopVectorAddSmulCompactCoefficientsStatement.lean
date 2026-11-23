import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topVector_add_smul_compactCoefficients : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → KB.CptCoef p.T.base H₁ → KB.CptCoef p.T.base H₂ → tv p (H₁ + a • H₂) w c = tv p H₁ w c + a • tv p H₂ w c := by
  first | exact @GlobalTheory.TopVec.tv_add_smul | exact GlobalTheory.TopVec.tv_add_smul | (intros; apply GlobalTheory.TopVec.tv_add_smul <;> assumption)
