import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectors
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  first | exact @GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | exact GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | (intros; apply GlobalTheory.TopVecPol.beta_eq_integral_inner_tv <;> assumption)
