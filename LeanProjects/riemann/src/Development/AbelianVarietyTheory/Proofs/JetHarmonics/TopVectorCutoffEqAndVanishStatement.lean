import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanish
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topVector_cutoff_eq_and_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) F → (ε < TBB.Gp p (TBB.bigPt P.r c) → tv p (D.cutF p.T.base χ F ε) w c = tv p F w c) ∧ (TBB.Gp p (TBB.bigPt P.r c) < δ * ε → tv p (D.cutF p.T.base χ F ε) w c = 0) ∧ (TBB.Gp p (TBB.bigPt P.r c) ≤ 0 → tv p F w c = 0) := by
  first | exact @GlobalTheory.TopVec.tv_cutF | exact GlobalTheory.TopVec.tv_cutF | (intros; apply GlobalTheory.TopVec.tv_cutF <;> assumption)
