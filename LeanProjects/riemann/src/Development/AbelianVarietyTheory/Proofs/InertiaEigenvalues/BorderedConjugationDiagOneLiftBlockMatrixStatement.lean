import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix : ∀ (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k), act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  first | exact @GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | exact GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | (intros; apply GlobalTheory.JR.Step.ActEmbLift.act_emb_lift <;> assumption)
