import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsLastRowArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_lastRowArrows : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (j : ℕ) (τ : D.what₂.Tau) (hj : j < D.R.m), PairPar (dualPar (parXp D (j + 1) τ)) (dualPar (parXp D j τ)) (-(D.hc τ).e ⟨j, hj⟩) (-(D.hc τ).e ⟨j, hj⟩) := by
  first | exact @GlobalTheory.TopPair.pairPar_top | exact GlobalTheory.TopPair.pairPar_top | (intros; apply GlobalTheory.TopPair.pairPar_top <;> assumption)
