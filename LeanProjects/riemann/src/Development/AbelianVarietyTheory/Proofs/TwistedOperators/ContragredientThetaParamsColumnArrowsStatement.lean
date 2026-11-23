import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_columnArrows : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i : ℕ) (τ : D.what₂.Tau), i < D.R.m → PairPar (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (dualPar (parP D i τ)) (cen D τ (D.R.m - i)) (cen D τ (D.R.m - i)) ∧ PairPar (dualPar (parP D i τ)) (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (cen D τ (D.R.m - i)) (cen D τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ParPairArrows.parPi_pairPar | exact GlobalTheory.ParPairArrows.parPi_pairPar | (intros; apply GlobalTheory.ParPairArrows.parPi_pairPar <;> assumption)
