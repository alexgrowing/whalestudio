import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  first | exact @GlobalTheory.PairLift.lowAll_of_lowFock | exact GlobalTheory.PairLift.lowAll_of_lowFock | (intros; apply GlobalTheory.PairLift.lowAll_of_lowFock <;> assumption)
