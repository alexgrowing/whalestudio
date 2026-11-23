import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportOfPolarisationIdealTimesLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTransport_of_polarisationIdealTimesLattice : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)), IsAA Λ ΛT → IsMov m Λ Λ → IsMov m ΛT ΛT := by
  first | exact @GlobalTheory.LevMoveAA.isMov_of_isAA | exact GlobalTheory.LevMoveAA.isMov_of_isAA | (intros; apply GlobalTheory.LevMoveAA.isMov_of_isAA <;> assumption)
