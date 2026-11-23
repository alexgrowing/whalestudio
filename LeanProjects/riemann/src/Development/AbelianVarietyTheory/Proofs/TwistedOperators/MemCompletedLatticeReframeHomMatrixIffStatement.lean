import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedLatticeReframeHomMatrixIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_reframeHomMatrix_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T), u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔ reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  first | exact @GlobalTheory.AdSpan.ReVec.latO_reW_iff | exact GlobalTheory.AdSpan.ReVec.latO_reW_iff | (intros; apply GlobalTheory.AdSpan.ReVec.latO_reW_iff <;> assumption)
