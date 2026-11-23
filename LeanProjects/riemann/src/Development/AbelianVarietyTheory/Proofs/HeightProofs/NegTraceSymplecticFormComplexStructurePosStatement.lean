import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePos
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  first | exact @GlobalTheory.FockCompare.symplC_jAt_neg | exact GlobalTheory.FockCompare.symplC_jAt_neg | (intros; apply GlobalTheory.FockCompare.symplC_jAt_neg <;> assumption)
