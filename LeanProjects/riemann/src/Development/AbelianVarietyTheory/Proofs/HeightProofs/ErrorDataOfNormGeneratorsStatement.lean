import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ErrorDataOfNormGenerators
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.error_data_of_norm_generators : ∀ X : Stages, (∀ i, ∃ π : 𝓞 X.B.host.E, (π : X.B.host.E) ∈ X.B.host.K ∧ (π : X.B.host.E) * X.B.host.conj (π : X.B.host.E) = (X.B.host.g i : X.B.host.E)) → Nonempty (ErrX X.toD7) := by
  first | exact @GlobalTheory.SplitGen.nonempty_errX | exact GlobalTheory.SplitGen.nonempty_errX | (intros; apply GlobalTheory.SplitGen.nonempty_errX <;> assumption)
