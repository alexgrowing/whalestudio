import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianSpaceSelfDualLatticeSignature
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianSpace_with_signature : ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  first | exact @GlobalTheory.exists_hSpace_sigOK_sig | exact GlobalTheory.exists_hSpace_sigOK_sig | (intros; apply GlobalTheory.exists_hSpace_sigOK_sig <;> assumption)
