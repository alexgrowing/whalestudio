import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseIsotropicFrameKillingEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_isotropicFrame_killing_embedding : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  first | exact @GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb | exact GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb | (intros; apply GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb <;> assumption)
