import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps : ∀ (D : D7) (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  first | exact @GlobalTheory.FinPl.LatMem.mem_latO_iff | exact GlobalTheory.FinPl.LatMem.mem_latO_iff | (intros; apply GlobalTheory.FinPl.LatMem.mem_latO_iff <;> assumption)
