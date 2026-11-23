import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_compactDualHaar : Nonempty CDHaar := by
  first | exact @GlobalTheory.CompactDualExists.nonempty_cdHaar | exact GlobalTheory.CompactDualExists.nonempty_cdHaar | (intros; apply GlobalTheory.CompactDualExists.nonempty_cdHaar <;> assumption)
