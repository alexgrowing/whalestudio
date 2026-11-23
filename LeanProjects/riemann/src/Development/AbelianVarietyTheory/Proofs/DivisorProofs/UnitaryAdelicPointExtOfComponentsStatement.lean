import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_ext_of_components : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf), (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  first | (exact @GlobalTheory.OrbFinAf.ext_of_piV) | (exact GlobalTheory.OrbFinAf.ext_of_piV) | (intros; apply GlobalTheory.OrbFinAf.ext_of_piV  <;> assumption)
