import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.continuous_piV) | (exact GlobalTheory.OrbFinAf.continuous_piV) | (intros; apply GlobalTheory.OrbFinAf.continuous_piV  <;> assumption)
