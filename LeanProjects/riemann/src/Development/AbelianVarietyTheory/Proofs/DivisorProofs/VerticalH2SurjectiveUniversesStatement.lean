import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2SurjectiveUniverses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_h2_surjective_universes : VertHas.{1,1} (fun m ↦ Function.Surjective m.h2) ∧ VertHas.{1,0} (fun m ↦ Function.Surjective m.h2) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h2) := by
  first | exact @GlobalTheory.CxCoh.VertSurjTwo.inst | exact GlobalTheory.CxCoh.VertSurjTwo.inst | (intros; apply GlobalTheory.CxCoh.VertSurjTwo.inst <;> assumption)
