import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH1SurjectiveUniverses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_h1_surjective_universes : VertHas.{1,1} (fun m ↦ Function.Surjective m.h1) ∧ VertHas.{1,0} (fun m ↦ Function.Surjective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h1) := by
  first | exact @GlobalTheory.CxCoh.VertSurj.instances | exact GlobalTheory.CxCoh.VertSurj.instances | (intros; apply GlobalTheory.CxCoh.VertSurj.instances <;> assumption)
