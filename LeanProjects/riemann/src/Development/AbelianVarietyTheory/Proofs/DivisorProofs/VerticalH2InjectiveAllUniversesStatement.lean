import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2InjectiveAllUniverses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_h2_injective_three_universe_pairs : VertHas.{1,1} (fun m ↦ Function.Injective m.h2) ∧ VertHas.{1,0} (fun m ↦ Function.Injective m.h2) ∧ VertHas.{0,0} (fun m ↦ Function.Injective m.h2) := by
  first | exact @GlobalTheory.CxCoh.vertical_h2_injective_universes | exact GlobalTheory.CxCoh.vertical_h2_injective_universes | (intros; apply GlobalTheory.CxCoh.vertical_h2_injective_universes <;> assumption)
