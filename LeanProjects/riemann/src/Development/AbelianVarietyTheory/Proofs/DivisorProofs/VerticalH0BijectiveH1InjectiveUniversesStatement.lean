import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH0BijectiveH1InjectiveUniverses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_h0_bijective_h1_injective_universes : VertHas.{1,1} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{1,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) := by
  first | exact @GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | exact GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | (intros; apply GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 <;> assumption)
