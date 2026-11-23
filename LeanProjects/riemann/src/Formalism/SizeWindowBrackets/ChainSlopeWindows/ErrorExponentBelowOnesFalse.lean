import Formalism.SizeWindowBrackets.ErrorFormsEventualPowerBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence

open Real

namespace Formalism.LFunctionChainParameters.LErr7

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr

set_option linter.unusedVariables false

noncomputable def sD (X : ℝ) : Data Unit (fun _ => Unit) Unit 1 1 := {
  x := X, ε := 1 / 100, a := X, b := 1, b' := 1, k := X, L := 1, La := 1, B0 := 1, Nc := 1,
  gam := 0, LpL := 0, v := 1, lg := 0, logGam := 0, aT := fun _ => X, w := fun _ _ _ => 1, d := fun _ _ => 1,
  T := fun _ _ => 1, muN := fun _ _ => 0, muMaxN := fun _ _ => 0, h := fun _ _ => 0, muM := fun _ _ => 0,
  muMaxM := fun _ _ => 0, EeJ := fun _ _ _ => 0, muCC := fun _ => 0, muMinCC := fun _ => 0, Fo := fun _ => 0,
  Ga := fun _ => 0, Ta := fun _ => 0, ASK := fun _ => 0, IO := fun _ => 0, HH := fun _ => 1, del := fun _ => 0,
  η := fun _ => 0, e := fun _ => 0, delBar := 0, etaBar := 1, eBar := 0 }

def sC : Consts := ⟨1, 2, 1, 1, 1, 1, 1, 1, 0, 1⟩

lemma xe : ((10 : ℝ) ^ 400) ^ ((1 : ℝ) / 100) = 10 ^ 4 := by
  rw [← Real.rpow_natCast (10 : ℝ) 400, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (10 : ℝ) 4]
  norm_num

noncomputable def modelB (B : ℝ) : Data Unit (fun _ => Unit) Unit 1 1 := { modelD 0 with B0 := B }

def modelConstantsDivFour : Consts := ⟨1, 4, 1, 1, 1, 1, 1, 1, 0, 1⟩

section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

end

end Formalism.LFunctionChainParameters.LErr7

section Check
open Formalism.LFunctionChainParameters.LErr7
end Check
