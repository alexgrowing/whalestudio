import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

noncomputable section

namespace GlobalTheory.BK

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

instance isUnitBall_OL : IsUnitBall ↥(OL LL) ↥LL.1 where
  inj := Subtype.val_injective
  mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ (GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y).1 y.2,
    fun h => ⟨⟨x, (GlobalTheory.mem_integralClosure_padicInt_iff LL.1 x).2 h⟩, rfl⟩⟩

instance normedAlgebra_finExt : NormedAlgebra ℚ_[l] ↥LL.1 where
  norm_smul_le c x := norm_smul_le c (x : Om l)

instance isUltrametricDist_finExt : IsUltrametricDist ↥LL.1 :=
  IsUltrametricDist.of_normedAlgebra ℚ_[l]

instance completeSpace_finExt : CompleteSpace ↥LL.1 :=
  haveI := LL.2
  FiniteDimensional.complete ℚ_[l] ↥LL.1

example : invL l (S ↥(OL LL) ↥LL.1 8) →+* Ahat ↥(OL LL) ↥LL.1 l 8 := toHatS ↥(OL LL) ↥LL.1 l 8

end GlobalTheory.BK
