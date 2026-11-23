import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace PI.UnitaryDimensionFormula

theorem idxDSig : IdxDSig := by
  intro I
  refine ⟨unitaryCongruence.sigA_sigA (I := I), ?_⟩
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp [JA, sigA, Formalism.UG.inclE, Formalism.UG.sigR]
  congr 1
  rw [← unitaryCongruence.J_conj (I := I) j i]
  first
  | rfl
  | simp

theorem idxDInt : IdxDInt := fun I =>
  ⟨fun _ hx _ hy => unitaryCongruence.hA_int I hx hy, fun _ hc => unitaryCongruence.sigA_mem I hc⟩

end PI.UnitaryDimensionFormula
