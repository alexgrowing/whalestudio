import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ainf_isDomain_and_injective : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧
    Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  intro l _
  have : IsDomain (Per.Fl l) := inferInstance
  have h : IsDomain (Per.Ainf l) := inferInstance
  have hp : (l : Per.Ainf l) ≠ 0 := WittVector.p_nonzero l _
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hp
  exact ⟨h, IsLocalization.isDomain_of_le_nonZeroDivisors (Per.AinfP l) hle, IsLocalization.injective _ hle⟩

end GlobalTheory.MemLoc
