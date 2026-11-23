import Mathlib
import GroundTheory.LocalFields.RamificationTame
import GroundTheory.LocalFields.UnramifiedHensel

noncomputable section

open scoped IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_tame_structure (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ T : IntermediateField K L, IsUnramified K T ∧
      Module.finrank K T = residueDegree K L ∧ residueDegree T L = 1 ∧
      ramificationIndex T L = ramificationIndex K L ∧
      Module.finrank T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  obtain ⟨β, -, -, -, -, hun, hdeg, hres⟩ := exists_unramified_adjoin K L
  set T := K⟮(β : L)⟯
  obtain ⟨htow, hrest⟩ := exists_pow_eq_uniformizer_of_isUnramified T hres he
  have hfin : Module.finrank T L = ramificationIndex K L := by
    have := ramificationIndex_mul_residueDegree T L
    rw [hres, mul_one, htow] at this
    exact this.symm
  exact ⟨T, hun, hdeg, hres, htow, hfin, hrest⟩

end GroundTheory.LocalField
