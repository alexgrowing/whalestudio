import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

theorem UpperTheory.V.Sd.finCoef :
    UpperTheory.V.Sd.FinCoef := by
  intro l _ Γ _ _ _ _ _ n r hr
  exact GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ n r
    fun i j => (Units.continuous_val.comp hr).matrix_elem i j
