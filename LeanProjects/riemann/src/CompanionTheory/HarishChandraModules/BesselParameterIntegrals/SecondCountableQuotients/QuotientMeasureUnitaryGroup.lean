import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.PolarUH
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.StabilizerModularFunctionTrivial
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.ModExists

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula

theorem quotient_measure_unitary_group : PI.QuotSetU := by
  intro k r z hz hT
  have hG := unitary_hermitian_group k r
  have hS := stabilizer_closed_matrix_group k r z hz hT
  obtain ⟨DG, hDG, hRG⟩ := ModEx.exists_modular_function _ _ hG
  obtain ⟨DS, hDS, hRS⟩ := ModEx.exists_modular_function _ _ hS
  exact ⟨hG, hS, siegel_set_subset k r z, hRG (unitary_group_modular_function_trivial k r DG hDG),
    hRS (stabilizer_modular_function_trivial k r z hz hT DS hDS)⟩

end CompanionTheory.D.Upq.QuotSetU
