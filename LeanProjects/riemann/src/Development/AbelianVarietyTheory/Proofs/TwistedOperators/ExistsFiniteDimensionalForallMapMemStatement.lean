import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMem
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_forall_map_mem' : ∀ (p q : ℕ) (M : GKMod p q), AdmGK M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V, (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ W, φ v ∈ E := by
  first | exact @GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem | exact GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem | (intros; apply GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem <;> assumption)
