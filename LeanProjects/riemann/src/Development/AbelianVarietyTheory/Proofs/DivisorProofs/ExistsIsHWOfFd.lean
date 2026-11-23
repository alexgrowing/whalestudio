import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem exists_isHW_of_fd : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act →
    (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∀ U : Submodule ℂ V, U ≠ ⊥ →
    FiniteDimensional ℂ U → KStable act U → ∃ (μ : Ix p q → ℚ) (v : V), v ∈ U ∧ IsHW act μ v := by
  intro p q V _ _ act hL hd U hU hfd hK
  exact GlobalTheory.BlockReps.exists_hw (fun Y Z _ _ => hL Y Z) hK (fun v _ => hd v) hU

end GlobalTheory.HoweR
