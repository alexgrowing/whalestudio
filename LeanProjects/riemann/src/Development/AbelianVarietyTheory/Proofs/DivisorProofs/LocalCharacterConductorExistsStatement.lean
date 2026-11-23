import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_conductor_exists : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∃ c : k, c ≠ 0 ∧ ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (c * (x * y)) = 1) ↔ x ∈ 𝒪[k] := by
  first | exact @GlobalTheory.CondRescale.exists_rescale_conductor_integers | exact GlobalTheory.CondRescale.exists_rescale_conductor_integers | (intros; apply GlobalTheory.CondRescale.exists_rescale_conductor_integers <;> assumption)
