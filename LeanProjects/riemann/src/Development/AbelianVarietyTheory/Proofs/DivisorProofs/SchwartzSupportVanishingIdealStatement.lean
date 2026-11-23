import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSupportVanishingIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_support_vanishing_ideal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, ‖ψ0 x‖ = 1) → ψ0 ≠ 1 → ∀ (I : Set (Y × Y')) (φ : Matrix Y Y' k → ℂ), φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k) →
    (∀ t : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t r q = 0) → φ t = 0) →
    φ ∈ Submodule.span ℂ {f | ∃ z : Matrix Y Y' k, (∀ r q, (r, q) ∉ I → z r q = 0) ∧
      ∃ φ' ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), f = (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ' t) - φ'} := by
  first | exact @GlobalTheory.SBVanish.mem_span_of_vanish | exact GlobalTheory.SBVanish.mem_span_of_vanish | (intros; apply GlobalTheory.SBVanish.mem_span_of_vanish <;> assumption)
