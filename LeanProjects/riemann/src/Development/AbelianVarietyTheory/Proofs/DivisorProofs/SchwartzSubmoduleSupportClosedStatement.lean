import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleSupportClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_submodule_support_closed : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, ‖ψ0 x‖ = 1) → ψ0 ≠ 1 → ∀ (I : Set (Y × Y')) (S : Submodule ℂ (Matrix Y Y' k → ℂ)),
    S ≤ GlobalTheory.WeilM.SB (Matrix Y Y' k) →
    (∀ φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), (∀ t : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t r q = 0) → φ t = 0) → φ ∈ S) →
    (∀ x : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → x r q = 0) → ∀ φ ∈ S, (fun t => φ (t + x)) ∈ S) →
    (∀ z : Matrix Y Y' k, ∀ φ ∈ S, (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ t) ∈ S) →
    ∀ φ₀ ∈ S, ∀ t₀ : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t₀ r q = 0) → φ₀ t₀ ≠ 0 → S = GlobalTheory.WeilM.SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.SBRestrict.eq_SB_of_restrict | exact GlobalTheory.SBRestrict.eq_SB_of_restrict | (intros; apply GlobalTheory.SBRestrict.eq_SB_of_restrict <;> assumption)
