import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumTransverseLagrangianLocalField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
open ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vacuum_transverseLagrangian_localField : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ f₀ ∈ GlobalTheory.WeilM.SB (κ → k), f₀ ≠ 0 ∧
      (∀ u : Matrix (Fin n) (Fin d) k, (∀ r q, u r q ∈ 𝒪[k]) → GlobalTheory.WeilM.schr ψ0 (wT u) f₀ = f₀) ∧
      (∀ z : Matrix (Fin n) (Fin d) k, (∀ r q, z r q ∈ 𝒪[k]) → GlobalTheory.WeilM.schr ψ0 (wM z) f₀ = f₀) := by
  first | exact @GlobalTheory.LagVac.exists_vacuum | exact GlobalTheory.LagVac.exists_vacuum | (intros; apply GlobalTheory.LagVac.exists_vacuum <;> assumption)
