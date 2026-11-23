import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧ (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj = τ.map (fun z => (z.im : ℂ)) ∧ ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧ spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  first | exact @GlobalTheory.SiegelAction.symplectic_action | exact GlobalTheory.SiegelAction.symplectic_action | (intros; apply GlobalTheory.SiegelAction.symplectic_action <;> assumption)
