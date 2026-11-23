import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLie
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | exact GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | (intros; apply GlobalTheory.UnitLemma.OrbitAll.identity_of_lie <;> assumption)
