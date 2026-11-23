import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedOrbitSumEqPairOrbitSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTermStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitSum_eq_pairOrbitSum : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = pairSum F := by
  first | exact @GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum | exact GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum | (intros; apply GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum <;> assumption)
