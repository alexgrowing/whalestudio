import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTermStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_conjClasses_centralizer_orbits_eq_pairOrbits : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  first | exact @GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits | exact GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits | (intros; apply GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits <;> assumption)
