import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_stabilizerWeightedPairTerm : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) => pairTerm F (Quotient.out o))).Finite := by
  first | exact @GlobalTheory.OrbitUnfold.finite_support_pairTerm | exact GlobalTheory.OrbitUnfold.finite_support_pairTerm | (intros; apply GlobalTheory.OrbitUnfold.finite_support_pairTerm <;> assumption)
