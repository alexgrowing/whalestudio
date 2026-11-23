import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfJointEigenvalue
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_hom_of_joint_eigenvalue : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ), v.Integers O → ∀ (ρ : Λ →+* Matrix (Fin h) (Fin h) O) (χ : Λ → C), (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) ≠ ⊥ → ∃ σ : Λ →+* O, ∀ a, algebraMap O C (σ a) = χ a := by
  first | exact @GlobalTheory.jointEigen_ringHom_toIntegers | exact GlobalTheory.jointEigen_ringHom_toIntegers | (intros; apply GlobalTheory.jointEigen_ringHom_toIntegers <;> assumption)
