import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulEigenspaceFinrankOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_mul_eigenspace_finrank_one : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  first | exact @GlobalTheory.RegEigen.eig_leftMulMatrix_finrank | exact GlobalTheory.RegEigen.eig_leftMulMatrix_finrank | (intros; apply GlobalTheory.RegEigen.eig_leftMulMatrix_finrank <;> assumption)
