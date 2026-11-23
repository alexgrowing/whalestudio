import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite → (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) → Φ B *ᵥ v ∈ S := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | exact GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift <;> assumption)
