import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominanceOrderLEOfMemSpanWeightVectorsDominatedB
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ), IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  first | exact @GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle | exact GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle <;> assumption)
