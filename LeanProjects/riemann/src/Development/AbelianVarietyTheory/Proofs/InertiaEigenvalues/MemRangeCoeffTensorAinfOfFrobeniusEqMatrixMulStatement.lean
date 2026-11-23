import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeCoeffTensorAinfOfFrobeniusEqMatrixMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_coeffTensorAinf_of_frobenius_eq_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {n : Type} [Fintype n] (v : n → OW l O) (Y : Matrix n n (OA l O)), (∀ i, frobOW l O (v i) = (Y.map (inclO l O) *ᵥ v) i) → ∀ i, v i ∈ (inclO l O).range := by
  first | exact @GlobalTheory.FrobIntTensor.mem_range_inclO | exact GlobalTheory.FrobIntTensor.mem_range_inclO | (intros; apply GlobalTheory.FrobIntTensor.mem_range_inclO <;> assumption)
