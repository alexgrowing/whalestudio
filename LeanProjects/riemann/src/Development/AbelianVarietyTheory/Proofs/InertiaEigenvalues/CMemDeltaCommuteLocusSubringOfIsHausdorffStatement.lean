import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemDeltaCommuteLocusSubringOfIsHausdorff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C, ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  first | exact @GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | exact GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | (intros; apply GlobalTheory.BSP.C_mem_δLocus_of_hausdorff <;> assumption)
