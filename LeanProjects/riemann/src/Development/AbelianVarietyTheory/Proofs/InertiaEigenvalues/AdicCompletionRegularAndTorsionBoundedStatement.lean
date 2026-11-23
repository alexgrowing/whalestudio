import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionRegularAndTorsionBounded
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_completion_regular_and_torsion_bounded : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (d : L) (N : ℕ), d ∈ nonZeroDivisors L → (∀ (x : L) (m : ℕ), (l : L) ^ m * x ∈ Ideal.span {d} → (l : L) ^ N * x ∈ Ideal.span {d}) → IsCompl i (Ideal.span {(l : L)} ⊔ Ideal.span {d}) → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  first | exact @GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded | exact GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded | (intros; apply GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded <;> assumption)
