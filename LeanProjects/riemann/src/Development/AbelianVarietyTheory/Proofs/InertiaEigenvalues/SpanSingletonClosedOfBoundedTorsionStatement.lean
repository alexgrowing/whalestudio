import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSingletonClosedOfBoundedTorsion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {d}) A → ∀ x : A, (∀ n : ℕ, ∃ z, x - d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n) → x ∈ Ideal.span {d} := by
  first | exact @GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | exact GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | (intros; apply GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion <;> assumption)
