import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowOfMulMemPowBoundedTorsion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_pow_of_mul_mem_pow_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → ∀ (n : ℕ) (z : A), d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (2 * (n + N + 1)) → z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := by
  first | exact @GlobalTheory.div_d_continuous_of_bdd_ltorsion | exact GlobalTheory.div_d_continuous_of_bdd_ltorsion | (intros; apply GlobalTheory.div_d_continuous_of_bdd_ltorsion <;> assumption)
