import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMemIdealPowOfXPowMulMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ), ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S, (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  first | exact @GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | exact GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | (intros; apply GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem <;> assumption)
