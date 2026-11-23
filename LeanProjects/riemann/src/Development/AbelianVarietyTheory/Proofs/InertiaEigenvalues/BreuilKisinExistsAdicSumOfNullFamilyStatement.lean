import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) → ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev := by
  first | exact @GlobalTheory.BSP.exists_sum_null_ev | exact GlobalTheory.BSP.exists_sum_null_ev | (intros; apply GlobalTheory.BSP.exists_sum_null_ev <;> assumption)
