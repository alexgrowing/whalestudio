import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) := by
  first | exact @GlobalTheory.BKReal.IBInj.iB_injective_finExt | exact GlobalTheory.BKReal.IBInj.iB_injective_finExt | (intros; apply GlobalTheory.BKReal.IBInj.iB_injective_finExt <;> assumption)
