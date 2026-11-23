import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleValue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratifiedPhiModuleValue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module B.A N), Nonempty (Eval S B N) := by
  first | exact @GlobalTheory.BSP.exists_eval | exact GlobalTheory.BSP.exists_eval | (intros; apply GlobalTheory.BSP.exists_eval <;> assumption)
