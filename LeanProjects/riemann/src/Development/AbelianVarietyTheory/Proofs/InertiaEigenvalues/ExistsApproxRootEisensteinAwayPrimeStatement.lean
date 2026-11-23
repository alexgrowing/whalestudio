import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_root_eisenstein_away_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ), ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧ bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  first | exact @GlobalTheory.BSP.BK.exists_approx_root | exact GlobalTheory.BSP.BK.exists_approx_root | (intros; apply GlobalTheory.BSP.BK.exists_approx_root <;> assumption)
