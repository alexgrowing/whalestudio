import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrincipalIdealRingWittPowerSeriesAwayPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrincipalIdealRing_wittPowerSeries_away_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  first | exact @GlobalTheory.BSP.isPrincipalIdealRing_away_l | exact GlobalTheory.BSP.isPrincipalIdealRing_away_l | (intros; apply GlobalTheory.BSP.isPrincipalIdealRing_away_l <;> assumption)
