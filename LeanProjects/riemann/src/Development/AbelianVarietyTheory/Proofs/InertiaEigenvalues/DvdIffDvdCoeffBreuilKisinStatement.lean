import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  first | exact @GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c | exact GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c | (intros; apply GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c <;> assumption)
