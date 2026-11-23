import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l), ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  first | exact @GlobalTheory.SeedSec.o_eq_aDp_wA | exact GlobalTheory.SeedSec.o_eq_aDp_wA | (intros; apply GlobalTheory.SeedSec.o_eq_aDp_wA <;> assumption)
