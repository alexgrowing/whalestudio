import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholze
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze : GlobalTheory.Published.BhattScholzeIntegral → ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  first | exact @GlobalTheory.HWL.exists_hw_fon_cmp_of_integral | exact GlobalTheory.HWL.exists_hw_fon_cmp_of_integral | (intros; apply GlobalTheory.HWL.exists_hw_fon_cmp_of_integral <;> assumption)
