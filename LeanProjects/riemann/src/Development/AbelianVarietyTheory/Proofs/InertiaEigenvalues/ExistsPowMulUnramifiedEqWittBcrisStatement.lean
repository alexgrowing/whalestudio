import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcris
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  first | exact @GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB | exact GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB | (intros; apply GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB <;> assumption)
