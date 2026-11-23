import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfUnitFrobeniusEqMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  first | exact @GlobalTheory.Per.frobenius_eq_mul_solvable | exact GlobalTheory.Per.frobenius_eq_mul_solvable | (intros; apply GlobalTheory.Per.frobenius_eq_mul_solvable <;> assumption)
