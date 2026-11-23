import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroNeZeroOfWittFrobeniusExpandDvd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_zero_ne_zero_of_wittFrobenius_expand_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul | exact GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul | (intros; apply GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul <;> assumption)
