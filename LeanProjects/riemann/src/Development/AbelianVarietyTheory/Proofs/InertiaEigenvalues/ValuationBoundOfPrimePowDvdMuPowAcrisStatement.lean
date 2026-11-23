import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n : ℕ) (x : ℤ_[l]), x ≠ 0 → (l : Per.Acris l) ^ n ∣ ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) x) → (l - 1) * n ≤ (l - 1) * x.valuation + 2 * j := by
  first | exact @GlobalTheory.AcrisMuBound.main | exact GlobalTheory.AcrisMuBound.main | (intros; apply GlobalTheory.AcrisMuBound.main <;> assumption)
