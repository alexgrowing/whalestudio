import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeLocalizedOfTorsionBounded
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded : ∀ (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N] (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P), SemiBC u → ∀ (L : P →ₗ[A] N) (n a : ℕ), (∀ y, L y = 0 → t ^ n • y = 0) → (∀ x, ∃ y, L y = t ^ n • x) → ∀ Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N, (∀ x, IsFrac t (Φ x) (L (u x)) a) → SemiBC Φ := by
  first | exact @GlobalTheory.BSP.semiBC_localized | exact GlobalTheory.BSP.semiBC_localized | (intros; apply GlobalTheory.BSP.semiBC_localized <;> assumption)
