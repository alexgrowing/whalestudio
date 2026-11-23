import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N), (∀ x, u' x = u x) → (SemiBC u ↔ IsBaseChange B u') := by
  first | exact @GlobalTheory.BSP.semiBC_iff_isBaseChange | exact GlobalTheory.BSP.semiBC_iff_isBaseChange | (intros; apply GlobalTheory.BSP.semiBC_iff_isBaseChange <;> assumption)
