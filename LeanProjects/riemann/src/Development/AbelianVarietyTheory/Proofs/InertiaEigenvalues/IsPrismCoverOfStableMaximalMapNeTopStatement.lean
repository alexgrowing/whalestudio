import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverOfStableMaximalMapNeTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrismCover_of_stable_maximal_map_ne_top : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Stable h → (∀ 𝔪 : Ideal B.A, 𝔪.IsMaximal → 𝔪.map h.f ≠ ⊤) → Cover h := by
  first | exact @GlobalTheory.BSP.cover_of_stable_of_map_ne_top | exact GlobalTheory.BSP.cover_of_stable_of_map_ne_top | (intros; apply GlobalTheory.BSP.cover_of_stable_of_map_ne_top <;> assumption)
