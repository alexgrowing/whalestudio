import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushout
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_and_cover_prismHom_of_pushout : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  first | exact @GlobalTheory.BSP.stable_cover_of_isPO | exact GlobalTheory.BSP.stable_cover_of_isPO | (intros; apply GlobalTheory.BSP.stable_cover_of_isPO <;> assumption)
