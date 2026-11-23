import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismPushoutModAdicPow_universal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → ∀ (Q : Obj l R) (a : Hom C Q) (b : Hom B' Q), a.comp h = b.comp k → ∃! c : Hom C' Q, c.comp k' = a ∧ c.comp h' = b := by
  first | exact @GlobalTheory.BSP.PoUniv.isPO_univ | exact GlobalTheory.BSP.PoUniv.isPO_univ | (intros; apply GlobalTheory.BSP.PoUniv.isPO_univ <;> assumption)
