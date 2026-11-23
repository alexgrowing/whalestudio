import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A) (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)), ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  first | exact @GlobalTheory.BSP.env_isPO | exact GlobalTheory.BSP.env_isPO | (intros; apply GlobalTheory.BSP.env_isPO <;> assumption)
