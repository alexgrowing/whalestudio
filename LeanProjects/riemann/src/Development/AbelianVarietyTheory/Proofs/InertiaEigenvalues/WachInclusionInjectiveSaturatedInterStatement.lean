import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusion_injective_saturated_inter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → Function.Injective I.ioE ∧ (∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) ∧ (∀ (x : R.EE) (y : RW LL), I.ioE x = ((l : ℕ) : RW LL) * y → ∃ x', x = ((l : ℕ) : R.EE) * x') ∧ ∀ x : R.EE, (∃ y, inclR LL y = I.ioE x) → ∃ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), algebraMap _ R.EE a = x := by
  first | exact @GlobalTheory.IoInj.ioE_injective_saturated_inter | exact GlobalTheory.IoInj.ioE_injective_saturated_inter | (intros; apply GlobalTheory.IoInj.ioE_injective_saturated_inter <;> assumption)
