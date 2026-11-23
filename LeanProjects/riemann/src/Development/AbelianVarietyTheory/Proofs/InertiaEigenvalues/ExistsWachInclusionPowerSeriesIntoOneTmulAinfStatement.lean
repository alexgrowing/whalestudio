import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachInclusionPowerSeriesIntoOneTmulAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachInclusion_powerSeries_into_one_tmul_ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧ io PowerSeries.X = WittVector.teichmuller l (AI.εroot s) - 1 ∧ ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w := by
  first | exact @GlobalTheory.PrismS.IoDescent.main | exact GlobalTheory.PrismS.IoDescent.main | (intros; apply GlobalTheory.PrismS.IoDescent.main <;> assumption)
