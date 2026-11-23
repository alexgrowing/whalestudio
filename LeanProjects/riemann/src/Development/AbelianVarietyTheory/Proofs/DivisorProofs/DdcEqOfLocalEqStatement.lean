import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_eq_of_local_eq : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (x : A.Pt) (f : V n → Alt n), A.loc α x.1.1 =ᶠ[𝓝 x.crd] f → A.ddc α x = kappa • delAt (dbarAt f) x.crd := by
  first | exact @GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq | exact GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq | (intros; apply GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq <;> assumption)
