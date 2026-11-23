import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_cyclotomic_endo_eq_frobenius_laurent : ∀ (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l] (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → ∀ a : O⟦X⟧, ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  first | exact @GlobalTheory.RedPhiProof.red_phi | exact GlobalTheory.RedPhiProof.red_phi | (intros; apply GlobalTheory.RedPhiProof.red_phi <;> assumption)
