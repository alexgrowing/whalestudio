import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootsActFaithfullyLaurent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_roots_act_faithfully_laurent : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩), (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧ Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c := by
  first | exact @GlobalTheory.DeltaInv.main | exact GlobalTheory.DeltaInv.main | (intros; apply GlobalTheory.DeltaInv.main <;> assumption)
