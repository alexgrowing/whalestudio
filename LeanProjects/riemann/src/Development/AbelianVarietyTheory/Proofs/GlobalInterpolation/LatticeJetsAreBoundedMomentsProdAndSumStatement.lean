import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ω : ℂ_[q]) (Λ : AddSubgroup V), (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∏ j, G j z) ∧ ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) → (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  first | exact @GlobalTheory.MomN.latInt_prod_sum | exact GlobalTheory.MomN.latInt_prod_sum | (intros; apply GlobalTheory.MomN.latInt_prod_sum <;> assumption)
