import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralFinsetSum
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_integral_finset_sum : ∀ {g : ℕ} (M : Submodule ℤ (Fl g)), IsLat M → ∀ (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {ι : Type} (s : Finset ι) (ψ : ι → Fl g → V), (∀ i ∈ s, Continuous (ψ i)) → (∀ i ∈ s, ∀ l ∈ M, ∀ x, ψ i (x + l) = ψ i x) → ∫ x in D, ∑ i ∈ s, ψ i x = ∑ i ∈ s, ∫ x in D, ψ i x := by
  first | exact @GlobalTheory.setIntegral_finset_sum_of_periodic | exact GlobalTheory.setIntegral_finset_sum_of_periodic | (intros; apply GlobalTheory.setIntegral_finset_sum_of_periodic <;> assumption)
