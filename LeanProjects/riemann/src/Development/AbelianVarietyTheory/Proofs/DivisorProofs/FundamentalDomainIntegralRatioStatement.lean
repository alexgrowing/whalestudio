import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralRatio
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_integral_ratio : ∀ {g : ℕ} (M M' : Submodule ℤ (Fl g)), IsLat M → IsLat M' → M ≤ M' → ∀ (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∃ c : ℝ, c ≠ 0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ψ : Fl g → V), Continuous ψ → (∀ l ∈ M', ∀ x, ψ (x + l) = ψ x) → ∀ D' : Set (Fl g), IsAddFundamentalDomain M' D' volume → ∫ x in D, ψ x = c • ∫ x in D', ψ x := by
  first | exact @GlobalTheory.setIntegral_fundamentalDomain_sublattice | exact GlobalTheory.setIntegral_fundamentalDomain_sublattice | (intros; apply GlobalTheory.setIntegral_fundamentalDomain_sublattice <;> assumption)
