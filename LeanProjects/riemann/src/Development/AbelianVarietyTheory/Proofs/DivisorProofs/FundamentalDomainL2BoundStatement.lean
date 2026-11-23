import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_L2_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ, (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) → ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧ ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.QuotLocInt.integrableOn_compact | exact GlobalTheory.QuotLocInt.integrableOn_compact | (intros; apply GlobalTheory.QuotLocInt.integrableOn_compact <;> assumption)
