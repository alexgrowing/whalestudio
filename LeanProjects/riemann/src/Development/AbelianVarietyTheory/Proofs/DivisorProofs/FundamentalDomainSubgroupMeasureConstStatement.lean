import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainSubgroupMeasureConst
import Mathlib

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_subgroup_measure_const : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] (Γ : Subgroup G) [Countable Γ], Γ ≤ H → (∀ γ ∈ Γ.subgroupOf H, MeasurePreserving (fun p : H => γ * p) ν ν) → ∀ 𝓓 : Set G, IsFundamentalDomain Γ 𝓓 μ → ∀ E : Set H, IsFundamentalDomain (Γ.subgroupOf H) E ν → ∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ 𝓓} = ν E := by
  first | exact @GlobalTheory.ae_measure_subgroup_slice_fundamentalDomain | exact GlobalTheory.ae_measure_subgroup_slice_fundamentalDomain | (intros; apply GlobalTheory.ae_measure_subgroup_slice_fundamentalDomain <;> assumption)
