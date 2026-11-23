import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.measure_fundamentalDomain_prod_lt_top | exact GlobalTheory.measure_fundamentalDomain_prod_lt_top | (intros; apply GlobalTheory.measure_fundamentalDomain_prod_lt_top <;> assumption)
