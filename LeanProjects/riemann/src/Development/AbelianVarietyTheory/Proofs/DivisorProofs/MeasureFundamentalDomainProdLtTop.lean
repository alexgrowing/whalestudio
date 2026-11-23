import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory

theorem isFundamentalDomain_stdDom_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂] (μ : Measure (G₁ × G₂)) :
    IsFundamentalDomain (Γ₁.prod Γ₂) (GlobalTheory.AutomorphicL2Unitary.stdDom Γ₁ ×ˢ GlobalTheory.AutomorphicL2Unitary.stdDom Γ₂) μ := by
  refine .mk' ((GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₁).prod (GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₂)).nullMeasurableSet ?_
  rintro ⟨a, b⟩
  obtain ⟨γ₁, h₁, u₁⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₁ a
  obtain ⟨γ₂, h₂, u₂⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₂ b
  refine ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨c, d⟩, hcd⟩ ⟨hc, hd⟩
  have e₁ := u₁ ⟨c, (Subgroup.mem_prod.1 hcd).1⟩ hc
  have e₂ := u₂ ⟨d, (Subgroup.mem_prod.1 hcd).2⟩ hd
  ext <;> simp [← e₁, ← e₂]

theorem measure_fundamentalDomain_prod_lt_top : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ₁ Γ₂ _ _ h₁ h₂ μ hμ 𝓕 h𝓕
  have hd := GlobalTheory.isFundamentalDomain_stdDom_prod Γ₁ Γ₂ μ
  haveI : Countable (Γ₁.prod Γ₂) := by
    have : Function.Injective (fun γ : Γ₁.prod Γ₂ => ((⟨(γ : G₁ × G₂).1, (Subgroup.mem_prod.1 γ.2).1⟩ : Γ₁),
      (⟨(γ : G₁ × G₂).2, (Subgroup.mem_prod.1 γ.2).2⟩ : Γ₂))) := by
      rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      ext <;> simp [h.1, h.2]
    exact this.countable
  rw [h𝓕.measure_eq hd]
  have hp : (Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂) |>.IsHaarMeasure := inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂)),
    Measure.smul_apply, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have a₁ := h₁ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₁ Measure.haar)
  have a₂ := h₂ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₂ Measure.haar)
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top a₁.lt_top a₂.lt_top)

end GlobalTheory
