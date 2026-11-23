import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAutSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscrete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.UnipFD

open Pointwise in

theorem measure_fd_lt_top_of_cocompact {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) [μ.IsHaarMeasure] [SMulInvariantMeasure Γ G μ] {D : Set G}
    (hD : IsFundamentalDomain Γ D μ) : μ D < ⊤ := by
  have hsub : D ⊆ ⋃ γ : Γ, ((γ • K) ∩ D) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hk
  calc μ D ≤ μ (⋃ γ : Γ, ((γ • K) ∩ D)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ D) := measure_iUnion_le _
    _ = μ K := (hD.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}
    (Y : Spc F E n) (H : Plane E n n₁),
    (∃ K : Set (unip σ Y H), IsCompact K ∧ ∀ u : unip σ Y H, ∃ γ ∈ (ratU σ Y.J).subgroupOf (unip σ Y H), γ * u ∈ K) →
    ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ n n₁ Y H hcpt
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ Y.J
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ Y H) := (GlobalTheory.UnipCT.isClosed_unip σ Y H).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) Y.J
  set Γ := (ratU σ Y.J).subgroupOf (unip σ Y H) with hΓ
  haveI hcount : Countable Γ :=
    Function.Injective.countable (f := fun g : Γ => (⟨g.1.1, g.2⟩ : ratU σ Y.J))
      fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh
  haveI := (GlobalTheory.RatUDisc.countable_discrete_ratU F E σ n Y.J).2
  haveI hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective (f := fun g : Γ => (⟨g.1.1, g.2⟩ : ratU σ Y.J))
      (by fun_prop) (fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh)
  obtain ⟨K, hK, hcov⟩ := hcpt
  haveI : SMulInvariantMeasure Γ (unip σ Y H) (Measure.haar : Measure (unip σ Y H)) :=
    ⟨fun c s _ => measure_preimage_mul _ (c : unip σ Y H) s⟩
  obtain ⟨D, hD⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain Γ (Measure.haar : Measure (unip σ Y H))
  have h0 : Measure.haar D ≠ 0 := hD.measure_ne_zero (NeZero.ne _)
  have h1 : Measure.haar D ≠ ⊤ := (measure_fd_lt_top_of_cocompact Γ hK hcov _ hD).ne
  refine ⟨(Measure.haar D)⁻¹ • Measure.haar, D,
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
      hD.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]

end GlobalTheory.UnipFD
