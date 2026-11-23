import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
open Matrix

namespace GlobalTheory.CompanionTheory.OpenCore

theorem exists_open_core {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K S : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hSo : IsOpen (S : Set G)) :
    ∃ K₁ : Subgroup G, K₁ ≤ K ∧ IsOpen (K₁ : Set G) ∧ K₁ ≤ S ∧ K₁.relIndex K ≠ 0 ∧
      ∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((S.subgroupOf K : Subgroup K) : Set K) := hSo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ S.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (S.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (((S.subgroupOf K).normalCore : Subgroup K) : Set K) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((S.subgroupOf K).normalCore_isClosed ((S.subgroupOf K).isClosed_of_isOpen hHo))
  refine ⟨(S.subgroupOf K).normalCore.map K.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ hN
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hx)
  · have e : ((S.subgroupOf K).normalCore.map K.subtype).relIndex K = (S.subgroupOf K).normalCore.index := by
      rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K)]
    rw [e]
    exact (inferInstance : (S.subgroupOf K).normalCore.FiniteIndex).1
  · rintro κ hκ _ ⟨x, hx, rfl⟩
    refine ⟨⟨κ, hκ⟩ * x * (⟨κ, hκ⟩ : K)⁻¹, (Subgroup.normalCore_normal _).conj_mem x hx ⟨κ, hκ⟩, ?_⟩
    simp

theorem exists_open_normal_subgroup_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧
      ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  obtain ⟨S, hSo, hSU⟩ := GlobalTheory.SmGL.ProdIrr.exists_openSubgroup_GL U hU
  obtain ⟨K₁, h1, h2, h3, h4, h5⟩ := exists_open_core (GlobalTheory.SplitWeil.KO k (Fin n)) S
    GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO hSo
  exact ⟨K₁, h1, h2, fun g hg => hSU g (h3 hg), h4, h5⟩

end GlobalTheory.CompanionTheory.OpenCore
