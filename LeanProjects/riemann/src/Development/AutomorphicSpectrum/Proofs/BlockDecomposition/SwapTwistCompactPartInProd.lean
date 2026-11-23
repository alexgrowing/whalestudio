import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitUnit

theorem compact_zpowers_fst {H : Type} [Group H] [TopologicalSpace H] [T2Space H] (t : H × H)
    (hc : IsCompact (closure (Subgroup.zpowers t : Set (H × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set H)) := by
  have hi : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (H × H))) := hc.image continuous_fst
  refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
  rintro x ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure ⟨k, rfl⟩, ?_⟩
  simp

theorem main : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := by
  intro H _ _ _ _ σ K d d' _ hσ hK hd hd' hcpt hsurj
  refine ⟨?_, ?_⟩
  · rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    obtain ⟨h₁, h₂⟩ := (mem_twCent_swTw σ hσ d d' t).1 ht
    have hg : t.1 ∈ K :=
      hcpt (Subgroup.subset_closure ⟨h₁, compact_zpowers_fst t hc⟩)
    refine Subgroup.mem_prod.2 ⟨hg, ?_⟩
    rw [h₂]
    exact K.mul_mem (K.mul_mem hd' (hK _ hg)) (K.inv_mem hd')
  · rintro ⟨x₁, x₂⟩ hy
    have hy' := Subgroup.mem_prod.1 hy
    have hz₁ : x₁⁻¹ * d * σ x₂ ∈ K := by simpa using hy'.1
    have hz₂ : x₂⁻¹ * d' * σ x₁ ∈ K := by simpa using hy'.2
    have hN : x₁⁻¹ * (d * σ d') * MonoidHom.id H x₁ ∈ K := by
      have e : x₁⁻¹ * (d * σ d') * MonoidHom.id H x₁ = (x₁⁻¹ * d * σ x₂) * σ (x₂⁻¹ * d' * σ x₁) := by
        simp only [map_mul, map_inv, hσ, MonoidHom.id_apply]
        group
      rw [e]
      exact K.mul_mem hz₁ (hK _ hz₂)
    obtain ⟨g, hg, hk₁⟩ := hsurj x₁ hN
    refine ⟨(g, d' * σ g * d'⁻¹), (mem_twCent_swTw σ hσ d d' _).2 ⟨hg, rfl⟩,
      (g⁻¹ * x₁, d' * σ (g⁻¹ * x₁) * (x₂⁻¹ * d' * σ x₁)⁻¹), ?_, ?_⟩
    · exact Subgroup.mem_prod.2 ⟨hk₁, K.mul_mem (K.mul_mem hd' (hK _ hk₁)) (K.inv_mem hz₂)⟩
    · ext
      · simp
      · simp only [Prod.mk_mul_mk, map_mul, map_inv]
        group

end GlobalTheory.CompanionTheory.SplitUnit

end
