import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsMore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

theorem exists_mul_mem_adjoin_of_isLocalization {S : Type*} [CommRing S] {S' : Type*} [CommRing S'] [Algebra S S']
    {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra S' Ω] [IsScalarTower S S' Ω] (M : Submonoid S)
    [IsLocalization M S'] (s : Set Ω) {w : Ω} (hw : w ∈ Algebra.adjoin S' s) :
    ∃ m ∈ M, algebraMap S Ω m * w ∈ Algebra.adjoin S s := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, M.one_mem, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M r
    refine ⟨m, m.2, ?_⟩
    have e : algebraMap S Ω m * algebraMap S' Ω (IsLocalization.mk' S' a m) = algebraMap S Ω a := by
      rw [IsScalarTower.algebraMap_apply S S' Ω, IsScalarTower.algebraMap_apply S S' Ω a, ← map_mul,
        IsLocalization.mk'_spec']
    rw [e]
    exact Subalgebra.algebraMap_mem _ a
  | add x y _ _ hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
    have e : algebraMap S Ω (m₁ * m₂) * (x + y) =
        algebraMap S Ω m₂ * (algebraMap S Ω m₁ * x) + algebraMap S Ω m₁ * (algebraMap S Ω m₂ * y) := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) h₁) (mul_mem (Subalgebra.algebraMap_mem _ _) h₂)
  | mul x y _ _ hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
    have e : algebraMap S Ω (m₁ * m₂) * (x * y) = (algebraMap S Ω m₁ * x) * (algebraMap S Ω m₂ * y) := by
      rw [map_mul]; ring
    rw [e]
    exact mul_mem h₁ h₂

theorem SecOverLocalization.proof : SecOverLocalization.Statement := by
  intro S _ K _ ι _ Ω _ _ y β S' _ _ _ _ M _
  classical
  apply le_antisymm
  · intro z hz
    simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule] at hz

    have key : ∀ c : ∀ k, ι k, ∃ m ∈ M, ∀ _ : ∀ k, y ⟨k, c k⟩ ≠ 0,
        algebraMap S Ω m * (z * ∏ k, y ⟨k, c k⟩ ^ (-β k)) ∈ chartRingOver S y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      · obtain ⟨m, hm, h⟩ := exists_mul_mem_adjoin_of_isLocalization (S' := S') M _ (hz c hc)
        exact ⟨m, hm, fun _ => h⟩
      · exact ⟨1, M.one_mem, fun h => absurd h hc⟩
    choose m hm hmz using key
    set m₀ := ∏ c, m c with hm₀
    have hm₀M : m₀ ∈ M := prod_mem fun c _ => hm c

    have hmem : algebraMap S Ω m₀ * z ∈ secOver S y β := by
      simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
        Subalgebra.mem_toSubmodule]
      intro c hc
      have e : algebraMap S Ω m₀ * z * ∏ k, y ⟨k, c k⟩ ^ (-β k) =
          algebraMap S Ω (∏ c' ∈ Finset.univ.erase c, m c') *
            (algebraMap S Ω (m c) * (z * ∏ k, y ⟨k, c k⟩ ^ (-β k))) := by
        rw [hm₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), map_mul]; ring
      rw [e]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (hmz c hc)

    obtain ⟨u, hu⟩ := IsLocalization.map_units S' (⟨m₀, hm₀M⟩ : M)
    have hz' : z = (↑u⁻¹ : S') • (algebraMap S Ω m₀ * z) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply S S' Ω, ← mul_assoc, ← map_mul]
      have : (↑u⁻¹ : S') * algebraMap S S' m₀ = 1 := by
        rw [show algebraMap S S' m₀ = (u : S') from hu.symm, Units.inv_mul]
      rw [this, map_one, one_mul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · refine Submodule.span_le.mpr fun z hz => ?_
    simp only [SetLike.mem_coe, secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule] at hz ⊢
    intro c hc
    have hle : chartRingOver S y c ≤ (chartRingOver S' y c).restrictScalars S :=
      Algebra.adjoin_le fun x hx => (Algebra.subset_adjoin hx : x ∈ Algebra.adjoin S' _)
    exact hle (hz c hc)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
