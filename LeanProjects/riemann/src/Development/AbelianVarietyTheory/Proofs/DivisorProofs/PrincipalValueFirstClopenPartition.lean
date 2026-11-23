import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

namespace GlobalTheory.NormalCore

theorem indOne_isLocallyConstant {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem pv_sum_left_clopen (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ) (ι : Type) (s : Finset ι)
    (Kf : ι → Set (Matrix (Fin n) (Fin d) k)) (B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)) :
    B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d → (∀ i ∈ s, IsClopen (Kf i)) →
      (↑s : Set ι).PairwiseDisjoint Kf → B₁ = (⋃ i ∈ s, Kf i) → pv Bf B₁ B₂ = ∑ i ∈ s, pv Bf (Kf i) B₂ := by
  classical
  intro h₁ hcl hdis hB
  by_cases h₂ : B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d
  swap
  · have e : ∀ B : Set (Matrix (Fin n) (Fin d) k), pv Bf B B₂ = 0 := fun B => by
      rw [pv, dif_neg (fun h => h₂ h.2)]
    simp [e]
  have hsub : ∀ i ∈ s, Kf i ⊆ B₁ := fun i hi x hx => by
    rw [hB]; exact Set.mem_biUnion hi hx
  have mem : ∀ i ∈ s, (Kf i).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := by
    intro i hi
    refine ⟨⟨indOne_isLocallyConstant (hcl i hi), ?_⟩, fun Y hY => ?_⟩
    · refine h₁.1.2.mono ?_
      intro x hx
      rw [Function.mem_support, Set.indicator_apply_ne_zero] at hx ⊢
      exact ⟨hsub i hi hx.1, one_ne_zero⟩
    · have h0 := h₁.2 Y hY
      have : Y ∉ B₁ := fun hY' => by simp [Set.indicator_of_mem hY'] at h0
      exact Set.indicator_of_notMem (fun hK => this (hsub i hi hK)) _
  let Ψ : ι → fullRk k n d := fun i => if hi : i ∈ s then ⟨_, mem i hi⟩ else 0
  have hΨ : ∀ i ∈ s, (Ψ i).1 = (Kf i).indicator 1 := fun i hi => by simp [Ψ, dif_pos hi]
  have hsum : (∑ i ∈ s, Ψ i).1 = B₁.indicator 1 := by
    rw [Submodule.coe_sum, Finset.sum_congr rfl hΨ, hB, Finset.indicator_biUnion s Kf hdis]
    ext x; simp [Finset.sum_apply]
  rw [pv_eq Bf (∑ i ∈ s, Ψ i) ⟨_, h₂⟩ hsum rfl, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i hi => (pv_eq Bf (Ψ i) ⟨_, h₂⟩ (hΨ i hi) rfl).symm

end GlobalTheory.NormalCore
