import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

namespace GlobalTheory

theorem pv_add_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ) (ι : Type) (s : Finset ι) (Kf : ι → Set (Matrix (Fin n) (Fin d) k)) (B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)), B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d → (∀ i ∈ s, IsClopen (Kf i)) → (↑s : Set ι).PairwiseDisjoint Kf → B₂ = (⋃ i ∈ s, Kf i) → pv Bf B₁ B₂ = ∑ i ∈ s, pv Bf B₁ (Kf i) := by
  intro k _ _ _ _ n d Bf ι s Kf B₁ B₂ h₂ hcl hdis hcov
  classical
  by_cases h₁ : B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d
  swap
  · have h0 : ∀ X : Set (Matrix (Fin n) (Fin d) k), pv Bf B₁ X = 0 := fun X => by
      rw [pv, dif_neg (fun h => h₁ h.1)]
    rw [h0, Finset.sum_eq_zero (fun i _ => h0 _)]
  have hsub : ∀ i ∈ s, Kf i ⊆ B₂ := fun i hi x hx => by
    rw [hcov]; exact Set.mem_biUnion hi hx
  have hm : ∀ i ∈ s, (Kf i).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := by
    intro i hi
    refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
    · exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (hcl i hi)).isLocallyConstant
    · refine h₂.1.2.mono ?_
      intro x hx
      have hx' : x ∈ Kf i := by
        by_contra h; exact hx (Set.indicator_of_notMem h _)
      have : x ∈ B₂ := hsub i hi hx'
      simp [Set.indicator_of_mem this]
      exact this
    · have hY2 := h₂.2 Y hY
      have : Y ∉ B₂ := fun h => by simp [Set.indicator_of_mem h] at hY2
      exact Set.indicator_of_notMem (fun h => this (hsub i hi h)) _
  let Φ : ι → fullRk k n d := fun i => if h : i ∈ s then ⟨_, hm i h⟩ else 0
  have hΦ : ∀ i ∈ s, (Φ i).1 = (Kf i).indicator 1 := fun i hi => by simp [Φ, dif_pos hi]
  have hsum : (∑ i ∈ s, Φ i).1 = B₂.indicator 1 := by
    rw [Submodule.coe_sum, hcov, Finset.indicator_biUnion s Kf hdis]
    funext x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i hi => by rw [hΦ i hi])
  rw [pv_eq Bf ⟨_, h₁⟩ (∑ i ∈ s, Φ i) rfl hsum, map_sum]
  exact Finset.sum_congr rfl (fun i hi => (pv_eq Bf ⟨_, h₁⟩ (Φ i) rfl (hΦ i hi)).symm)

end GlobalTheory
