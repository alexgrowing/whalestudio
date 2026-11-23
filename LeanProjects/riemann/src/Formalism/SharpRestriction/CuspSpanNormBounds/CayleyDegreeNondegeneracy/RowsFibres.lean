import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsRpowPow

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.HermitianLatticeCounting

open Classical in

theorem rows_fibres {Pr κ : Type} (S : Finset Pr) (c₁ c₂ : Pr → κ) (F : Pr → ℝ) :
    ∑ p ∈ S, F p = ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), F p := by
  rw [← Finset.sum_product', ← Finset.sum_fiberwise_of_maps_to (g := fun p => (c₁ p, c₂ p))
    (t := S.image c₁ ×ˢ S.image c₂) (fun p hp => Finset.mem_product.2
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩)]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun p _ => ?_
  rw [Prod.ext_iff]

open Classical in

theorem weighted_sum_le {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p ≤ M * N x y)
    (hN : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∑ x ∈ S.image c₁, φ x ≤ Φ) (hΦ₂ : ∑ y ∈ S.image c₂, φ y ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  rw [rows_fibres S c₁ c₂]
  have hΦ0 : 0 ≤ Φ := le_trans (Finset.sum_nonneg fun x _ => hφ0 x) hΦ₁
  calc ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
      ≤ ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, M * (R * (φ x * φ y)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        calc ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
            ≤ ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (α x * α y) := by
              refine Finset.sum_le_sum fun p hp => ?_
              obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hp
              refine mul_le_mul_of_nonneg_left ?_ (hw p hpS)
              exact mul_le_mul (h1 ▸ hα₁ p hpS) (h2 ▸ hα₂ p hpS) (ha₂ p hpS) (hα0 x)
          _ = (∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p) * (α x * α y) := by rw [Finset.sum_mul]
          _ ≤ (M * N x y) * (α x * α y) :=
              mul_le_mul_of_nonneg_right (hcount x hx y hy) (mul_nonneg (hα0 x) (hα0 y))
          _ = M * (N x y * (α x * α y)) := by ring
          _ ≤ M * (R * (φ x * φ y)) := mul_le_mul_of_nonneg_left (hN x hx y hy) hM
    _ = M * (R * ((∑ x ∈ S.image c₁, φ x) * ∑ y ∈ S.image c₂, φ y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ M * (R * Φ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) hM
        rw [sq]
        exact mul_le_mul hΦ₁ hΦ₂ (Finset.sum_nonneg fun x _ => hφ0 x) hΦ0

theorem weighted_sum_le' {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → ∀ S' : Finset Pr, S' ⊆ S →
      (∀ p ∈ S', c₁ p = x ∧ c₂ p = y) → ∑ p ∈ S', w p ≤ M * N x y)
    (hN : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₁ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ)
    (hΦ₂ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₂ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  classical
  refine weighted_sum_le S w a₁ a₂ c₁ c₂ M R Φ N α φ hM hR hw ha₁ ha₂ hα₁ hα₂ ?_ ?_ hα0 hφ0 ?_ ?_
  · intro x hx y hy
    exact hcount x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy) _ (Finset.filter_subset _ _)
      fun p hp => (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    exact hN x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy)
  · exact hΦ₁ _ fun x hx => Finset.mem_image.1 hx
  · exact hΦ₂ _ fun x hx => Finset.mem_image.1 hx

end Formalism.MainNotions.BridgeLemma₂
