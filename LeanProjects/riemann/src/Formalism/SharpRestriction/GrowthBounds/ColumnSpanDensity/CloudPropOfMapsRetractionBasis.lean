import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudCount
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LemmaSMat

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def RestCloudMaps : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (TT : Finset (Fin n')) (a ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ),
    IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 → (∀ s, s ∉ TT → lam0 s = 0) →
    (∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) → 2 * ccl ≤ 8 * a →
    ∀ e : Edge R.W R.Qq (mm + 1 + 1), IsEdge p n' 1 e →
    ∃ (nb : ℕ) (io : Vsp R.Kf (flatW (mm + 1) A B) →ₗ[R.Kf]
        Vsp R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)))
      (U : Fin nb → Vsp R.Kf (flatW (mm + 1) A B) →ₗ[R.Kf] Vsp R.Kf lam0)
      (L : Fin nb → Vsp R.Kf lam0 →ₗ[R.Kf]
        Vsp R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)))
      (ka : Fin nb → ℕ),
      (nb : ℝ) = dimCl TT lam0 ∧ (∀ b, ka b ≤ TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
      (∀ a' b F, L a' (U b F) = if a' = b then ((p : R.Kf) ^ ka b) • io F else 0) ∧
      (∀ F, io F ∈ Re p R.ι R.σ R.w 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) e ↔
        F ∈ Re p R.ι R.σ R.w 1 (flatW (mm + 1) A B) e) ∧
      ∀ t c₂ : ℕ, 2 * TT.card * ccl ≤ c₂ →
        (∀ F ∈ CCL R (flatW (mm + 1) A B) t c₂ e,
          io F ∈ CCL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ e) ∧
        (∀ b, ∀ F ∈ CCL R (flatW (mm + 1) A B) t c₂ e, U b F ∈ CCL R lam0 t c₂ e) ∧
        (∀ a', ∀ g ∈ CCL' R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ e,
          ((p : R.Kf) ^ (Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) - Ar 1 lam0)) •
            (g ∘ₗ L a') ∈ CCL' R lam0 t (c₂ - 2 * TT.card * ccl) e)

theorem lemmaSMat : LemmaSMat := fun O _ _ _ σ ρ z1 z2 h1 h2 N B => KP.lemmaSMat σ ρ z1 z2 h1 h2 N B

theorem cloud_prop_of_maps_retraction_basis (hC : RestCloudMaps) (hRet : LatRetract) (hBP : BePerfect) (hD3 : DualHeightBasis) : CloudLowerBoundWeyl := by
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 t c₂ D₁ κ₁ κ₂ hD hDc hNc hκ0 hκ1 hκ2 hρ1 hρ2 e he
  obtain ⟨nb, io, U, L, ka, hnb, hka, h24, hiso, hmem⟩ :=
    hC p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨hio, hU, hL⟩ := hmem t c₂ hNc
  obtain ⟨n1, hX1, f1⟩ := hρ1 e he
  obtain ⟨n2, hX2, f2⟩ := hρ2 e he
  obtain ⟨r, hr, hfac⟩ := cloud_count R lemmaSMat hRet hBP hD3 _ _ lam0 (flattened_weight_dominant _ _ _) (flattened_weight_dominant _ _ _) e he t c₂
    (c₂ - 2 * TT.card * ccl) (Nat.sub_le _ _) D₁ hD hDc nb (TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) io U L ka hka h24 hiso hio
    hU hL n1 n2 f1 f2
  refine ⟨nb * r, ?_, ?_⟩
  · rw [← hnb]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    linarith
  · have : (2 * D₁ + ((TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ) : ℝ)) =
        2 * D₁ + (TT.card : ℝ) * (⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ) := by push_cast; ring
    rw [← this]
    exact hfac

end Formalism.MainNotions.flipOneThree.Pf

end
