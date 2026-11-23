import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory Matrix

namespace GlobalTheory
open ValuativeRel

theorem norm_addChar_nonarch {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (t : k) : ‖ψ0 t‖ = 1 := by
  have hO : IsCompact (𝒪[k] : Set k) := by exact GlobalTheory.SplitWeil.Model.isCompact_int
  have hK : IsCompact ((fun u => t * u) '' (𝒪[k] : Set k)) := hO.image (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := (hK.image hψ).isBounded.exists_norm_le
  have hpow : ∀ n : ℤ, ‖ψ0 t‖ ^ n ≤ C := fun n => by
    have hmem : ψ0 (t * (n : k)) ∈ ψ0 '' ((fun u => t * u) '' (𝒪[k] : Set k)) :=
      ⟨t * n, ⟨n, intCast_mem _ n, rfl⟩, rfl⟩
    have := hC _ hmem
    rwa [mul_comm, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow, norm_zpow] at this
  have hne : ψ0 t ≠ 0 := fun h => by
    have := AddChar.map_add_eq_mul ψ0 t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hpos : 0 < ‖ψ0 t‖ := norm_pos_iff.2 hne
  refine le_antisymm ?_ ?_
  · by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hpow n) (by rw [zpow_natCast]; exact not_le.2 hn)
  · by_contra h
    have h1 : 1 < ‖ψ0 t‖⁻¹ := one_lt_inv₀ hpos |>.2 (not_le.1 h)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h1
    have := hpow (-(n : ℤ))
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    exact absurd this (not_le.2 hn)

theorem schr_unitary : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  intro k _ _ _ _ _ ψ0 hψ κ _ μ hμ w φ φ'
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have h1 : ∀ s : k, ψ0 s * (starRingEnd ℂ) (ψ0 s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar_nonarch ψ0 hψ s]; simp
  have h2 : (fun y => GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y)) =
      fun y => φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1)) := by
    funext y
    simp only [GlobalTheory.WeilM.schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))
    linear_combination (φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1))) * this
  rw [h2]
  exact integral_add_right_eq_self (fun y => φ y * (starRingEnd ℂ) (φ' y)) w.1

end GlobalTheory
