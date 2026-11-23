import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory

theorem exists_unfoldingKernel_levelSubgroup_bruhat : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  intro G G' T T' _ _ _ _ _ _ _ _ _ _ _ μ μ' _ m m' _ K K' hK hK' φ ψ ψ' j hψ hψ' hj hφK hcomm
    hm hm' b hb hb1 f hf hfinv ν hν
  have hbf : Measurable fun t => b t * f t := hb.mul hf
  refine ⟨(K : Set G).indicator (fun h => b (ψ h) * f (ψ h)), (hbf.comp hψ).indicator hK, ?_, ?_⟩
  · rw [lintegral_indicator hK, ← lintegral_map hbf hψ, hm, hν _ hbf]
    refine lintegral_congr fun c => ?_
    simp only [hfinv]
    rw [lintegral_mul_const _ (f := fun s => b (j s * Quotient.out c))
      (hb.comp (hj.mul_const _)), hb1, one_mul]
  · intro h
    by_cases hh : ∃ g, (φ g)⁻¹ * h ∈ K
    · obtain ⟨g₀, hk⟩ := hh
      have hmem : h ∈ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := ⟨g₀, hk⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      obtain ⟨k, rfl⟩ : ∃ k, h = φ g₀ * k := ⟨(φ g₀)⁻¹ * h, by simp⟩
      rw [inv_mul_cancel_left] at hk
      rw [← lintegral_mul_left_eq_self _ g₀]
      have hF : Measurable fun s : T' => b (j s⁻¹ * ψ k) :=
        hb.comp ((hj.comp measurable_inv).mul_const _)
      have key : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h))
          ((φ (g₀ * g))⁻¹ * (φ g₀ * k)) =
          (K' : Set G').indicator (fun g => b (j (ψ' g)⁻¹ * ψ k) * f (ψ k)) g := by
        intro g
        have e : (φ (g₀ * g))⁻¹ * (φ g₀ * k) = (φ g)⁻¹ * k := by
          rw [map_mul]; group
        have e2 : ψ ((φ g)⁻¹ * k) = j (ψ' g)⁻¹ * ψ k := by
          rw [map_mul, map_inv, hcomm, map_inv]
        rw [e]
        by_cases hg : g ∈ K'
        · have : (φ g)⁻¹ * k ∈ (K : Set G) := K.mul_mem (K.inv_mem ((hφK g).2 hg)) hk
          rw [Set.indicator_of_mem this, Set.indicator_of_mem (show g ∈ (K' : Set G') from hg),
            e2, hfinv]
        · have : (φ g)⁻¹ * k ∉ (K : Set G) := fun hx =>
            hg ((hφK g).1 (K.inv_mem_iff.1 ((K.mul_mem_cancel_right hk).1 hx)))
          rw [Set.indicator_of_notMem this,
            Set.indicator_of_notMem (show g ∉ (K' : Set G') from hg)]
      simp only [key]
      rw [lintegral_indicator hK',
        ← lintegral_map (f := fun s : T' => b (j s⁻¹ * ψ k) * f (ψ k)) (hF.mul_const _) hψ', hm',
        lintegral_mul_const _ hF, lintegral_inv_eq_self (fun s => b (j s * ψ k)), hb1, one_mul,
        map_mul, hcomm, hfinv]
    · have hmem : h ∉ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := hh
      rw [Set.indicator_of_notMem hmem, zero_mul]
      have : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h)) ((φ g)⁻¹ * h) = 0 :=
        fun g => Set.indicator_of_notMem (fun hx => hh ⟨g, hx⟩) _
      simp only [this, lintegral_zero]

end GlobalTheory
