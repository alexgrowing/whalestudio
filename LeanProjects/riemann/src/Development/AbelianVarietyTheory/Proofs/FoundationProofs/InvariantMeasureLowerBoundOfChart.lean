import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem invariant_measure_lower_bound_of_chart :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype ι] (mK : Measure G) [IsProbabilityMeasure mK] (K U : Set G) (θ : (ι → ℝ) → G) (T δ : ℝ), Continuous θ → IsClosed U → mK Kᶜ = 0 → (∀ R, Measure.map (fun x => θ R * x) mK = mK) → 0 < δ → 0 ≤ T → (∀ x ∈ K, ∃ R₀ : ι → ℝ, (∀ i, |R₀ i| ≤ T) ∧ ∀ R : ι → ℝ, (∀ i, |R i - R₀ i| ≤ δ) → (θ R)⁻¹ * x ∈ U) → ENNReal.ofReal ((δ / (T + δ)) ^ Fintype.card ι) ≤ mK U := by
  intro G ι _ _ _ _ _ _ _ mK _ K U θ T δ hθ hU hK hinv hδ hT hch
  have hTδ : 0 < T + δ := by linarith
  set Q : Set (ι → ℝ) := Metric.closedBall 0 (T + δ) with hQ
  set S : Set ((ι → ℝ) × G) := {p | (θ p.1)⁻¹ * p.2 ∈ U} with hS
  have hSc : IsClosed S := hU.preimage (by fun_prop : Continuous fun p : (ι → ℝ) × G => (θ p.1)⁻¹ * p.2)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hQv : volume Q = ENNReal.ofReal ((2 * (T + δ)) ^ Fintype.card ι) :=
    Real.volume_pi_closedBall _ hTδ.le
  have hsec : ∀ R, mK (Prod.mk R ⁻¹' S) = mK U := by
    intro R
    have hm : MeasurableSet (Prod.mk R ⁻¹' S) := measurable_prodMk_left hSm
    conv_lhs => rw [← hinv R]
    rw [Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [hS]
  have h1 : ((volume.restrict Q).prod mK) S = mK U * volume Q := by
    rw [Measure.prod_apply hSm]
    simp [hsec]
  have h2 : ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ≤ ((volume.restrict Q).prod mK) S := by
    rw [Measure.prod_apply_symm hSm]
    have hae : ∀ᵐ x ∂mK, x ∈ K := hK
    calc ENNReal.ofReal ((2 * δ) ^ Fintype.card ι)
        = ∫⁻ _x, ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ∂mK := by simp
      _ ≤ _ := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        obtain ⟨R₀, hR₀, hR⟩ := hch x hx
        have hm : MeasurableSet ((fun R => (R, x)) ⁻¹' S) := measurable_prodMk_right hSm
        rw [Measure.restrict_apply hm, ← Real.volume_pi_closedBall R₀ hδ.le]
        refine measure_mono fun R hRm => ?_
        have hd : ∀ i, |R i - R₀ i| ≤ δ := fun i => by
          have := (dist_pi_le_iff hδ.le).1 (Metric.mem_closedBall.1 hRm) i
          rwa [Real.dist_eq] at this
        refine ⟨hR R hd, ?_⟩
        rw [hQ, Metric.mem_closedBall, dist_pi_le_iff hTδ.le]
        intro i
        have h3 := abs_le.1 (hd i)
        have h4 := abs_le.1 (hR₀ i)
        rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le]
        constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  rw [h1, hQv] at h2
  have hpos : 0 < (2 * (T + δ)) ^ Fintype.card ι := by positivity
  have he : (δ / (T + δ)) ^ Fintype.card ι
      = (2 * δ) ^ Fintype.card ι / (2 * (T + δ)) ^ Fintype.card ι := by
    rw [← div_pow, mul_div_mul_left _ _ (two_ne_zero)]
  rw [he, ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.div_le_of_le_mul h2

end GlobalTheory.CartanInt
