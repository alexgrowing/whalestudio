import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierExtractionTsumClass

open Module

namespace GlobalTheory

theorem exists_torsion_twist_tsum_norm_ge :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : K), 0 < N → ‖(N : K)‖ = 1 → IsPrimitiveRoot ζ N → ∀ (σ : X → K) (q : X → ℝ) (r : ℝ), 0 < r → r < 1 → Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ z, ‖σ z‖ ≤ r ^ q z) → ∀ z₀ : X, ‖σ z₀‖ = r ^ q z₀ → (∀ μ, μ ≠ 0 → q z₀ < q (z₀ + N • μ)) → ∃ t : Multiplicative X →* Kˣ, t ^ N = 1 ∧ r ^ q z₀ ≤ ‖∑' z, σ z * (t (Multiplicative.ofAdd z) : K)‖ := by
  classical
  intro K X _ _ _ _ _ _ N ζ hN hN1 hζ σ q r hr0 hr1 hq hσ z₀ hz₀ hlead
  have hσ0 : Filter.Tendsto σ Filter.cofinite (nhds 0) :=
    squeeze_zero_norm hσ ((tendsto_rpow_atTop_of_base_lt_one r (by linarith) hr1).comp hq)
  obtain ⟨hfin, hsum, hnorm⟩ :=
    fourier_extraction_tsum_class K X N ζ hN hN1 hζ σ hσ0 z₀
  have hclass : ‖∑' μ, σ (z₀ + N • μ)‖ = r ^ q z₀ := by
    rw [← hz₀]
    refine hnorm fun μ hμ => (hσ _).trans_lt ?_
    rw [hz₀]
    exact Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 (hlead μ hμ)
  have hone : ∀ (t : {t : Multiplicative X →* Kˣ // t ^ N = 1}) (x : Multiplicative X),
      ‖(t.1 x : K)‖ = 1 := by
    intro t x
    have h1 : ‖(t.1 x : K)‖ ^ N = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, TorsionFourier.apply_pow_eq_one t.2,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1
  haveI := Fintype.ofFinite {t : Multiplicative X →* Kˣ // t ^ N = 1}
  rw [finsum_eq_sum_of_fintype] at hsum
  obtain ⟨t, -, ht⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := (Finset.univ : Finset {t : Multiplicative X →* Kˣ // t ^ N = 1}))
    ⟨⟨1, one_pow N⟩, Finset.mem_univ _⟩
    (fun t => (((t.1 (Multiplicative.ofAdd z₀))⁻¹ : Kˣ) : K) *
      ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K))
  refine ⟨t.1, t.2, ?_⟩
  rw [hsum, norm_mul, norm_pow, hN1, one_pow, one_mul, hclass, norm_mul,
    Units.val_inv_eq_inv_val, norm_inv, hone, inv_one, one_mul] at ht
  exact ht

end GlobalTheory
