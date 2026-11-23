import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open MeasureTheory Module
open scoped FourierTransform

private lemma sublevel_set_eq_closed_ball (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    {x : EuclideanSpace ℝ (Fin N) | ‖x‖ ^ 2 ≤ t} = Metric.closedBall 0 (Real.sqrt t) := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  rw [Real.le_sqrt (norm_nonneg x) ht]

theorem volume_euclidean_ball : ball_volume := by
  intro n t ht
  rw [sublevel_set_eq_closed_ball _ t ht]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * 0))) (Real.sqrt t) = Set.univ := by
      ext x
      have : x = 0 := by ext i; exact absurd i.2 (by simp)
      simp [this, Real.sqrt_nonneg]
    rw [hs]
    have hv : volume (Set.univ : Set (EuclideanSpace ℝ (Fin (2 * 0)))) = 1 := by
      have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (2 * 0))
      have := h1.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
      rw [Set.preimage_univ] at this
      rw [this]
      have hpi : (Set.univ : Set (Fin (2 * 0) → ℝ)) = Set.pi Set.univ (fun _ => Set.univ) := by simp
      rw [hpi, volume_pi_pi]
      simp
    rw [hv]
    simp
  · have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
    have : Nontrivial (EuclideanSpace ℝ (Fin (2 * n))) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    have hk : finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by simp
    rw [InnerProductSpace.volume_closedBall_of_dim_even hk, hk, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg t),
      ENNReal.toReal_ofReal (by positivity), pow_mul, Real.sq_sqrt ht]
    ring

theorem sphere_surface_volume : SphereVolumeDerivative := by
  intro M hM
  have hev : (fun t : ℝ => (2 : ℝ) ^ M *
      (volume {x : EuclideanSpace ℝ (Fin (2 * M)) | ‖x‖ ^ 2 ≤ t}).toReal) =ᶠ[nhds 1]
      fun t : ℝ => (2 : ℝ) ^ M * (Real.pi ^ M * t ^ M / (M.factorial : ℝ)) := by
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with t ht
    rw [volume_euclidean_ball M t ht.le]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (fun t : ℝ => t ^ M) ((M : ℝ) * 1 ^ (M - 1)) 1 := hasDerivAt_pow M 1
  have h2 := ((h1.const_mul (Real.pi ^ M)).div_const (M.factorial : ℝ)).const_mul ((2 : ℝ) ^ M)
  have he : (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) =
      2 ^ M * (Real.pi ^ M * ((M : ℝ) * 1 ^ (M - 1)) / (M.factorial : ℝ)) := by
    clear h2 h1 hev
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      one_pow, mul_one]
    rw [mul_pow]
    field_simp
  rw [he]
  exact h2

private lemma fourier_transform_scaled_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (g : V → ℂ) (ξ : V) :
    (∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((2 * inner ℝ x ξ : ℝ) : ℂ))) * g x) =
      𝓕 g ((2 : ℝ) • ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, inner_smul_right]
  congr 2
  push_cast
  ring

theorem self_dual_lattice_measure : SelfDualMeasure := by
  intro M φ FT x
  have hFT : ∀ g ξ, FT g ξ = (2 : ℂ) ^ M * 𝓕 g ((2 : ℝ) • ξ) := by
    intro g ξ
    simp only [FT]
    rw [fourier_transform_scaled_inner]
  rw [hFT]
  have h1 : FT (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) =
      fun ξ => (2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) ((2 : ℝ) • ξ) :=
    funext (hFT _)
  rw [h1, Real.fourier_eq]
  have h2 : (∫ v : EuclideanSpace ℝ (Fin (2 * M)), Real.fourierChar (-inner ℝ v ((2 : ℝ) • x)) •
        ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) ((2 : ℝ) • v))) =
      ∫ v : EuclideanSpace ℝ (Fin (2 * M)),
        (fun w => Real.fourierChar (-inner ℝ w x) •
          ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) ((2 : ℝ) • v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [inner_smul_left, inner_smul_right]
    simp
  rw [h2, Measure.integral_comp_smul volume (fun w => Real.fourierChar (-inner ℝ w x) •
          ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) (2 : ℝ)]
  have h3 : (∫ w : EuclideanSpace ℝ (Fin (2 * M)), Real.fourierChar (-inner ℝ w x) •
        ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) =
      (2 : ℂ) ^ M * 𝓕 (𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ)) x := by
    rw [Real.fourier_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h3]
  have h4 : 𝓕 (𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ)) x = φ (-x) := by
    have := φ.continuous.fourierInv_fourier_eq φ.integrable (𝓕 φ).integrable
    have h5 := congrFun this (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h5
    exact h5
  rw [h4]
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (2 * M))) = 2 * M := by simp
  rw [hfr, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  have h2M : ((2 : ℂ) ^ M) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h22 : ((2 : ℂ) ^ (2 * M)) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  generalize φ (-x) = c
  rw [h22]
  field_simp

end Formalism.HermitianLattices.GenusMassVolumes
