import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
import Development.AutomorphicArithmetic.DivisorFrames.FourierWeightIntegralSymmetry
import Development.AutomorphicArithmetic.DivisorFrames.ExistsTestFourierNonvanishing
import Development.AutomorphicArithmetic.DivisorFrames.SchwartzFourierPreimage
import Development.AutomorphicArithmetic.DivisorFrames.FourierNonvanishingUnitPoint
import Development.AutomorphicArithmetic.DivisorFrames.FourierContinuousNonvanishing
import Development.AutomorphicArithmetic.DivisorFrames.ConvolutionDecayIntegrableFourier
import Development.AutomorphicArithmetic.DivisorFrames.ConvolutionFamilyIntegrable
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem map_mul_vol' {ι : Type} [Fintype ι] {s : ι → ℂ} (hs : ∀ w, s w ≠ 0) :
    (volume : Measure (ι → ℂ)).map (fun y => s * y) = ENNReal.ofReal (nm s)⁻¹ • volume := by
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    LinearMap.pi fun i => (Algebra.lmul ℝ ℂ (s i)).comp (LinearMap.proj i)
  have hdet : LinearMap.det L = nm s := by
    rw [LinearMap.det_pi, nm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hL : (fun y => s * y) = L := by
    funext y i
    simp [L]
  rw [hL, Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact (nm_pos hs).ne'), hdet,
    abs_of_pos (inv_pos.2 (nm_pos hs))]

private theorem integral_scale' {ι : Type} [Fintype ι] {s : ι → ℂ} (hs : ∀ w, s w ≠ 0)
    {G : (ι → ℂ) → ℂ} (hG : Continuous G) : ∫ y, G (s * y) = (nm s)⁻¹ • ∫ y, G y := by
  have hm : Measurable fun y : ι → ℂ => s * y := measurable_const_mul s
  rw [← integral_map hm.aemeasurable hG.aestronglyMeasurable, map_mul_vol' hs, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.2 (nm_pos hs)).le]

private theorem bound_int {ι : Type} [Fintype ι] (C : ℝ) :
    Integrable (fun s : ι → ℂ => C / (1 + ‖s‖) ^ (Module.finrank ℝ (ι → ℂ) + 1)) := by
  have := integrable_one_add_norm (E := ι → ℂ) (μ := volume)
    (r := ((Module.finrank ℝ (ι → ℂ) + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  refine (this.const_mul C).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]

theorem UpperTheory.exists_convolution_nonvanishing_weight :
    ∀ {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
        [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (κ : ι → ℤ) (e : ℕ),
        (∀ w, 2 * (e : ℤ) < κ w) → ∀ (η : K → Fin n × ι → ℂ), Continuous η → (∀ k w, ∃ i, η k (i, w) ≠ 0) →
        ∀ (φ : K → (ι → ℂ) → ℂ), Continuous (Function.uncurry φ) → (∀ N : ℕ, ∃ C : ℝ, ∀ k s, ‖φ k s‖ ≤ C / (1 + ‖s‖) ^ N) →
        ∀ k₀ : K, φ k₀ ≠ 0 →
        (∀ k (t : ι → ℂ), (∀ w, t w ≠ 0) → sc t (η k) = η k₀ → ∃ r : ℝ, 0 < r ∧ ∀ s, φ k s = r * wt κ e t * φ k₀ (t * s)) →
        ∃ v : Fin n × ι → ℂ, ∫ k, ∫ s, φ k (s + pr v (η k)) * wt κ e s ∂volume ∂μ ≠ 0 := by
  intro ι _ n K _ _ _ _ _ μ _ _ κ e hκ η hη h0 φ hφ hdec k₀ hk₀ hhom
  by_contra hcon
  push Not at hcon
  have hφk : ∀ k, Continuous (φ k) := fun k => hφ.comp (Continuous.prodMk_right k)
  obtain ⟨C, hC⟩ := hdec (Module.finrank ℝ (ι → ℂ) + 1)
  have hint : ∀ k, Integrable (φ k) := fun k =>
    (bound_int C).mono' (hφk k).aestronglyMeasurable (Filter.Eventually.of_forall (hC k))
  obtain ⟨y₀, hy₀, hF₀⟩ := UpperTheory.fourier_nonvanishing_unit_point (φ k₀) (hφk k₀) (hint k₀) hk₀
  have hG : Continuous (Function.uncurry fun k y => FT (φ k) y) := by
    refine continuous_of_dominated (F := fun (p : K × (ι → ℂ)) s => φ p.1 s * ec (s * p.2))
      (fun p => ?_) (fun p => ?_) (bound_int C) ?_
    · exact ((hφk p.1).mul (continuous_ec.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]; exact hC _ _
    · refine Filter.Eventually.of_forall fun s => ?_
      exact (hφ.comp (continuous_fst.prodMk continuous_const)).mul
        (continuous_ec.comp (continuous_const.mul continuous_snd))
  have hnm : ∀ {y : ι → ℂ}, (∀ w, y w ≠ 0) → (nm y : ℂ) ≠ 0 := fun hy => by exact_mod_cast (nm_pos hy).ne'
  have hc : FT (φ k₀) y₀ * dwt κ e y₀ ≠ 0 :=
    mul_ne_zero hF₀ (inv_ne_zero (mul_ne_zero (wt_ne_zero κ e hy₀) (hnm hy₀)))
  have hpos : ∀ k y, sc y (η k) = sc y₀ (η k₀) →
      0 < (starRingEnd ℂ (FT (φ k₀) y₀ * dwt κ e y₀) * (FT (φ k) y * dwt κ e y)).re := by
    intro k y hy
    have hyne : ∀ w, y w ≠ 0 := fun w hw => by
      obtain ⟨i, hi⟩ := h0 k₀ w
      have h1 : y w * η k (i, w) = y₀ w * η k₀ (i, w) := congrFun hy (i, w)
      rw [hw, zero_mul] at h1
      exact mul_ne_zero (hy₀ w) hi h1.symm
    obtain ⟨t, ht, rfl⟩ : ∃ t : ι → ℂ, (∀ w, t w ≠ 0) ∧ y = t * y₀ :=
      ⟨fun w => y w / y₀ w, fun w => div_ne_zero (hyne w) (hy₀ w), funext fun w => (div_mul_cancel₀ _ (hy₀ w)).symm⟩
    have hsc : sc t (η k) = η k₀ := by
      funext p
      have h1 : t p.2 * y₀ p.2 * η k p = y₀ p.2 * η k₀ p := congrFun hy p
      refine mul_left_cancel₀ (hy₀ p.2) ?_
      rw [← h1, sc]
      ring
    obtain ⟨r, hr, hrs⟩ := hhom k t ht hsc
    have hFT : FT (φ k) (t * y₀) = r * wt κ e t * ((nm t)⁻¹ • FT (φ k₀) y₀) := by
      rw [FT, FT, ← integral_scale' ht (G := fun s => φ k₀ s * ec (s * y₀))
        ((hφk k₀).mul (continuous_ec.comp (continuous_id.mul continuous_const))), ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only
      rw [hrs s, mul_left_comm s t y₀, mul_assoc t s y₀]
      ring
    have h2 : FT (φ k) (t * y₀) * dwt κ e (t * y₀)
        = ((r * ((nm t)⁻¹ * (nm t)⁻¹) : ℝ) : ℂ) * (FT (φ k₀) y₀ * dwt κ e y₀) := by
      have a1 := wt_ne_zero κ e ht
      have a2 := hnm ht
      rw [hFT, dwt_mul, show dwt κ e t = (wt κ e t * (nm t : ℂ))⁻¹ from rfl, Complex.real_smul]
      push_cast
      field_simp
    rw [h2, mul_left_comm, Complex.re_ofReal_mul, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    have a3 := nm_pos ht
    exact mul_pos (by positivity) (Complex.normSq_pos.2 hc)
  obtain ⟨β, hβ, hβc, hβi, hβne⟩ := UpperTheory.fourier_continuous_nonvanishing μ η hη h0 (fun k y => FT (φ k) y) hG κ e k₀ y₀ hy₀ _ hpos
  obtain ⟨h, hh, hhi, hhF⟩ := UpperTheory.schwartz_fourier_preimage β hβ hβc
  obtain ⟨h₀, i1, i2, i3, i4⟩ := UpperTheory.exists_test_fourier_nonvanishing κ e hκ
  have key : ∀ k, (∫ s, (∫ v, h v * φ k (s + pr v (η k))) * wt κ e s) * (∫ y, FT h₀ y * dwt κ e y)
      = (∫ s, h₀ s * wt κ e s) * ∫ y, β (sc y (η k)) * FT (φ k) y * dwt κ e y := by
    intro k
    obtain ⟨j1, j2, j3⟩ := UpperTheory.convolution_decay_integrable_fourier κ e (η k) (φ k) (hφk k)
      (fun N => (hdec N).imp fun C hC => hC k) h hh hhi
    simp only [hhF] at j3
    have := UpperTheory.fourier_weight_integral_symmetry κ e _ h₀ j1 i1 j2 i2 (by simpa only [j3] using hβi k) i3
    simpa only [j3] using this
  have hfub := UpperTheory.convolution_family_integrable μ κ e η hη φ hφ hdec h hh hhi
  simp only [hcon, mul_zero, integral_zero] at hfub
  have := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall key)
  rw [integral_mul_const, integral_const_mul, hfub, zero_mul] at this
  exact mul_ne_zero i4 hβne this.symm
