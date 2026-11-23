import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.GaussSt

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Metric Set

section polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sphMonom_polar_mul (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) (φ : ℝ → ℝ) :
    ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ =
      (∫ u : sphere (0 : E) 1, G u ∂μ.toSphere) *
        ((∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) : ℝ) : ℂ) := by
  have hpres := (Measure.measurePreserving_homeomorphUnitSphereProd μ).integral_comp
    (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => G (p.1 : E) * ((φ p.2 : ℝ) : ℂ))
  calc ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ
      = ∫ x in ({0}ᶜ : Set E), G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ := by
        rw [restrict_compl_singleton]
    _ = ∫ x : ({0}ᶜ : Set E), G (‖(x : E)‖⁻¹ • (x : E)) * (φ ‖(x : E)‖ : ℂ)
          ∂(Measure.comap Subtype.val μ) :=
        (integral_subtype_comap (measurableSet_singleton 0).compl _).symm
    _ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), G (p.1 : E) * ((φ p.2 : ℝ) : ℂ)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) hpres
        simp [homeomorphUnitSphereProd]
    _ = _ := by
        rw [integral_prod_mul (fun u : sphere (0 : E) 1 => G (u : E))
          (fun r : Ioi (0 : ℝ) => ((φ r : ℝ) : ℂ)), integral_complex_ofReal]

end polar

theorem sphMonom_volumeIoiPow_integral (m : ℕ) (φ : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow m) = ∫ r in Ioi (0 : ℝ), r ^ m * φ r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
    ((measurable_subtype_coe.pow_const m).ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (ENNReal.ofReal (r ^ m)).toReal • φ r)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) m)]

theorem sphMonom_radial (m k : ℕ) :
    ∫ r : Ioi (0 : ℝ), r.1 ^ k * Real.exp (-(r.1 ^ 2)) ∂(Measure.volumeIoiPow m) =
      Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) / 2 := by
  have hv := sphMonom_volumeIoiPow_integral m (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)))
  rw [hv]
  have hq : (-1 : ℝ) < ((m + k : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((m + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((m + k : ℕ) : ℝ)) (by norm_num) hq
  calc ∫ r in Ioi (0 : ℝ), r ^ m * (r ^ k * Real.exp (-(r ^ 2)))
      = ∫ x in Ioi (0 : ℝ), x ^ (((m + k : ℕ) : ℝ)) * Real.exp (-x ^ (2 : ℝ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        simp only [Real.rpow_natCast, Real.rpow_two]
        ring
    _ = 1 / 2 * Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) := h2
    _ = _ := by ring

section eucl

variable (N : ℕ)

def sphMonomL : (Fin N → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin N) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℂ)).symm

def sphMonomMu : Measure (EuclideanSpace ℂ (Fin N)) :=
  (volume : Measure (Fin N → ℂ)).map (sphMonomL N)

instance sphMonomMu_isAddHaar : (sphMonomMu N).IsAddHaarMeasure := by
  unfold sphMonomMu; infer_instance

theorem norm_sphMonomL (z : Fin N → ℂ) : ‖sphMonomL N z‖ = Real.sqrt (sqN z) := by
  rw [EuclideanSpace.norm_eq]
  rfl

theorem integral_sphMonomMu (g : EuclideanSpace ℂ (Fin N) → ℂ) :
    ∫ x, g x ∂(sphMonomMu N) = ∫ z, g (sphMonomL N z) :=
  (sphMonomL N).toHomeomorph.measurableEmbedding.integral_map g

theorem finrank_sphMonomE : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

end eucl

section key

variable {N : ℕ}

theorem sphMonom_sqN_nonneg (z : Fin N → ℂ) : 0 ≤ sqN z :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem sphMonom_key [NeZero N] {k : ℕ} (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ (r : ℝ) (z : Fin N → ℂ), f (r • z) = (r : ℂ) ^ k * f z) :
    (∫ z, f z * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + 0 : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) =
      (∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + k : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  have hzs : ∀ z : Fin N → ℂ, z = Real.sqrt (sqN z) • ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    by_cases hs : Real.sqrt (sqN z) = 0
    · have h0 : sqN z = 0 := by
        have := Real.sqrt_eq_zero'.1 hs
        linarith [sphMonom_sqN_nonneg z]
      have hz : z = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖z j‖)).1 h0 i (Finset.mem_univ i)
        simpa using this
      rw [hs, zero_smul]
      exact hz
    · rw [smul_inv_smul₀ hs]
  have hhom : ∀ z, f z = ((Real.sqrt (sqN z) : ℝ) : ℂ) ^ k * f ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    conv_lhs => rw [hzs z]
    exact hf _ _
  have hexp : ∀ z : Fin N → ℂ, Real.exp (-sqN z) = Real.exp (-(Real.sqrt (sqN z)) ^ 2) := by
    intro z
    rw [Real.sq_sqrt (sphMonom_sqN_nonneg z)]
  let G : EuclideanSpace ℂ (Fin N) → ℂ := fun y => f ((sphMonomL N).symm y)
  have hG : ∀ z, G (‖sphMonomL N z‖⁻¹ • sphMonomL N z) = f ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    simp only [G, map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_sphMonomL]
  have hrad : ∀ j, ∫ r : Ioi (0 : ℝ), r.1 ^ j * Real.exp (-(r.1 ^ 2))
      ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) - 1)) =
        Real.Gamma ((((2 * N - 1 + j : ℕ) : ℝ) + 1) / 2) / 2 := by
    intro j
    rw [finrank_sphMonomE]
    exact sphMonom_radial (2 * N - 1) j
  have hpol : ∀ j, ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ j * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) =
      (∫ u : sphere (0 : EuclideanSpace ℂ (Fin N)) 1, G u ∂(sphMonomMu N).toSphere) *
        ((Real.Gamma ((((2 * N - 1 + j : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by
    intro j
    refine (sphMonom_polar_mul (sphMonomMu N) G (fun r => r ^ j * Real.exp (-(r ^ 2)))).trans ?_
    congr 1
    exact_mod_cast hrad j
  have hL1 : ∫ z, f z * (Real.exp (-sqN z) : ℂ) =
      ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ k * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) := by
    rw [integral_sphMonomMu]
    congr 1
    funext z
    rw [hG z, norm_sphMonomL, hhom z, hexp z]
    push_cast
    ring
  have hL2 : ∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) =
      ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ 0 * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) := by
    rw [integral_sphMonomMu]
    congr 1
    funext z
    rw [hG z, norm_sphMonomL, hexp z]
    push_cast
    ring
  rw [hL1, hL2, hpol k, hpol 0]
  ring

theorem sphMonom_continuous_sqN : Continuous (fun z : Fin N → ℂ => sqN z) := by
  unfold sqN
  exact continuous_finset_sum _ fun i _ => (continuous_norm.comp (continuous_apply i)).pow 2

theorem sphMonom_measurable_normalize :
    Measurable (fun z : Fin N → ℂ => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) :=
  (Complex.measurable_ofReal.comp (sphMonom_continuous_sqN.measurable.sqrt.inv)).smul measurable_id

theorem sphMonom_integral_sphProb (g : (Fin N → ℂ) → ℂ) (hg : Continuous g) :
    ∫ z, g z ∂(sphProb N) =
      ((Real.pi ^ N)⁻¹ : ℂ) * ∫ z, g ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) := by
  have hm := sphMonom_measurable_normalize (N := N)
  have hmeas : Measurable fun z : Fin N → ℂ => ENNReal.ofReal ((Real.pi ^ N)⁻¹ * Real.exp (-sqN z)) :=
    Measurable.ennreal_ofReal (measurable_const.mul
      (Real.measurable_exp.comp (sphMonom_continuous_sqN.measurable.neg)))
  rw [sphProb, integral_map hm.aemeasurable hg.aestronglyMeasurable, gaussC,
    integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  congr 1
  funext z
  have hsm : (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z = (Real.sqrt (sqN z))⁻¹ • z := by
    funext i
    simp [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (by positivity), hsm, Complex.real_smul]
  push_cast
  ring

theorem sphMonom_monoC_smul (a : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    monoC a (r • z) = (r : ℂ) ^ (∑ i, a i) * monoC a z := by
  simp only [monoC, Pi.smul_apply, Complex.real_smul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

theorem sphMonom_f_smul (a b : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    starRingEnd ℂ (monoC a (r • z)) * monoC b (r • z) =
      (r : ℂ) ^ ((∑ i, a i) + ∑ i, b i) * (starRingEnd ℂ (monoC a z) * monoC b z) := by
  simp only [sphMonom_monoC_smul, map_mul, map_pow, Complex.conj_ofReal]
  ring

theorem sphMonom_continuous_f (a b : Fin N → ℕ) :
    Continuous fun z : Fin N → ℂ => starRingEnd ℂ (monoC a z) * monoC b z := by
  have hm : ∀ c : Fin N → ℕ, Continuous fun z : Fin N → ℂ => monoC c z := fun c =>
    continuous_finset_prod _ fun i _ => (continuous_apply i).pow _
  exact (Complex.continuous_conj.comp (hm a)).mul (hm b)

theorem sphMonom_sqN_smul (c : ℂ) (z : Fin N → ℂ) : sqN (c • z) = ‖c‖ ^ 2 * sqN z := by
  simp only [sqN, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem sphMonom_sqN_normalize (z : Fin N → ℂ) (hz : z ≠ 0) :
    sqN ((((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) = 1 := by
  have hs : sqN z ≠ 0 := by
    intro h
    apply hz
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖z j‖)).1 h i (Finset.mem_univ i)
    simpa using this
  rw [sphMonom_sqN_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (sphMonom_sqN_nonneg z), inv_mul_cancel₀ hs]

theorem sphMonom_gamma (D n k : ℕ) (h : k = n + n) :
    Real.Gamma ((((2 * (D + 1) - 1 + k : ℕ) : ℝ) + 1) / 2) = ((D + n).factorial : ℝ) := by
  subst h
  rw [show 2 * (D + 1) - 1 + (n + n) = 2 * (D + n) + 1 by omega,
    show ((((2 * (D + n) + 1 : ℕ) : ℝ) + 1) / 2) = ((D + n : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]

end key

end ReciprocityTheory.GeometryOfNumbersTheory
