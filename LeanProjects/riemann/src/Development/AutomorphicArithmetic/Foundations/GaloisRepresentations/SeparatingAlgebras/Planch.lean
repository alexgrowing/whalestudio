import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

end

private theorem sum_norm_sq_le_integral_of_plancherel {G : Type} [Group G] {n : ℕ} (K : Subgroup G)
    (φ : (Fin n → UnitAddCircle) → G → ℂ) (D S : (Fin n → UnitAddCircle) → ℂ) (f : G → ℂ)
    (T : Finset G) (mr B : ℝ) (N : ℕ) (c : ℂ) (hm : 0 < mr) (hN : 0 < N)
    (hφc : ∀ y, Continuous fun θ => φ θ y) (hDc : Continuous D) (hSc : Continuous S)
    (hB : ∀ θ, ‖D θ‖ ≤ B)
    (hintK : ∀ y ∈ K, c * ∫ θ, φ θ y * D θ = (N : ℂ))
    (hint0 : ∀ y ∉ K, c * ∫ θ, φ θ y * D θ = 0)
    (hA : ∀ θ y, (mr : ℂ) * ∑ g ∈ T, f g * φ θ (y * g) = S θ * φ θ y)
    (hT1 : ∀ g ∈ T, ∀ g' ∈ T, g⁻¹ * g' ∈ K → g = g')
    (hconj : ∀ᵐ θ, ∀ y, φ θ y⁻¹ = starRingEnd ℂ (φ θ y))
    (hone : ∀ θ, φ θ 1 = 1) :
    ∑ g ∈ T, ‖f g‖ ^ 2 ≤ (‖c‖ * B / (mr ^ 2 * N)) * ∫ θ, ‖S θ‖ ^ 2 := by
  classical
  have hI : ∀ u : (Fin n → UnitAddCircle) → ℂ, Continuous u → Integrable u := fun u hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)
  have h1 : ∀ g ∈ T, (mr : ℂ) * N * f g = c * ∫ θ, S θ * φ θ g⁻¹ * D θ := by
    intro g hg
    have e : (fun θ => S θ * φ θ g⁻¹ * D θ) =
        fun θ => ∑ g' ∈ T, (mr : ℂ) * f g' * (φ θ (g⁻¹ * g') * D θ) := by
      funext θ
      rw [← hA θ g⁻¹, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun g' _ => by ring
    have hsum := integral_finset_sum T fun g' _ =>
      hI (fun θ => (mr : ℂ) * f g' * (φ θ (g⁻¹ * g') * D θ))
        (continuous_const.mul ((hφc _).mul hDc))
    rw [e, hsum]
    simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    have hs : ∀ g' ∈ T, c * ((mr : ℂ) * f g' * ∫ θ, φ θ (g⁻¹ * g') * D θ) =
        if g = g' then (mr : ℂ) * N * f g else 0 := by
      intro g' hg'
      rw [show c * ((mr : ℂ) * f g' * ∫ θ, φ θ (g⁻¹ * g') * D θ) =
        (mr : ℂ) * f g' * (c * ∫ θ, φ θ (g⁻¹ * g') * D θ) by ring]
      by_cases hgg : g = g'
      · subst hgg
        rw [inv_mul_cancel, hintK 1 K.one_mem, if_pos rfl]
        ring
      · rw [hint0 _ fun hk => hgg (hT1 g hg g' hg' hk), if_neg hgg]
        simp
    rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq, if_pos hg]
  have h2 : (mr : ℂ) ^ 2 * N * ∑ g ∈ T, ((‖f g‖ ^ 2 : ℝ) : ℂ) =
      c * ∫ θ, ((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ := by
    calc (mr : ℂ) ^ 2 * N * ∑ g ∈ T, ((‖f g‖ ^ 2 : ℝ) : ℂ)
        = (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * ((mr : ℂ) * N * f g) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          have := Complex.conj_mul' (f g)
          push_cast
          rw [show (mr : ℂ) * (starRingEnd ℂ (f g) * ((mr : ℂ) * N * f g)) =
            (mr : ℂ) ^ 2 * N * (starRingEnd ℂ (f g) * f g) by ring, this]
      _ = (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * (c * ∫ θ, S θ * φ θ g⁻¹ * D θ) := by
          congr 1
          exact Finset.sum_congr rfl fun g hg => by rw [h1 g hg]
      _ = c * ∫ θ, (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * (S θ * φ θ g⁻¹ * D θ) := by
          have hsum := integral_finset_sum T fun g _ =>
            hI (fun θ => starRingEnd ℂ (f g) * (S θ * φ θ g⁻¹ * D θ))
              (continuous_const.mul ((hSc.mul (hφc _)).mul hDc))
          rw [integral_const_mul, hsum]
          simp_rw [integral_const_mul]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun g _ => by ring
      _ = c * ∫ θ, ((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hconj] with θ hθ
          have hA1 := hA θ 1
          simp only [one_mul, hone, mul_one] at hA1
          calc (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * (S θ * φ θ g⁻¹ * D θ)
              = S θ * D θ * starRingEnd ℂ ((mr : ℂ) * ∑ g ∈ T, f g * φ θ g) := by
                simp_rw [hθ]
                rw [map_mul, map_sum, Complex.conj_ofReal]
                simp_rw [map_mul]
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun g _ => by ring
            _ = ((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ := by
                rw [hA1, mul_comm (S θ) (D θ), mul_assoc, Complex.mul_conj']
                push_cast
                ring
  have h3 : mr ^ 2 * N * ∑ g ∈ T, ‖f g‖ ^ 2 ≤ ‖c‖ * ((∫ θ, ‖S θ‖ ^ 2) * B) := by
    have hl : mr ^ 2 * N * ∑ g ∈ T, ‖f g‖ ^ 2 =
        ‖(mr : ℂ) ^ 2 * N * ∑ g ∈ T, ((‖f g‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_sum,
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hl, h2, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
      (((hSc.norm.pow 2).mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall fun θ => ?_)
    show ‖((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ‖ ≤ ‖S θ‖ ^ 2 * B
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB θ) (by positivity)
  have hpos : 0 < mr ^ 2 * (N : ℝ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [h3]

theorem UpperTheory.Gal.Gen.planch_pf :
    UpperTheory.Gal.Gen.GammaInt → UpperTheory.Gal.Gen.GammaConj → UpperTheory.Gal.Gen.GammaEig → UpperTheory.Gal.Gen.InjAE → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.Planch := by
  intro hInt hConj hEig hInj hDens F _ _ _ _ n _ _ μ _
  have hq : 1 < qF F := by
    unfold qF
    exact Finite.one_lt_card
  have ht0 : (0 : ℝ) ≤ ((qF F : ℝ))⁻¹ := by positivity
  have ht1 : ((qF F : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)
  obtain ⟨_, hDc, hev, hunit⟩ := hDens n _ ht0 ht1
  have htc : Complex.ofReal ((qF F : ℝ))⁻¹ = ((qF F : ℂ))⁻¹ := by push_cast; rfl
  rw [htc] at hDc
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn isCompact_univ hDc.continuousOn
  have hm : 0 < μ.real (GLnLocal.integralGL F n) := by
    apply ENNReal.toReal_pos
    · exact ((GLnLocal.isOpen_integralGL F n).measure_pos μ
        ⟨1, (GLnLocal.integralGL F n).one_mem⟩).ne'
    · exact ((GLnLocal.isCompact_integralGL F n).measure_lt_top).ne
  have hI := hInt F n μ
  have hC := hConj F n μ
  refine ⟨‖vPoly n ((qF F : ℂ))⁻¹‖ * B / (μ.real (GLnLocal.integralGL F n) ^ 2 * n.factorial), ?_⟩
  intro h T hT
  refine sum_norm_sq_le_integral_of_plancherel (GLnLocal.integralGL F n) (fun θ y => zonalSpherical μ (pt θ) y)
    (fun θ => dens ((qF F : ℂ))⁻¹ (pt θ)) (fun θ => evalAt (pt θ) (satakeTransform μ h)) _ T
    (μ.real (GLnLocal.integralGL F n)) B n.factorial (vPoly n ((qF F : ℂ))⁻¹) hm n.factorial_pos
    (fun y => (hI y).1) hDc (hev _) (fun θ => hB θ (Set.mem_univ _))
    (fun y hy => by rw [(hI y).2, if_pos hy])
    (fun y hy => by rw [(hI y).2, if_neg hy])
    (fun θ y => ?_) hT.1 ?_ (fun θ => zonalSpherical_one _)
  · rw [← hT.2 (fun x => zonalSpherical μ (pt θ) (y * x)) fun g k hk => by
      rw [← mul_assoc]
      exact zonalSpherical_mul_right _ _ hk]
    exact hEig F n μ (pt θ) h y
  · filter_upwards [hInj n] with θ hθ
    intro y
    exact hC (pt θ) hθ (hunit θ) y
