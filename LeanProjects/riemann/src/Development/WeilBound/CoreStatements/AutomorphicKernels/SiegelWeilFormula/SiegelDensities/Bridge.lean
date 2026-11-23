import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.SWMeasCAll

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal Matrix

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eSp_eq (v : HeightOneSpectrum (𝓞 F)) :
    PositivityTheory.SiegelWeilFormula.Gen.eSp E v = ((eR E v : ℝ) : ℂ) ∧ (eR E v = 1 ∨ eR E v = -1) := by
  unfold eR PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs <;> simp

theorem one_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h

theorem cfac_eq (v : HeightOneSpectrum (𝓞 F)) :
    (((cfac E v : ℝ≥0) : ℝ) : ℂ) = (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v / (Ideal.absNorm v.asIdeal : ℂ))⁻¹ := by
  obtain ⟨h1, h2⟩ := eSp_eq (E := E) v
  have hq := one_le_absNorm v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hr : 0 ≤ 1 - eR E v / (Ideal.absNorm v.asIdeal : ℝ) := by
    rcases h2 with h | h <;> rw [h]
    · rw [sub_nonneg, div_le_one hq0]; exact hq
    · have : 0 ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by positivity
      rw [neg_div]; linarith
  rw [h1, cfac, Real.coe_toNNReal _ (inv_nonneg.2 hr)]
  push_cast
  rfl

end Local

theorem isEulerProd_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0)
    (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (h : IsEulerProd b I c minf m) : IsEulerProd b I 1 (c • minf) m := by
  obtain ⟨h1, h2, S₀, h3⟩ := h
  refine ⟨h1, h2, S₀, fun S hS φinf φ hφi hφ => ?_⟩
  rw [h3 S hS φinf φ hφi hφ, lintegral_smul_measure, ENNReal.smul_def]
  simp only [ENNReal.coe_one, one_mul, smul_eq_mul]
  ring

theorem densEq_of_C (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) (hC : SWMeasCAll) : PositivityTheory.SiegelWeilFormula.Gen.DensEq := by
  intro F E _ _ _ _ _ σ hCM M hM J hJ haJ T hT hdet d b Φ Φinf Φf Φv hsch hpure hprod
  have ha : PositivityTheory.PfSWUS.HMass.IsAnisoH σ J := fun x hx h0 => hx (haJ x h0)
  have hfv : FinVol F E σ M J := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  refine ⟨hfv.1, fun μ hμ => ⟨(hfv.2 μ hμ).1, fun 𝓕 h𝓕 =>
    ⟨GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F, fun ψ hψ => ?_⟩⟩⟩
  obtain ⟨⟨laminf, hli⟩, hlv⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlv
  obtain ⟨ci, c, hc1, hWi, hWv⟩ := GlobalTheory.T.exists_unit_scaling_selfdual_adelic_measures F E σ hCM M J hJ d b laminf lam hli hlam ψ hψ M
  obtain ⟨ei, e, he1, hHi, hHv⟩ := GlobalTheory.T.exists_unit_scaling_selfdual_herm_measures F E σ hCM d b laminf lam hli hlam ψ hψ M
  obtain ⟨hci0, hc0, -, -, hdiv, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ei c e hc1 he1
  obtain ⟨hei0, he0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ei ci e c he1 hc1
  refine ⟨⟨_, (hWi _).2 rfl⟩, fun μinf hμinf => ⟨⟨_, (hHi _).2 rfl⟩, fun νinf hνinf =>
    ⟨⟨_, fun v => (hWv v _).2 rfl⟩, fun μv hμv => ⟨⟨_, fun v => (hHv v _).2 rfl⟩, fun νv hνv => ?_⟩⟩⟩⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have key : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
      IsLocR R → ∀ l : Measure R, l.IsAddHaarMeasure →
      ∃ m : HermR R σ M → Measure (Fin M → Fin M → R ⊗[F] E),
        IsGramFib R σ J M (coordW R b l M M) (coordHerm R σ b l M) m ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧
        ∀ (a a' : ℝ≥0), a ≠ 0 → a' ≠ 0 → (a • coordW R b l M M).IsAddHaarMeasure →
          (a' • coordHerm R σ b l M).IsAddHaarMeasure →
          ∀ φ : (Fin M → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ →
          IsContDensityOn (a • coordW R b l M M) (gramR R σ J) Subtype.val (a' • coordHerm R σ b l M)
            {S | IsUnit (S : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det} φ
            (fun S => (a / a') • ∫ X, φ X ∂(m S)) := by
    intro R _ _ _ _ _ hR l hl
    obtain ⟨i1, i2, i3, i4, -⟩ := id hR
    obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b l hl
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ R hR M _ _ (hW M M) (hH M)
    refine ⟨m, hm, fun S => (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR M _ _ m (hW M M) (hH M) hm S).1, ?_⟩
    intro a a' ha ha' h1 h2 φ hφ hφc
    have h3 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hCM M J hJ R hR M _ _ m (hW M M) (hH M) hm a a' ha ha'
    have h4 := (GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM M J hJ R hR M _ _ _ h1 h2 h3 φ hφ hφc).1
    simpa only [integral_smul_nnreal_measure] using h4
  have keyi : ∃ m : HermR (Ainf F) σ M → Measure (Fin M → Fin M → Ainf F ⊗[F] E),
      IsGramFib (Ainf F) σ J M (coordW (Ainf F) b laminf M M) (coordHerm (Ainf F) σ b laminf M) m ∧
      (∀ S, IsLocallyFiniteMeasure (m S)) ∧ Continuous Φinf ∧
      (∀ S : HermR (Ainf F) σ M, IsUnit (S : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).det → Integrable Φinf (m S)) ∧
      ∀ (a a' : ℝ≥0), a ≠ 0 → a' ≠ 0 → (a • coordW (Ainf F) b laminf M M).IsAddHaarMeasure →
        (a' • coordHerm (Ainf F) σ b laminf M).IsAddHaarMeasure →
        IsContDensityOn (a • coordW (Ainf F) b laminf M M) (gramR (Ainf F) σ J) Subtype.val
          (a' • coordHerm (Ainf F) σ b laminf M)
          {S | IsUnit (S : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).det} Φinf
          (fun S => (a / a') • ∫ X, Φinf X ∂(m S)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := id hLi
    obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hli.1
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ (Ainf F) hLi M _ _ (hW M M) (hH M)
    obtain ⟨hcI, -, hiI⟩ := hB F E σ hCM M J hJ M _ _ m (hW M M) (hH M) hm Φinf hsch
    refine ⟨m, hm, fun S => (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Ainf F) hLi M _ _ m (hW M M) (hH M) hm S).1,
      hcI, hiI, ?_⟩
    intro a a' ha ha' h1 h2
    have h3 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hCM M J hJ (Ainf F) hLi M _ _ m (hW M M) (hH M) hm a a' ha ha'
    have h4 := (hB F E σ hCM M J hJ M _ _ _ h1 h2 h3 Φinf hsch).2.1
    simpa only [integral_smul_nnreal_measure] using h4
  obtain ⟨minf, hmi, hfi, hcI, hiI, hdi⟩ := keyi
  choose m hm hf hd using fun v => key (Fv F v) (hLv v) (lam v) (hlam v).1
  have e1 := (hWi μinf).1 hμinf
  have e2 := (hHi νinf).1 hνinf
  have e3 := fun v => (hWv v (μv v)).1 (hμv v)
  have e4 := fun v => (hHv v (νv v)).1 (hνv v)
  obtain ⟨κ, hE, hκ⟩ := hC F E σ hCM M hM J hJ ha T hT hdet d b laminf lam hli hlam μ 𝓕 hμ h𝓕 minf m hmi hm
  have hE1 := isEulerProd_smul b _ κ _ _ hE
  haveI : IsLocallyFiniteMeasure (minf (hermOf (Ainf F) σ T hT)) := hfi _
  have hlf : ∀ v, IsLocallyFiniteMeasure (cfac E v • m v (hermOf (Fv F v) σ T hT)) := fun v => by
    haveI := hf v (hermOf (Fv F v) σ T hT)
    infer_instance
  obtain ⟨hmeas, hint, hmul, hI⟩ := PositivityTheory.PfSWUS.HMass.euler_int_integrable F E σ hCM d b M M _ _ _ hE1
    inferInstance hlf Φ Φinf Φf Φv hcI
    ((hiI _ (PositivityTheory.PfSWUS.HMass.isUnit_det_hermOf (Ainf F) σ T hT hdet)).smul_measure_nnreal) hpure hprod
  have hθ := GlobalTheory.T.siegel_mean_value_integrable F E σ hCM M J hJ μ 𝓕 hμ h𝓕 M _ Φ hmeas hint
  have hz : Multipliable fun v => (cfac E v : ℝ≥0) • ∫ X, Φv v X ∂(m v (hermOf (Fv F v) σ T hT)) := by
    simpa only [integral_smul_nnreal_measure] using hmul
  obtain ⟨r1, r2⟩ := GlobalTheory.CompanionTheory.SW.TopDens.rescale_tprod (ci / ei) (fun v => c v / e v) hdiv.1 hdiv.2
    (∫ X, Φinf X ∂(minf (hermOf (Ainf F) σ T hT))) _ hz
  have hgv : ∀ v, ((c v / e v) • ∫ X, Φv v X ∂(m v (hermOf (Fv F v) σ T hT))) /
      (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v / (Ideal.absNorm v.asIdeal : ℂ)) =
      (c v / e v) • ((cfac E v : ℝ≥0) • ∫ X, Φv v X ∂(m v (hermOf (Fv F v) σ T hT))) := by
    intro v
    rw [div_eq_mul_inv, ← cfac_eq]
    simp only [NNReal.smul_def, Complex.real_smul]
    ring
  refine ⟨fun S => (ci / ei) • ∫ X, Φinf X ∂(minf S), fun v S => (c v / e v) • ∫ X, Φv v X ∂(m v S),
    ?_, fun v => ?_, ?_, ?_⟩
  · have := hdi ci ei hci0 hei0 (e1 ▸ hμinf.1) (e2 ▸ hνinf.1)
    rwa [← e1, ← e2] at this
  · have := hd v (c v) (e v) (hc0 v) (he0 v) (e3 v ▸ (hμv v).1) (e4 v ▸ (hνv v).1) (Φv v)
      (hpure.1 v).1.continuous (hpure.1 v).2
    rwa [← e3 v, ← e4 v] at this
  · simp only [hgv]
    exact r1
  · intro Λ hΛ
    rw [hθ, hI, tprod_congr hgv, integral_smul_nnreal_measure]
    simp only [integral_smul_nnreal_measure]
    rw [mul_comm _ Λ, mul_assoc Λ, r2, NNReal.smul_def, Complex.real_smul, hκ Λ hΛ]
    ring

end PositivityTheory.SiegelWeilFormula.Densx

end
