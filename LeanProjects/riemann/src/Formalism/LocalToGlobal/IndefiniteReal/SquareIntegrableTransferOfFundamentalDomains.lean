import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta Formalism.L2.SG.RowDict

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ)
    (f : GA D (D.sp.Y 0) → ENNReal) (hf : ∀ γ ∈ GQ (D.sp.Y 0), ∀ x, f (γ * x) = f x) :
    ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕, f y ∂μ := by
  have := Formalism.IndefR.PeterssonHilbertSpace.countable_GQ (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  have hR : μ.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (D.sp.Y 0) μ hH
  let e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0) :=
    { toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }
  have he : (e : X.B.I.GA → GA D (D.sp.Y 0)) = ι.symm := rfl
  set 𝓕' : Set (GA D (D.sp.Y 0)) := ι.symm '' X.B.fund with h𝓕'def
  have hpre : e ⁻¹' 𝓕' = X.B.fund := by
    ext x
    simp only [Set.mem_preimage, h𝓕'def, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := ι.symm.injective (by rw [hxy]; rfl)
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

  have h1 : ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕', f (y * t) ∂μ := by
    have hm : Measure.map e (muX X) = (ENNReal.ofReal c • μ).restrict 𝓕' := by
      rw [← hmap, ← he, MeasurableEquiv.restrict_map, hpre]
    rw [show (∫⁻ x, f (ι.symm x * t) ∂(muX X)) = ∫⁻ y, f (y * t) ∂(Measure.map e (muX X)) from
      (lintegral_map_equiv (fun y => f (y * t)) e).symm, hm, Measure.restrict_smul, lintegral_smul_measure]
    rfl

  have hmp : MeasurePreserving (fun y : GA D (D.sp.Y 0) => y * t) μ μ := measurePreserving_mul_right μ t
  have hemb : MeasurableEmbedding (fun y : GA D (D.sp.Y 0) => y * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  have h2 : ∫⁻ y in 𝓕', f (y * t) ∂μ = ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ :=
    hmp.setLIntegral_comp_emb hemb f 𝓕'
  have himg : (fun y : GA D (D.sp.Y 0) => y * t) '' 𝓕' = (fun y => y * t⁻¹) ⁻¹' 𝓕' := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨z * t⁻¹, hz, by simp⟩
  have hFD : IsFundamentalDomain (GQ (D.sp.Y 0)) ((fun y => y * t) '' 𝓕') μ := by
    rw [himg]
    refine h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ t⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id ?_
    intro γ y
    show (γ : GA D (D.sp.Y 0)) * y * t⁻¹ = (γ : GA D (D.sp.Y 0)) * (y * t⁻¹)
    rw [mul_assoc]
  have h3 : ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ = ∫⁻ y in 𝓕, f y ∂μ :=
    hFD.setLIntegral_eq h𝓕 f (fun γ x => hf γ γ.2 x)
  rw [h1, h2, h3]

theorem squareIntegrableTransfer_of_fundamentalDomains (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 ≤ c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ) :
    SquareIntegrableTransfer μ 𝓕 X ι t c := by
  intro F hFc hinv hF
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  have hmeasG : Measurable (fun x => F (ι.symm x * t)) :=
    hFc.measurable.comp ((measurable_mul_const t).comp hιs)
  have hL := lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral μ 𝓕 X ι t c hι hιs hmap hH h𝓕 h𝓕' (fun y => ENNReal.ofReal (‖F y‖ ^ 2))
    (fun γ hγ x => by simp only [hinv γ hγ x])
  have hint : Integrable (fun y => ‖F y‖ ^ 2) (μ.restrict 𝓕) :=
    (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  have hfin : ∫⁻ y in 𝓕, ENNReal.ofReal (‖F y‖ ^ 2) ∂μ < ⊤ := hint.lintegral_lt_top
  have hasm : AEStronglyMeasurable (fun x => F (ι.symm x * t)) (muX X) := hmeasG.aestronglyMeasurable
  have hint2 : Integrable (fun x => ‖F (ι.symm x * t)‖ ^ 2) (muX X) := by
    refine ⟨(continuous_pow 2).comp_aestronglyMeasurable hasm.norm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity), hL]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨(memLp_two_iff_integrable_sq_norm hasm).2 hint2, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint2.aestronglyMeasurable, hL,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint.aestronglyMeasurable]

theorem fund_image_of (μ : Measure (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 < c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (hrat : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ ι g ∈ X.B.I.GFset) :
    IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ := by
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  obtain ⟨hmf, hcov, hdis⟩ := X.B.fund_spec
  let e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0) :=
    { toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }
  have hset : ι.symm '' X.B.fund = ι ⁻¹' X.B.fund := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨ι y, hy, by simp⟩

  have hnull : ∀ A : Set X.B.I.GA, X.B.I.muA X.B.μf A = 0 → μ (ι ⁻¹' A) = 0 := by
    intro A hA
    have h1 : Measure.map e (X.B.I.muA X.B.μf) (ι ⁻¹' A) = X.B.I.muA X.B.μf A := by
      rw [MeasurableEquiv.map_apply]
      congr 1
      ext x
      simp [e]
    have h2 : (ENNReal.ofReal c • μ) (ι ⁻¹' A) = 0 := by
      rw [← hmap]
      exact h1.trans hA
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
    rcases h2 with h | h
    · exact absurd h (by simpa using hc)
    · exact h
  rw [hset]
  refine IsFundamentalDomain.mk'' (hι hmf).nullMeasurableSet (ae_of_all _ ?_) ?_ ?_
  · intro y
    obtain ⟨γ', hγ', hmem⟩ := hcov (ι y)
    refine ⟨⟨ι.symm γ', (hrat _).2 (by simpa using hγ')⟩, ?_⟩
    show ι (ι.symm γ' * y) ∈ X.B.fund
    simpa using hmem
  · intro γ hγ
    have hγ1 : ι γ ≠ 1 := by
      intro h
      apply hγ
      ext
      simpa using congrArg ι.symm h
    have h0 := hdis (ι γ) ((hrat γ).1 γ.2) hγ1
    refine (measure_mono_null ?_ (hnull _ h0) : μ _ = 0)
    intro y hy
    obtain ⟨⟨z, hz, rfl⟩, hy2⟩ := hy
    refine ⟨⟨ι z, hz, ?_⟩, hy2⟩
    show ι γ * ι z = ι ((γ : GA D (D.sp.Y 0)) * z)
    rw [map_mul]
  · intro γ
    exact (measurePreserving_mul_left μ (γ : GA D (D.sp.Y 0))).quasiMeasurePreserving

theorem squareIntegrableTransfer_of_rational_points (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 < c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (hrat : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ ι g ∈ X.B.I.GFset) :
    SquareIntegrableTransfer μ 𝓕 X ι t c :=
  squareIntegrableTransfer_of_fundamentalDomains μ 𝓕 X ι t c hι hιs hc.le hmap hH h𝓕 (fund_image_of μ X ι c hι hιs hc hmap hH hrat)

theorem measurable_of_borel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA)
    (hB : BorelSpace X.B.I.GA) :
    Measurable (ι.toMulEquiv : GA D (D.sp.Y 0) → X.B.I.GA) ∧
      Measurable (ι.toMulEquiv.symm : X.B.I.GA → GA D (D.sp.Y 0)) := by
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  exact ⟨ι.continuous.measurable, ι.symm.continuous.measurable⟩

end Formalism.IndefR.AutomorphicEvaluation

end
