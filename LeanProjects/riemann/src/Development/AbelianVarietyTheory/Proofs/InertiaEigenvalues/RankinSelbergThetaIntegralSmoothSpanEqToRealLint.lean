import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPoleToc

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem eq_ofReal_norm {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.im = 0) : z = ((‖z‖ : ℝ) : ℂ) := by
  have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]

theorem rsPsi_self_eq (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  set u : Fin a → Cinf E := fun i => pInf E (y i)
  set w := g * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ u))⁻¹
  set s : ℝ := (GlobalTheory.ThetaPoisson.latt a J).indicator 1 ((fun i => pFin E (y i)) - η)
  have hs : (GlobalTheory.ThetaPoisson.latt a J).indicator (1 : (Fin a → Af E) → ℂ) ((fun i => pFin E (y i)) - η) = (s : ℂ) := by
    classical
    simp only [s]; rw [Set.indicator_apply, Set.indicator_apply]; split_ifs <;> simp
  have hs0 : 0 ≤ s := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hΦu : Φ u = (((Φ u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(hΦ u).2])
  have e : GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((Complex.normSq (F w) * (Φ u).re * s : ℝ) : ℂ) := by
    simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf]
    rw [hs, Complex.mul_conj, hΦu]
    push_cast
    rfl
  refine eq_ofReal_norm ?_ ?_
  · rw [e, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hΦ u).1) hs0
  · rw [e, Complex.ofReal_im]

theorem tsum_eq_toReal {ι : Type} (f : ι → ℂ) (hf : ∀ i, f i = ((‖f i‖ : ℝ) : ℂ)) :
    ∑' i, f i = (((∑' i, ‖f i‖ₑ).toReal : ℝ) : ℂ) := by
  rw [ENNReal.tsum_toReal_eq fun _ => enorm_ne_top, Complex.ofReal_tsum]
  exact tsum_congr fun i => by rw [toReal_enorm, ← hf i]

theorem thetaZ_eq_toReal (ℓ : Fin a) (F : GA E a → ℂ) (hF : Continuous F) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ) (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (x : ℝ)
    (hfin : ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤) :
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
                 ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
                 ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  set G : GA E a → ℝ≥0∞ := fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) with hG

  have hcont : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, Continuous fun g : GA E a => GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) := by
    intro ξ
    have h1 : Continuous fun g : GA E a =>
        (g, (fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g.val : Matrix (Fin a) (Fin a) (Ad E))) :=
      continuous_id.prodMk (continuous_const.matrix_vecMul Units.continuous_val)
    have h2 := GlobalTheory.RSTheta.continuous_rsPsi hF hF hΦc hΦs J η
    have h3 := h2.comp h1
    exact h3
  have hdet : Continuous fun g : GA E a => ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    have h : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
      continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
    exact h.rpow_const fun g => Or.inl (ideleModule E (GeneralLinearGroup.det g)).2.ne'
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (ENNReal.measurable_ofReal.comp hdet.measurable)
    exact (lowerSemicontinuous_tsum fun ξ => (hcont ξ).enorm.lowerSemicontinuous).measurable

  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
      ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) = (((G g).toReal : ℝ) : ℂ) := by
    intro g
    rw [tsum_eq_toReal _ fun ξ => rsPsi_self_eq ℓ F Φ hΦ J η g _, hG]
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (ideleModule E (GeneralLinearGroup.det g)).2.le x), Complex.ofReal_mul]
  have hae : ∀ᵐ g ∂μ.restrict 𝓕, G g < ⊤ := ae_lt_top hGm hfin
  calc GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = ∫ g in 𝓕, (((G g).toReal : ℝ) : ℂ) ∂μ := by
        rw [GlobalTheory.RSPole.thetaZ]; exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((∫ g in 𝓕, (G g).toReal ∂μ : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_toReal hGm.aemeasurable hae]

theorem thetaZ_eq_toReal_lintegral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → Continuous F →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ →
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a ℓ π F _ hF Φ hΦc hΦs hΦ J η μ _ 𝓕 _ x hfin
  exact thetaZ_eq_toReal ℓ F hF Φ hΦc hΦs hΦ J η μ 𝓕 x hfin

end GlobalTheory.RSPoleToc
