import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzHadamardLemma
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCharacterInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2Statement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical
namespace GlobalTheory.ArchInvForm

theorem trace_half {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (⅟(2 : mixedEmbedding.mixedSpace F) * z) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z / 2 := by
  have h : (2 : ℝ) • (⅟(2 : mixedEmbedding.mixedSpace F) * z) = z := by
    rw [Algebra.smul_def, map_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have h2 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h
  rw [map_smul, smul_eq_mul] at h2
  linarith

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w φ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ) w φ := by
  funext x
  simp only [schr, GlobalTheory.ArchUniq.schrF, hψ]
  congr 3
  rw [map_add, trace_half]
  rfl

theorem int_phase_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @Measure V (borel V)) (hμ : @Measure.IsAddHaarMeasure V _ _ (borel V) μ)
    (u v p : V → ℂ) (hp : ∀ x, ‖p x‖ = 1) (a : V) :
    @integral V ℂ _ _ (borel V) μ (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) =
      @integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (v x)) := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have e : (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) = fun x => u (x + a) * starRingEnd ℂ (v (x + a)) := by
    funext x
    have h1 : p x * starRingEnd ℂ (p x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp x]; simp
    rw [map_mul]
    linear_combination (u (x + a) * starRingEnd ℂ (v (x + a))) * h1
  rw [e]
  exact integral_add_right_eq_self (μ := μ) (fun x => u x * starRingEnd ℂ (v x)) a

theorem const_of_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro _ F _ _ _ κ _ ψ hψ T A hT
  have hP := GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) κ
  have hnorm : ∀ t, ‖ψ t‖ = 1 := by
    intro t
    rw [hψ, show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t : ℝ) : ℂ) =
      ((-(2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hK : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w (f f₁ g g₁ : SInf F κ), (f₁ : _ → ℂ) = schr ψ w f → (g₁ : _ → ℂ) = schr ψ w g →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ w f f₁ g g₁ hf hg
    have e1 := hT w f f₁ hf
    have e2 := hT w g g₁ hg
    have e : (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) = fun x =>
        (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) * T f (x + (A w).1)) *
          starRingEnd ℂ (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) *
            T g (x + (A w).1)) := by
      funext x
      rw [show T f₁ x = schr ψ (A w) (T f) x from congrFun e1 x, show T g₁ x = schr ψ (A w) (T g) x from congrFun e2 x]
      rfl
    rw [e]
    exact int_phase_shift μ hμ _ _ _ (fun x => hnorm _) _
  have hmod : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f f' g g' : SInf F κ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ L f f' g g' hf hg
    obtain ⟨b, hb⟩ := GlobalTheory.ArchUniqStd.exists_right hP ((-(1 / (2 * Real.pi))) • L)
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = Complex.exp (Complex.I * (L x : ℂ)) * u x) →
        (u' : _ → ℂ) = schr ψ (0, b) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      rw [hu x]
      simp only [GlobalTheory.ArchUniq.schrF]
      rw [add_zero, hP.zero_left, zero_div, add_zero, hb, ContinuousLinearMap.smul_apply, smul_eq_mul]
      congr 2
      push_cast
      field_simp
    exact hK μ hμ (0, b) f f' g g' (hw f f' hf) (hw g g' hg)
  have htr : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (a : κ → mixedEmbedding.mixedSpace F) (f f' g g' : SInf F κ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ a f f' g g' hf hg
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = u (x + a)) → (u' : _ → ℂ) = schr ψ (a, 0) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      simp [GlobalTheory.ArchUniq.schrF, hu, hP.zero_right]
    exact hK μ hμ (a, 0) f f' g g' (hw f f' hf) (hw g g' hg)
  letI mV : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  set μ₀ : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar with hμ₀
  have hμ₀H : μ₀.IsAddHaarMeasure := by rw [hμ₀]; infer_instance
  obtain ⟨c, hc⟩ := GlobalTheory.T.translation_invariant_form_const_l2 _ μ₀ hμ₀H T (htr μ₀ hμ₀H) (GlobalTheory.T.translation_character_invariant_form _ μ₀ hμ₀H T (hmod μ₀ hμ₀H))
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.ArchUniqStd.exists_one (V := κ → mixedEmbedding.mixedSpace F)
  have hself : ∀ h : SInf F κ, ∫ x, h x * starRingEnd ℂ (h x) ∂μ₀ = ((∫ x, ‖h x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) :=
    fun h => GlobalTheory.WrongSignGauss.ip_self μ₀ h
  have hint : Integrable (fun x => ‖Φ x‖ ^ 2) μ₀ := by
    refine (GlobalTheory.WrongSignGauss.integrable_ip μ₀ Φ Φ).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  have hn : 0 < ∫ x, ‖Φ x‖ ^ 2 ∂μ₀ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
    have ho : IsOpen (Function.support fun x => ‖Φ x‖ ^ 2) := (Φ.continuous.norm.pow 2).isOpen_support
    exact ho.measure_pos μ₀ ⟨0, by simp [hΦ]⟩
  have hm : 0 ≤ ∫ x, ‖T Φ x‖ ^ 2 ∂μ₀ := integral_nonneg fun x => sq_nonneg _
  have hcΦ := hc Φ Φ
  change ∫ x, T Φ x * starRingEnd ℂ (T Φ x) ∂μ₀ = c * ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ₀ at hcΦ
  rw [hself, hself] at hcΦ
  have hcc : c = (((∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀) : ℝ) : ℂ) := by
    have hn' : ((∫ x, ‖Φ x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    rw [eq_div_iff hn', hcΦ]
  refine ⟨(∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀), div_nonneg hm hn.le, fun μ hμ f f' => ?_⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hs : μ = Measure.addHaarScalarFactor μ μ₀ • μ₀ := Measure.isAddLeftInvariant_eq_smul μ μ₀
  have hcf := hc f f'
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ₀ = c * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ₀ at hcf
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ = _ * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ
  rw [hs, integral_smul_nnreal_measure, integral_smul_nnreal_measure, hcf, ← hcc]
  simp only [NNReal.smul_def, smul_eq_mul, Complex.real_smul]
  ring

end GlobalTheory.ArchInvForm
