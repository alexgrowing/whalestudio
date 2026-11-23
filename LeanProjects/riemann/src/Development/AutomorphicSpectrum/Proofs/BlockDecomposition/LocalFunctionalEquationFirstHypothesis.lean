import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementVectorDecayBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVectorGaugeBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierContinuousBoundedSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OuterZetaIntegrandBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOuterZetaIntegrandStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralEqGroupIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralTranslateInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralIwasawaMajorantFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandEqIteratedIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestVectorNonvanishingLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaPullback
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem second_row_unipotent_invariant (x : F) (h : GL (Fin 2) F) : e2r (uni2 x * h) = e2r h := by
  ext i
  fin_cases i <;> simp [e2r, uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem Bq_uni (ψ : AddChar F Circle) {W₀ W' : GL (Fin 2) F → ℂ} (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ)
    (h₀ : ∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) (h₁ : ∀ x g, W' (uni2 x * g) = (ψ⁻¹ x : ℂ) * W' g)
    (g : GL (Fin 2) F) (x : F) (h : GL (Fin 2) F) :
    Bq ψ W₀ W' Φ s g (uni2 x * h) = Bq ψ W₀ W' Φ s g h := by
  have hc : (ψ x : ℂ) * (ψ⁻¹ x : ℂ) = 1 := by
    rw [← Circle.coe_mul, AddChar.inv_apply', mul_inv_cancel, Circle.coe_one]
  unfold Bq
  rw [h₀ x h, mul_assoc (uni2 x) h g, h₁ x (h * g), second_row_unipotent_invariant, map_mul, GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.det_unipotent_adele, one_mul]
  linear_combination (W₀ h * W' (h * g) * pFT ψ Φ g.val (e2r h) * mp (GeneralLinearGroup.det h) s) * hc

omit [MeasurableSpace F] [BorelSpace F] in
theorem wR_eq (p : Fˣ × Fˣ × GL (Fin 2) F) : ((wR p : ℝ) : ℂ) = mp p.1 (-1) := by
  rw [wR, mp, Complex.cpow_neg_one]
  push_cast
  rfl

theorem zeta_integrand_iwasawa_eq_bilinear (ψ : AddChar F Circle) (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ)
    (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) :
    z2I W₀ (tr2 W' g) (pFT ψ Φ g.val) s p = ((wR p : ℝ) : ℂ) * Bq ψ W₀ W' Φ s g (hI p) := by
  have e : mp p.1 (s - 1) = mp p.1 (-1) * mp p.1 s := by
    rw [← GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.mp_add]; congr 1; ring
  rw [z2I, Bq, GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.mp_det_hI p hp, wR_eq, e, tr2]
  ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_mp (s : ℂ) : Continuous fun h : Fˣ => mp h s := by
  have hc : Continuous fun h : Fˣ => (((modulus (h : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  simp only [mp]
  refine hc.cpow continuous_const fun h => ?_
  have h0 : (0 : ℝ) < (modulus (h : F) : ℝ) := by exact_mod_cast modulus_pos h.ne_zero
  exact Complex.ofReal_mem_slitPlane.2 h0

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_det : Continuous fun h : GL (Fin 2) F => (GeneralLinearGroup.det h : Fˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_det
  · have : (fun h : GL (Fin 2) F => (((GeneralLinearGroup.det h)⁻¹ : Fˣ) : F)) =
        fun h : GL (Fin 2) F => ((h⁻¹ : GL (Fin 2) F).val).det := by
      funext h
      rw [← map_inv]
      rfl
    exact this ▸ ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).comp continuous_inv).matrix_det

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_second_vector_GL2 : Continuous (e2r : GL (Fin 2) F → Fin 2 → F) := by
  refine continuous_pi fun i => ?_
  have hv := Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)
  fin_cases i
  · exact hv.matrix_elem 1 0
  · exact hv.matrix_elem 1 1

theorem cont_Bq (ψ : AddChar F Circle) {W₀ W' : GL (Fin 2) F → ℂ} {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (s : ℂ)
    (c₀ : Continuous W₀) (c₁ : Continuous W')
    (cP : Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2)) (g : GL (Fin 2) F) :
    Continuous (Bq ψ W₀ W' Φ s g) := by
  show Continuous fun h => W₀ h * W' (h * g) * pFT ψ Φ g.val (e2r h) * mp (GeneralLinearGroup.det h) s
  have a1 : Continuous fun h : GL (Fin 2) F => pFT ψ Φ g.val (e2r h) :=
    cP.comp (continuous_const.prodMk continuous_second_vector_GL2)
  exact ((c₀.mul (c₁.comp (continuous_id.mul continuous_const))).mul a1).mul ((cont_mp s).comp cont_det)

theorem fixg (ψ : AddChar F Circle) (hψ : IsStd ψ) {W₀ W' : GL (Fin 2) F → ℂ} {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (s : ℂ)
    (c₀ : Continuous W₀) (c₁ : Continuous W')
    (cP : Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2))
    (h₀ : ∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) (h₁ : ∀ x g, W' (uni2 x * g) = (ψ⁻¹ x : ℂ) * W' g)
    (g : GL (Fin 2) F) :
    ∫ p, Aq ψ W₀ W' Φ s (p, g) ∂mIw ψ =
      mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) (pFT ψ Φ g.val) s := by
  have key := GlobalTheory.T.iwasawa_integral_translate_invariance F ψ hψ (Bq ψ W₀ W' Φ s g) (cont_Bq ψ s c₀ c₁ cP g) (Bq_uni ψ Φ s h₀ h₁ g) g⁻¹
  have e : ∫ p, Aq ψ W₀ W' Φ s (p, g) ∂mIw ψ = mp (GeneralLinearGroup.det g) (s + 1 / 2) *
      ∫ p, ((wR p : ℝ) : ℂ) * Bq ψ W₀ W' Φ s g (hI p * g⁻¹) ∂mIw ψ := by
    simp only [Aq]
    exact integral_const_mul _ _
  rw [e, key]
  congr 1
  exact integral_congr_ae ((GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ).mono fun p hp => (zeta_integrand_iwasawa_eq_bilinear ψ W₀ W' Φ s g p hp).symm)

omit [MeasurableSpace F] [BorelSpace F] in
theorem enorm_mp (a : Fˣ) (z : ℂ) :
    ‖mp a z‖ₑ = ENNReal.ofReal ((modulus (a : F) : ℝ) ^ z.re) := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  rw [← ofReal_norm, mp, Complex.norm_cpow_eq_rpow_re_of_pos h0]

omit [MeasurableSpace F] [BorelSpace F] in
theorem enorm_wR (p : Fˣ × Fˣ × GL (Fin 2) F) : ‖((wR p : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (wR p) := by
  have h0 : 0 ≤ wR p := inv_nonneg.2 (by positivity)
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

theorem aqi (ψ : AddChar F Circle) (hψ : IsStd ψ) (ω : Fˣ →* ℂˣ) (G : (Fˣ →* ℂˣ) → ℂ → ℂ)
    (V' : Submodule ℂ (GL (Fin 2) F → ℂ)) (hω : IsUnit1 ω) (H : WhT ψ⁻¹ ω G V') (ν : Fˣ →* ℂˣ) (hν : IsUnit1 ν)
    (W₀ : GL (Fin 2) F → ℂ) (hW₀ : W₀ ∈ V2 ψ ν ν⁻¹) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (hΦ : Φ ∈ LFS.SB F)
    (W' : GL (Fin 2) F → ℂ) (hW' : W' ∈ V') (s : ℂ) (hs : 0 < s.re) :
    Integrable (Aq ψ W₀ W' Φ s) ((mIw ψ).prod (LFS.hG ψ)) := by
  haveI : SFinite (LFS.hG ψ) := by unfold LFS.hG; infer_instance
  haveI : SFinite (mIw ψ) := by unfold mIw; infer_instance
  obtain ⟨h₀, hcen, c₀, hb₀⟩ := GlobalTheory.T.godement_vector_decay_bound F ψ hψ ν hν W₀ hW₀
  obtain ⟨c₁, hb₁⟩ := GlobalTheory.T.whittaker_vector_gauge_bound F ψ hψ ω G V' hω H W' hW'
  obtain ⟨cP, C₂, R, hC₂, hbP⟩ := GlobalTheory.T.partial_fourier_continuous_bounded_support F ψ hψ Φ hΦ
  obtain ⟨ε, hε, hε2, hσ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 2 * ε < s.re :=
    ⟨min (s.re / 4) (1 / 4), lt_min (by positivity) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num),
      by have := min_le_left (s.re / 4) (1 / 4); linarith⟩
  obtain ⟨C₀, B, hC₀, hW⟩ := hb₀ ε hε
  obtain ⟨C₁, hC₁, hWb⟩ := hb₁ ε hε
  have hptb := GlobalTheory.T.outer_zeta_integrand_bound F ψ hψ W₀ W' Φ s C₀ C₁ C₂ B R ε hC₀ hC₁ hC₂ hε hε2 hcen hW hWb hbP
  have hbnd := GlobalTheory.T.lintegral_iwasawa_majorant_finite F ψ hψ R B s.re ε hε hσ hε2
  have hc := GlobalTheory.T.continuous_outer_zeta_integrand F ψ hψ W₀ W' Φ s c₀ c₁ cP
  have hm : Measurable (fun q => ‖Aq ψ W₀ W' Φ s q‖ₑ) := hc.enorm.measurable
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.aemeasurable]
  set CC : ENNReal := ENNReal.ofReal (C₀ * C₁ * C₂) with hCC
  have step : ∀ g : GL (Fin 2) F, ∫⁻ p, ‖Aq ψ W₀ W' Φ s (p, g)‖ₑ ∂mIw ψ ≤
      CC * (ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) *
        ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ) := by
    intro g
    set D : ENNReal := ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) with hD
    have hdet : ‖mp (GeneralLinearGroup.det g) (s + 1 / 2)‖ₑ = D := by
      rw [enorm_mp, hD]
      simp [Matrix.GeneralLinearGroup.val_det_apply]
    have hf : Measurable fun h => ‖Bq ψ W₀ W' Φ s g h‖ₑ := (cont_Bq ψ s c₀ c₁ cP g).enorm.measurable
    have hr := GlobalTheory.T.iwasawa_integral_right_translate_invariant F ψ hψ (fun h => ‖Bq ψ W₀ W' Φ s g h‖ₑ) hf
      (fun x h => by simp only [Bq_uni ψ Φ s h₀ (H.psi W' hW') g x h]) g⁻¹
    calc ∫⁻ p, ‖Aq ψ W₀ W' Φ s (p, g)‖ₑ ∂mIw ψ
        = ∫⁻ p, D * (ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p * g⁻¹)‖ₑ) ∂mIw ψ := by
          refine lintegral_congr fun p => ?_
          simp only [Aq]
          rw [enorm_mul, enorm_mul, hdet, enorm_wR]
      _ = D * ∫⁻ p, ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p * g⁻¹)‖ₑ ∂mIw ψ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = D * ∫⁻ p, ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p)‖ₑ ∂mIw ψ := by rw [hr]
      _ ≤ D * ∫⁻ p, CC * (ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p)) ∂mIw ψ := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_ae ((GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ).mono fun p hp => ?_)
          have hb := hptb g p hp
          have : ‖Bq ψ W₀ W' Φ s g (hI p)‖ₑ ≤ CC * ENNReal.ofReal (Mj R B s.re ε g p) := by
            rw [hCC, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hb
          calc ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p)‖ₑ
              ≤ ENNReal.ofReal (wR p) * (CC * ENNReal.ofReal (Mj R B s.re ε g p)) := by gcongr
            _ = CC * (ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p)) := by ring
      _ = CC * (D * ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
  calc ∫⁻ g, ∫⁻ p, ‖Aq ψ W₀ W' Φ s (p, g)‖ₑ ∂mIw ψ ∂LFS.hG ψ
      ≤ ∫⁻ g, CC * (ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) *
        ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ) ∂LFS.hG ψ :=
        lintegral_mono step
    _ = CC * ∫⁻ g, ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) *
        ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ ∂LFS.hG ψ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbnd

end D

theorem main : A1 := by
  intro F _ _ _ _ _ _ ψ hψ ω G V' hω H ν hν W₀ hW₀ Φ hΦ W' hW' s hs0 hs1
  haveI : SFinite (LFS.hG ψ) := by unfold LFS.hG; infer_instance
  haveI : SFinite (mIw ψ) := by unfold mIw; infer_instance
  have hA := aqi ψ hψ ω G V' hω H ν hν W₀ hW₀ Φ hΦ W' hW' s hs0
  obtain ⟨h1, h2, h3, _⟩ := GlobalTheory.T.godement_vector_decay_bound F ψ hψ ν hν W₀ hW₀
  have hc' := (GlobalTheory.T.whittaker_vector_gauge_bound F ψ hψ ω G V' hω H W' hW').1
  have hP := (GlobalTheory.T.partial_fourier_continuous_bounded_support F ψ hψ Φ hΦ).1
  have hpt : ∀ᵐ p ∂mIw ψ, iw (LFS.Wp ψ W₀ Φ) W' s p = ∫ g, Aq ψ W₀ W' Φ s (p, g) ∂LFS.hG ψ :=
    (GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ).mono fun p hp => GlobalTheory.T.iwasawa_integral_eq_group_integral F ψ hψ W₀ W' Φ s hΦ p hp
  have hg := fixg ψ hψ (W₀ := W₀) (W' := W') (Φ := Φ) s h3 hc' hP h1 (H.psi W' hW')
  refine ⟨?_, ?_, ?_⟩
  · exact hA.integral_prod_left.congr (hpt.mono fun _ h => h.symm)
  · have := hA.integral_prod_right
    simpa only [hg] using this
  · unfold zetaGL3GL2
    rw [integral_congr_ae hpt,
      integral_integral_swap (f := fun p g => Aq ψ W₀ W' Φ s (p, g)) hA]
    simp only [hg]

end GlobalTheory.CompanionTheory.GL2Unfolding
