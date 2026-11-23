import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnLaplaceIntegralRightHalfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableModulusPowOnBoundedUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWhittakerIwasawaCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDualRankinSelbergIntegrandStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHolo

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mp_eq_exp (a : Fˣ) (s : ℂ) :
    mp a s = Complex.exp (((Real.log (modulus (a : F) : ℝ) : ℝ) : ℂ) * s) := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have h1 : (((modulus (a : F) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [mp]
  rw [Complex.cpow_def_of_ne_zero h1, Complex.ofReal_log h0.le]

theorem norm_mp' (a : Fˣ) (z : ℂ) : ‖mp a z‖ = (modulus (a : F) : ℝ) ^ z.re := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  simp only [mp]
  exact Complex.norm_cpow_eq_rpow_re_of_pos h0 z

theorem modulus_mul' (a b : Fˣ) :
    (modulus ((a * b : Fˣ) : F) : ℝ) = (modulus (a : F) : ℝ) * (modulus (b : F) : ℝ) := by
  rw [Units.val_mul, modulus_mul]
  push_cast
  rfl

theorem exponents {A B σ ε : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * B) ^ (1 - ε) * A ^ (1 / 2 - ε) * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) * (A ^ σ * B ^ (2 * σ)) =
      A ^ (σ - 2 * ε) * B ^ (2 * σ - ε) := by
  have e1 : A ^ (σ - 2 * ε) = A ^ (1 - ε) * A ^ (1 / 2 - ε) * A ^ (-(3 / 2) : ℝ) * A ^ σ := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA, ← Real.rpow_add hA]
    congr 1
    ring
  have e2 : B ^ (2 * σ - ε) = B ^ (1 - ε) * B ^ (-1 : ℝ) * B ^ (2 * σ) := by
    rw [← Real.rpow_add hB, ← Real.rpow_add hB]
    congr 1
    ring
  rw [e1, e2, Real.mul_rpow hA.le hB.le]
  ring

end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def gI (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) : ℂ :=
  GL2LocalData.dW3 W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * GL2LocalData.dW2 W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2) *
    mp p.1 (-(3 / 2)) * mp p.2.1 (-1)

def lI (p : Fˣ × Fˣ × GL (Fin 2) F) : ℝ :=
  Real.log (modulus (p.1 : F) : ℝ) + 2 * Real.log (modulus (p.2.1 : F) : ℝ)

theorem measurable_lI : Measurable (lI (F := F)) := by
  have hl : Measurable (fun a : Fˣ => Real.log (modulus (a : F) : ℝ)) :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp
      (continuous_modulus.comp Units.continuous_val)).measurable
  exact (hl.comp measurable_fst).add ((hl.comp (measurable_fst.comp measurable_snd)).const_mul 2)

theorem measurable_gI {W : GL (Fin 3) F → ℂ} {W' : GL (Fin 2) F → ℂ} (h3 : TemperedBoundGL3 W) (h2 : TemperedBoundGL2 W') :
    Measurable (gI W W') := by
  have hc : ∀ z : ℂ, Measurable (fun a : Fˣ => mp a z) := fun z => by
    have h1 : Continuous (fun a : Fˣ => (((modulus (a : F) : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (continuous_modulus.comp Units.continuous_val))
    refine (h1.cpow continuous_const fun a => Or.inl ?_).measurable
    have : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
    simpa using this
  exact ((GlobalTheory.T.measurable_dual_rankin_selberg_integrand F W W' h3.1 h2.1).mul ((hc _).comp measurable_fst)).mul
    ((hc _).comp (measurable_fst.comp measurable_snd))

theorem ae_mem_maximal_compact (ψ : AddChar F Circle) [SFinite ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F))] :
    ∀ᵐ p ∂GL2LocalData.mIw ψ, p.2.2 ∈ GL2LocalData.K2 F := by
  have hKm : MeasurableSet (GL2LocalData.K2 F) := (GLnLocal.isCompact_integralGL F 2).isClosed.measurableSet
  have h0 : ∀ᵐ k ∂((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F)), k ∈ GL2LocalData.K2 F := ae_restrict_mem hKm
  have h1 : ∀ᵐ z ∂((multHaar F).prod ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F))), z.2 ∈ GL2LocalData.K2 F :=
    Measure.quasiMeasurePreserving_snd.ae h0
  exact Measure.quasiMeasurePreserving_snd.ae h1

theorem bound_gI {W : GL (Fin 3) F → ℂ} {W' : GL (Fin 2) F → ℂ} {ε σ C₃ B₃ C₂ : ℝ}
    (hb₃ : ∀ (t₁ t₂ t₃ : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
      ‖W (dg t₁ t₂ t₃ * k)‖ ≤ C₃ * (modulus ((t₁ / t₃ : Fˣ) : F) : ℝ) ^ (1 - ε) ∧
      (W (dg t₁ t₂ t₃ * k) ≠ 0 →
        (modulus ((t₁ / t₂ : Fˣ) : F) : ℝ) ≤ B₃ ∧ (modulus ((t₂ / t₃ : Fˣ) : F) : ℝ) ≤ B₃))
    (hb₂ : ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W' (dg2 x y * k)‖ ≤ C₂ * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε))
    (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ GL2LocalData.K2 F) :
    ‖gI W W' p‖ * Real.exp (σ * lI p) ≤ (max C₃ 0 * max C₂ 0) *
      (Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ (σ - 2 * ε)) p.1 *
      (Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ (2 * σ - ε)) p.2.1 * 1)) := by
  obtain ⟨a, b, k⟩ := p
  obtain ⟨k₃, hk₃, k₂, hk₂, e3, e2⟩ := GlobalTheory.T.dual_whittaker_iwasawa_coordinates F a b k hp
  have hA : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hB : (0 : ℝ) < (modulus (b : F) : ℝ) := by exact_mod_cast modulus_pos b.ne_zero
  have q1 : ((1 : Fˣ) / (a * b)⁻¹) = a * b := by simp
  have q2 : ((1 : Fˣ) / b⁻¹) = b := by simp
  have q3 : (b⁻¹ / (a * b)⁻¹ : Fˣ) = a := by
    rw [div_inv_eq_mul, mul_comm a b, inv_mul_cancel_left]
  obtain ⟨n3, s3⟩ := hb₃ 1 b⁻¹ (a * b)⁻¹ k₃ hk₃
  have n2 := hb₂ b⁻¹ (a * b)⁻¹ k₂ hk₂
  rw [q1, modulus_mul'] at n3
  rw [q2, q3] at s3
  rw [q3] at n2
  have hRHS : ∀ x : Fˣ, ∀ δ : ℝ, 0 ≤ Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃}
      (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) x :=
    fun x δ => Set.indicator_nonneg (fun _ _ => by positivity) x
  simp only [gI, lI, e3, e2]
  set x := W (dg 1 b⁻¹ (a * b)⁻¹ * k₃) with hx
  set y := W' (dg2 b⁻¹ (a * b)⁻¹ * k₂) with hy
  by_cases hx0 : x = 0
  · rw [hx0]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hRHS _ _) (mul_nonneg (hRHS _ _) zero_le_one))
  obtain ⟨sb, sa⟩ := s3 hx0
  rw [Set.indicator_of_mem (show a ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} from sa),
    Set.indicator_of_mem (show b ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B₃} from sb), mul_one]
  set A : ℝ := (modulus (a : F) : ℝ) with hAd
  set B : ℝ := (modulus (b : F) : ℝ) with hBd
  have hE : Real.exp (σ * (Real.log A + 2 * Real.log B)) = A ^ σ * B ^ (2 * σ) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add]
    congr 1
    ring
  have hr1 : (-(3 / 2) : ℂ).re = -(3 / 2) := by norm_num
  have hr2 : (-1 : ℂ).re = -1 := by norm_num
  rw [norm_mul, norm_mul, norm_mul, norm_mp', norm_mp', hr1, hr2, hE, ← hAd, ← hBd]
  have m3 : ‖x‖ ≤ max C₃ 0 * (A * B) ^ (1 - ε) :=
    n3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have m2 : ‖y‖ ≤ max C₂ 0 * A ^ (1 / 2 - ε) :=
    n2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hm := mul_le_mul m3 m2 (norm_nonneg _) (by positivity)
  calc ‖x‖ * ‖y‖ * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) * (A ^ σ * B ^ (2 * σ))
      ≤ (max C₃ 0 * (A * B) ^ (1 - ε)) * (max C₂ 0 * A ^ (1 / 2 - ε)) * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) *
          (A ^ σ * B ^ (2 * σ)) := by gcongr
    _ = (max C₃ 0 * max C₂ 0) * ((A * B) ^ (1 - ε) * A ^ (1 / 2 - ε) * A ^ (-(3 / 2) : ℝ) * B ^ (-1 : ℝ) *
          (A ^ σ * B ^ (2 * σ))) := by ring
    _ = _ := by rw [exponents hA hB]

theorem integrable_gI (ψ : AddChar F Circle) {W : GL (Fin 3) F → ℂ} {W' : GL (Fin 2) F → ℂ}
    (h3 : TemperedBoundGL3 W) (h2 : TemperedBoundGL2 W') (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun p => ‖gI W W' p‖ * Real.exp (σ * lI p)) (GL2LocalData.mIw ψ) := by
  haveI hμ : (Ad3.LFS.hG ψ).IsHaarMeasure := by unfold Ad3.LFS.hG; infer_instance
  have hKc := GLnLocal.isCompact_integralGL F 2
  haveI : IsFiniteMeasure ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  set ε : ℝ := min (1 / 4) (σ / 4) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hε2 : ε ≤ σ / 4 := min_le_right _ _
  obtain ⟨C₃, B₃, hb₃⟩ := h3.2 ε hε0 hε1
  obtain ⟨C₂, B₂, hb₂⟩ := h2.2 ε hε0 hε1
  have hi₁ := GlobalTheory.T.integrable_modulus_pow_on_bounded_units F (σ - 2 * ε) B₃ (by linarith)
  have hi₂ := GlobalTheory.T.integrable_modulus_pow_on_bounded_units F (2 * σ - ε) B₃ (by linarith)
  have hi₃ : Integrable (fun _ : GL (Fin 2) F => (1 : ℝ)) ((Ad3.LFS.hG ψ).restrict (GL2LocalData.K2 F)) :=
    integrable_const _
  have hprod := (hi₁.mul_prod (hi₂.mul_prod hi₃)).const_mul (max C₃ 0 * max C₂ 0)
  have hmeas : AEStronglyMeasurable (fun p => ‖gI W W' p‖ * Real.exp (σ * lI p)) (GL2LocalData.mIw ψ) :=
    ((measurable_gI h3 h2).norm.mul
      (Real.measurable_exp.comp (measurable_lI.const_mul σ))).aestronglyMeasurable
  refine Integrable.mono' hprod hmeas ?_
  filter_upwards [ae_mem_maximal_compact ψ] with p hp
  rw [Real.norm_of_nonneg (by positivity)]
  exact bound_gI hb₃ (fun x y k hk => (hb₂ x y k hk).1) p hp

theorem iw_eq (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (u : ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) :
    GL2LocalData.iw (GL2LocalData.dW3 W) (GL2LocalData.dW2 W') u p = gI W W' p * Complex.exp (u * (lI p : ℂ)) := by
  simp only [GL2LocalData.iw, gI, lI, mp_eq_exp]
  push_cast
  have e : Complex.exp (((Real.log (modulus (p.1 : F) : ℝ) : ℝ) : ℂ) * (u - 3 / 2)) *
      Complex.exp (((Real.log (modulus (p.2.1 : F) : ℝ) : ℝ) : ℂ) * (2 * u - 1)) =
      Complex.exp (((Real.log (modulus (p.1 : F) : ℝ) : ℝ) : ℂ) * (-(3 / 2))) *
      Complex.exp (((Real.log (modulus (p.2.1 : F) : ℝ) : ℝ) : ℂ) * (-1)) *
      Complex.exp (u * (((Real.log (modulus (p.1 : F) : ℝ) : ℝ) : ℂ) +
        2 * ((Real.log (modulus (p.2.1 : F) : ℝ) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [mul_assoc _ (Complex.exp _) (Complex.exp _), e]
  ring

theorem holo : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), TemperedBoundGL3 W → TemperedBoundGL2 W' → DifferentiableOn ℂ (fun u => GL2LocalData.zetaGL3GL2 ψ (GL2LocalData.dW3 W) (GL2LocalData.dW2 W') u) {u : ℂ | 0 < u.re} := by
  intro F _ _ _ _ _ _ ψ W W' h3 h2
  have key := GlobalTheory.T.differentiableOn_laplace_integral_right_half (GL2LocalData.mIw ψ) (gI W W') lI (measurable_gI h3 h2).aestronglyMeasurable
    measurable_lI (integrable_gI ψ h3 h2)
  refine key.congr fun u _ => ?_
  simp only [GL2LocalData.zetaGL3GL2, iw_eq]

end GlobalTheory.CompanionTheory.DualHolo
