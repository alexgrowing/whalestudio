import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourierStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionCompactSupportModuloUnipotentStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Dens

def qMap {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x : InfinitePlace F → ι → ℝ) : InfinitePlace F → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))

def gW {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))

section
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_qMap (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Continuous (qMap B ρ) := by
  refine continuous_pi fun w => ?_
  exact continuous_const.mul (Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w)))

theorem continuous_gW (P : InfinitePlace F → Matrix ι ι ℝ) : Continuous (gW P) := by
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))
  exact Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w))

theorem gauss_I (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun _ => Complex.I) x = (gW P x : ℂ) := by
  simp only [gauss, gW, Complex.I_re, Complex.I_im]
  push_cast
  congr 1
  simp [Finset.mul_sum]

theorem gauss_shift (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (t : InfinitePlace F → ℝ) (v : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v =
      (gW P v : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w, qMap B ρ v w * t w : ℝ) : ℂ)) := by
  simp only [gauss, gW, qMap]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, add_zero, zero_add, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring

theorem one_dim_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun t : ℝ => (‖(t : ℂ) + Complex.I‖ ^ M)⁻¹) := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  have h2 : ‖(t : ℂ) + Complex.I‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h1 : 1 ≤ ‖(t : ℂ) + Complex.I‖ := by
    have : (1 : ℝ) ^ 2 ≤ ‖(t : ℂ) + Complex.I‖ ^ 2 := by rw [h2]; nlinarith [sq_nonneg t]
    exact (pow_le_pow_iff_left₀ zero_le_one (norm_nonneg _) two_ne_zero).1 this
  rw [Real.norm_of_nonneg (by positivity), ← h2]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))

theorem prod_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun x : InfinitePlace F → ℝ => (∏ w, ‖(x w : ℂ) + Complex.I‖ ^ M)⁻¹) := by
  have := Integrable.fintype_prod (μ := fun _ => (volume : Measure ℝ))
    (f := fun (_ : InfinitePlace F) (t : ℝ) => (‖(t : ℂ) + Complex.I‖ ^ M)⁻¹)
    (fun _ => one_dim_integrable M hM)
  simpa [Finset.prod_inv_distrib, volume_pi] using this

theorem density_of_q : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∃ Di : (InfinitePlace F → ℝ) → ℝ, Continuous Di ∧ (∀ y, 0 ≤ Di y) ∧ (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Di y)) ∧ Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) ∧ ∀ z : InfinitePlace F → ℝ, ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) = ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di z : ℝ) : ℂ) := by
  intro F _ _ ι _ _ M B ρ P h hM
  classical
  have hdet : B.det ≠ 0 := h.2.2.2.1
  set S : ℝ := Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| with hS
  have hSpos : 0 < S := by
    refine Real.sqrt_pos.2 (abs_pos.2 ?_)
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hdet)
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'

  have hgi : Integrable (gW P) := by
    have h0 := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P h (fun _ => Complex.I) (fun _ => by simp)).1
    have h1 := h0.re
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [gauss_I]
  have hgn : ∀ x, 0 ≤ gW P x := fun x => (Real.exp_pos _).le
  have hdm : Measurable fun x => ENNReal.ofReal (gW P x) :=
    ENNReal.measurable_ofReal.comp (continuous_gW P).measurable
  let ν : Measure (InfinitePlace F → ι → ℝ) := volume.withDensity fun x => ENNReal.ofReal (gW P x)
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hgi.2
  have hQ : Continuous (qMap B ρ) := continuous_qMap B ρ
  let m : Measure (InfinitePlace F → ℝ) := ν.map (qMap B ρ)
  haveI : IsFiniteMeasure m := Measure.isFiniteMeasure_map ν _

  have hχ : ∀ t : InfinitePlace F → ℝ,
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m =
        ∫ v, gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v := by
    intro t
    have hc : Continuous fun z : InfinitePlace F → ℝ =>
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) := by fun_prop
    rw [integral_map hQ.aemeasurable hc.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hdm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [ENNReal.toReal_ofReal (hgn v), Complex.real_smul]
    exact (gauss_shift B ρ P t v).symm
  have hcG : ∀ t : InfinitePlace F → ℝ, cG B ρ P (fun w => (t w : ℂ) + Complex.I) =
      (S : ℂ) * ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    intro t
    rw [hχ t]
    rfl

  have hcont : Continuous fun t : InfinitePlace F → ℝ =>
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    refine continuous_of_dominated (bound := fun _ => 1) (fun t => ?_) (fun t => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun z => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Filter.Eventually.of_forall fun z => ?_
      have : (2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ) =
          ((2 * Real.pi * ∑ w, z w * t w : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcGi : Integrable fun t : InfinitePlace F → ℝ =>
      cG B ρ P (fun w => (t w : ℂ) + Complex.I) := by
    have hcc : Continuous fun t : InfinitePlace F → ℝ =>
        cG B ρ P (fun w => (t w : ℂ) + Complex.I) := by
      simp only [hcG]
      exact continuous_const.mul hcont
    refine (prod_integrable (F := F) M hM).mono' hcc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have him : ∀ w, 0 < ((t w : ℂ) + Complex.I).im := fun w => by simp
    exact ((GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P h _ him).2.1).le
  have hχi : Integrable fun t : InfinitePlace F → ℝ =>
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    refine (hcGi.const_mul ((S : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hcG]
    rw [inv_mul_cancel_left₀ hSc]
  obtain ⟨D, hDc, hD0, hDf, hDm⟩ := GlobalTheory.T.schur_function_compact_support_modulo_unipotent (InfinitePlace F) m inferInstance hχi
  refine ⟨D, hDc, hD0, fun U hU => ?_, hcGi, fun z => ?_⟩
  · rw [← hDm U hU, Measure.map_apply hQ.measurable hU, withDensity_apply _ (hQ.measurable hU)]
    rfl
  · have hmul : ∀ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) =
        (S : ℂ) * ((∫ u, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ w, u w * x w : ℝ) : ℂ)) ∂m) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ))) := by
      intro x
      rw [hcG x, mul_assoc]
    simp only [hmul]
    rw [integral_const_mul, ← hDf z, Complex.ofReal_mul]

end

end GlobalTheory.CompanionTheory.SW.Core.Dens
