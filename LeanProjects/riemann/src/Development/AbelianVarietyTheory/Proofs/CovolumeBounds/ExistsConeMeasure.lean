import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralGaussianHyperboloidFiberStatement
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.ConeZero

def param (n : ℕ) (p : (Fin n → ℂ) × ℝ) : Fin (n + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) p.1
    (((Real.sqrt (sqLen p.1 + 0) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))

def coneMeasure (n : ℕ) : Measure (Fin (n + 1) → ℂ) :=
  Measure.map (param n) (volume.restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi)))

theorem continuous_sqLen (n : ℕ) : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

theorem sqLen_nonneg {n : ℕ} (w : Fin n → ℂ) : 0 ≤ sqLen w :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem continuous_param (n : ℕ) : Continuous (param n) := by
  have h := continuous_sqLen n
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [param, Fin.snoc_last]
    fun_prop
  · simp only [param, Fin.snoc_castSucc]
    fun_prop

theorem normSq_param_last (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    Complex.normSq (param n p (Fin.last n)) = sqLen p.1 := by
  simp only [param, Fin.snoc_last, map_mul, add_zero, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (sqLen_nonneg _), Complex.normSq_eq_norm_sq, mul_comm Complex.I,
    Complex.norm_exp_ofReal_mul_I]
  ring

theorem sqLen_param (n : ℕ) (p : (Fin n → ℂ) × ℝ) : sqLen (param n p) = 2 * sqLen p.1 := by
  rw [sqLen, Fin.sum_univ_castSucc, normSq_param_last]
  simp only [param, Fin.snoc_castSucc]
  rw [sqLen]; ring

theorem herm_param (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1))
      (param n p) (param n p) = 0 := by
  have h := normSq_param_last n p
  rw [herm, dotProduct, Fin.sum_univ_castSucc]
  simp only [mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, one_mul, Pi.star_apply,
    RCLike.star_def, neg_mul, mul_neg, ← Complex.normSq_eq_conj_mul_self, h]
  simp only [param, Fin.snoc_castSucc, sqLen]
  push_cast
  ring

theorem lintegral_cone (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v, F (sqLen v) ∂coneMeasure n
      = (∫⁻ w : Fin n → ℂ, F (2 * sqLen w)) * ENNReal.ofReal (2 * Real.pi) := by
  have hm : Measurable fun w : Fin n → ℂ => F (2 * sqLen w) :=
    hF.comp ((continuous_sqLen n).measurable.const_mul 2)
  rw [coneMeasure, lintegral_map (f := fun v => F (sqLen v)) (hF.comp (continuous_sqLen _).measurable)
    (continuous_param n).measurable]
  simp only [sqLen_param]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun p : (Fin n → ℂ) × ℝ => F (2 * sqLen p.1)) (hm.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
    Real.volume_Ioc, sub_zero]
  rw [lintegral_mul_const _ hm]

theorem lintegral_scale (n : ℕ) (s : ℝ) (hs : 0 < s) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : Fin n → ℂ, F (s * sqLen w)
      = ENNReal.ofReal (s ^ (-(n : ℝ))) * ∫⁻ w : Fin n → ℂ, F (sqLen w) := by
  have hm : Measurable fun w : Fin n → ℂ => F (sqLen w) := hF.comp (continuous_sqLen n).measurable
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h1 : ∀ w : Fin n → ℂ, s * sqLen w = sqLen (Real.sqrt s • w) := by
    intro w
    simp only [sqLen, Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt hs.le]
  simp only [h1]
  rw [← lintegral_map hm (measurable_const_smul (Real.sqrt s)),
    Measure.map_addHaar_smul volume hr, lintegral_smul_measure, smul_eq_mul]
  congr 2
  have hd : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hs.le, Real.rpow_neg hs.le, Real.rpow_natCast,
    abs_of_nonneg (by positivity)]

theorem gauss_ne_top (n : ℕ) :
    ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (Real.exp (-(2 * sqLen w))) ≠ ∞ := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-(2 * Complex.normSq z))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 2)
      (by norm_num) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [zero_mul, add_zero, Complex.norm_exp, Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.ofReal_pow]
    simp [-Complex.ofReal_pow]
  have h2 : Integrable (fun w : Fin n → ℂ => ∏ i, Real.exp (-(2 * Complex.normSq (w i)))) :=
    Integrable.fintype_prod (f := fun _ z => Real.exp (-(2 * Complex.normSq z))) fun _ => h1
  have h3 : Integrable (fun w : Fin n → ℂ => Real.exp (-(2 * sqLen w))) := by
    refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  exact h3.lintegral_lt_top.ne

theorem gauss_ne_zero (n : ℕ) :
    ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (Real.exp (-(2 * sqLen w))) ≠ 0 := by
  have hm : Measurable fun w : Fin n → ℂ => ENNReal.ofReal (Real.exp (-(2 * sqLen w))) := by
    have := (continuous_sqLen n).measurable
    fun_prop
  refine ((lintegral_pos_iff_support hm).2 ?_).ne'
  have : (Function.support fun w : Fin n → ℂ => ENNReal.ofReal (Real.exp (-(2 * sqLen w))))
      = Set.univ := by
    ext w
    simp [Real.exp_pos]
  rw [this]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

theorem ae_cone (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ v ∂coneMeasure n, v ≠ 0 ∧
      herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1)) v v = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [coneMeasure, ae_map_iff (continuous_param n).measurable.aemeasurable]
  · refine ae_restrict_of_ae ?_
    have h0 : ∀ᵐ p : (Fin n → ℂ) × ℝ, p.1 ≠ 0 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : Fin n → ℂ))
    filter_upwards [h0] with p hp
    refine ⟨fun h => hp ?_, herm_param n p⟩
    funext j
    have := congrFun h j.castSucc
    simpa [param] using this
  · refine MeasurableSet.inter (measurableSet_singleton (0 : Fin (n + 1) → ℂ)).compl ?_
    refine (isClosed_eq ?_ continuous_const).measurableSet
    unfold herm
    fun_prop

theorem Hpk_zero (k : ℕ) : Hpk k 0 = Matrix.diagonal
    (fun i : Fin (2 * 0 + k + 1) => if i = Fin.last (2 * 0 + k) then (-1 : ℂ) else 1) := by
  ext i j
  have hi := i.isLt
  by_cases h : i = j
  · subst h
    simp only [Hpk, diagonal_apply_eq, Fin.ext_iff, Fin.val_last]
    have : i.val ≤ 0 + k := by omega
    simp [show i.val ≤ k by omega]
  · simp [Hpk, h]

theorem exists_coneMeasure : ∀ k : ℕ, 1 ≤ k → ∃ m : Measure (Fin (2 * 0 + k + 1) → ℂ), SFinite m ∧ (∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k 0) v v = 0) ∧ (∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f → (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ (-((2 * 0 + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂m) ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0 ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞ ∧ ∀ g ∈ GV k 0, (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) = ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m := by
  intro k hk
  have hG : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t)) := by fun_prop
  have hpi : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simpa using Real.pi_pos
  refine ⟨coneMeasure (2 * 0 + k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold coneMeasure; infer_instance
  · rw [Hpk_zero]; exact ae_cone _ (by omega)
  · intro s hs f hf
    rw [lintegral_cone _ (fun t => f (s * t)) (hf.comp (measurable_const_mul s)),
      lintegral_cone _ f hf, ← mul_assoc,
      ← lintegral_scale _ s hs (fun t => f (2 * t)) (hf.comp (measurable_const_mul 2))]
    simp only [mul_left_comm s 2]
  · rw [lintegral_cone _ _ hG]
    exact mul_ne_zero (gauss_ne_zero _) hpi
  · rw [lintegral_cone _ _ hG]
    exact ENNReal.mul_ne_top (gauss_ne_top _) ENNReal.ofReal_ne_top
  · intro g hg
    have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
    rw [Hpk_zero] at hg'
    have h := GlobalTheory.T.lintegral_gaussian_hyperboloid_fiber (2 * 0 + k) g hg' 0 le_rfl
    have hs := (continuous_sqLen (2 * 0 + k + 1)).measurable
    have hm : Measurable fun v : Fin (2 * 0 + k + 1) → ℂ => g *ᵥ v :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    rw [coneMeasure, lintegral_map (f := fun v => ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v)))) (hG.comp (hs.comp hm)) (continuous_param _).measurable,
      lintegral_map (f := fun v => ENNReal.ofReal (Real.exp (-sqLen v))) (hG.comp hs) (continuous_param _).measurable]
    exact h

end GlobalTheory.HCXi.ConeZero
