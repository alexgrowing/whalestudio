import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpNorm

theorem norm_le_sum_inner {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ W) (u : W) : ‖u‖ ≤ ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
  calc ‖u‖ = ‖∑ i, ⟪b i, u⟫_ℂ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i, u⟫_ℂ • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, b.orthonormal.1 i, mul_one]

theorem rankOne_integral {X : Type} [MeasurableSpace X] (ν : Measure X)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (f : X → Wp) (g : X → Wq) (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) :
    Integrable (fun x => (innerSL ℂ (g x)).smulRight (f x)) ν ∧
      ‖∫ x, (innerSL ℂ (g x)).smulRight (f x) ∂ν‖ ≤ K := by
  haveI := FiniteDimensional.complete ℂ Wp
  set T : X → (Wq →L[ℂ] Wp) := fun x => (innerSL ℂ (g x)).smulRight (f x) with hT
  set e := stdOrthonormalBasis ℂ Wp
  set b := stdOrthonormalBasis ℂ Wq
  have hcont : Continuous (Function.uncurry fun (a : Wq) (c : Wp) => (innerSL ℂ a).smulRight c) := by
    fun_prop
  have hmeas : AEStronglyMeasurable T ν := hcont.comp_aestronglyMeasurable₂ hg hf
  have hbd : ∀ x, ‖f x‖ * ‖g x‖ ≤ ∑ j, ∑ i, ‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖ := fun x => by
    rw [← Finset.sum_mul_sum]
    exact mul_le_mul (norm_le_sum_inner e _) (norm_le_sum_inner b _) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hnormT : ∀ x, ‖T x‖ = ‖g x‖ * ‖f x‖ := fun x => by
    simp only [hT, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hterm : ∀ j i, AEMeasurable
      (fun x => ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := fun j i =>
    ((aestronglyMeasurable_const.inner hf).norm.mul
      (aestronglyMeasurable_const.inner hg).norm).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν) < ⊤ := by
    calc (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν)
        ≤ ∫⁻ x, ∑ j, ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [hnormT, mul_comm]
          refine (ENNReal.ofReal_le_ofReal (hbd x)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity]
          exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
      _ = ∑ j, ∑ i, ∫⁻ x, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          have hsum : ∀ j, AEMeasurable
              (fun x => ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := by
            intro j
            first
              | exact Finset.aemeasurable_fun_sum _ fun i _ => hterm j i
              | exact Finset.aemeasurable_sum' _ fun i _ => hterm j i
              | exact (Finset.aemeasurable_sum _ fun i _ => hterm j i).congr
                  (Filter.Eventually.of_forall fun x => by simp [Finset.sum_apply])
          rw [lintegral_finset_sum' _ fun j _ => hsum j]
          exact Finset.sum_congr rfl fun j _ => lintegral_finset_sum' _ fun i _ => hterm j i
      _ ≤ ∑ j, ∑ i, ENNReal.ofReal K :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            h (e j) (b i) (e.orthonormal.1 j) (b.orthonormal.1 i)
      _ < ⊤ := by simp [ENNReal.mul_lt_top]
  have hi : Integrable T ν := ⟨hmeas, hasFiniteIntegral_iff_norm _ |>.2 hfin⟩
  refine ⟨hi, ?_⟩
  have key : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪v, (∫ x, T x ∂ν) w⟫_ℂ‖ ≤ K := by
    intro v w hv hw
    rw [ContinuousLinearMap.integral_apply hi w, ← integral_inner (hi.apply_continuousLinearMap w) v]
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hK ?_)
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (h v w hv hw)
    show ENNReal.ofReal ‖⟪v, ⟪g x, w⟫_ℂ • f x⟫_ℂ‖ = ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖)
    rw [inner_smul_right, norm_mul, norm_inner_symm, mul_comm]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hK fun w hw => ?_
  set y := (∫ x, T x ∂ν) w
  by_cases hy : y = 0
  · rw [hy, norm_zero]; exact hK
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hv : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy'), inv_mul_cancel₀ hy'.ne']
  have hk := key _ w hv hw
  rw [inner_smul_left, norm_mul, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hy'), inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hk
  calc ‖y‖ = ‖y‖⁻¹ * ‖y‖ ^ 2 := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hy'.ne', one_mul]
    _ ≤ K := hk

private theorem mul_mem_dualWeyl_complex {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) :
    a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem measurableSet_of_isOpen' (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hc : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} :=
    isClosed_eq ((hof.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hof) continuous_const
  exact hc.measurableSet

theorem integrable_and_norm_ampJ_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  intro k r Wp _ _ _ Wq _ _ _ ν Φ Φ' γ c K hγ hν hΦ hΦ' hc hK h
  haveI := FiniteDimensional.complete ℂ Wp
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hS := measurableSet_of_isOpen' k r
  have hae : ν.restrict {x : Mt k r | Matrix.of x ∈ GG k r} = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hν)
  have hf : AEStronglyMeasurable (fun x : Mt k r => Φ (γ * Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ.comp (continuous_const.mul hof).continuousOn fun x hx => mul_mem_dualWeyl_complex hγ hx).aestronglyMeasurable hS
  have hg : AEStronglyMeasurable (fun x : Mt k r => Φ' (Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ'.comp hof.continuousOn fun x hx => hx).aestronglyMeasurable hS
  obtain ⟨hi, hn⟩ := rankOne_integral ν _ _ hf hg K hK h
  refine ⟨hi, ?_⟩
  simp only [ampJ, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hc.le)

end GlobalTheory.Amp.OpNorm
