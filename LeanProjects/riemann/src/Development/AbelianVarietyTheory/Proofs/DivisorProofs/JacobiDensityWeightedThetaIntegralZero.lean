import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

noncomputable section

open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.MixDens
open GlobalTheory.FlagFibre (Low uni dens)
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.MixDens.Canon

variable {m : ℕ}

def blk (G : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) (j : Fin (m + 1)) : Matrix (Fin j) (Fin j) ℂ :=
  (chg (uni n) G).submatrix (Fin.castLE (Nat.le_of_lt_succ j.isLt)) (Fin.castLE (Nat.le_of_lt_succ j.isLt))

theorem blk_add_smul (G K : Matrix (Fin m) (Fin m) ℂ) (a b : ℂ) (n : Low m → ℂ) (j : Fin (m + 1)) :
    blk (a • G + b • K) n j = a • blk G n j + b • blk K n j := by
  ext x y
  simp [blk, chg, Matrix.mul_add, Matrix.add_mul]

theorem posDef_blk {G : Matrix (Fin m) (Fin m) ℂ} (h : G.PosDef) (n : Low m → ℂ) (j : Fin (m + 1)) :
    (blk G n j).PosDef :=
  (posDef_chg ((isUnit_iff_isUnit_det _).2 (by rw [FlagFibre.det_uni]; exact isUnit_one)) h).submatrix
    (Fin.castLE_injective _)

theorem posSemidef_blk {G : Matrix (Fin m) (Fin m) ℂ} (h : G.PosSemidef) (n : Low m → ℂ) (j : Fin (m + 1)) :
    (blk G n j).PosSemidef :=
  (h.mul_mul_conjTranspose_same (uni n)ᵀ).submatrix _

theorem continuous_blk (G : Matrix (Fin m) (Fin m) ℂ) (j : Fin (m + 1)) : Continuous fun n => blk G n j :=
  ((FlagFibre.continuous_uni.matrix_transpose.matrix_mul continuous_const).matrix_mul
    FlagFibre.continuous_uni.matrix_conjTranspose.matrix_transpose).matrix_submatrix _ _

theorem abel (a : ℝ) : ∀ (k : ℕ) (f : Fin (k + 1) → ℝ),
    ∑ i : Fin k, (a - 2 * (i : ℕ)) * (f i.castSucc - f i.succ) =
      -2 * ∑ i : Fin k, f i.castSucc + (a + 2) * f 0 - (a + 2 - 2 * k) * f (Fin.last k) := by
  intro k
  induction k with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    have := ih fun i => f i.castSucc
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Fin.succ_castSucc, Fin.castSucc_zero, Fin.succ_last] at this ⊢
    rw [this]
    push_cast
    ring

def logMinor (G : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) (j : Fin (m + 1)) : ℝ := Real.log (blk G n j).det.re

theorem jacDens_eq_exp {G : Matrix (Fin m) (Fin m) ℂ} (h : G.PosDef) (n : Low m → ℂ) :
    jacDens G n = Real.exp (∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) *
      (logMinor G n i.castSucc - logMinor G n i.succ)) := by
  have h0 : logMinor G n 0 = 0 := by
    have : IsEmpty (Fin ((0 : Fin (m + 1)) : ℕ)) := ⟨fun x => x.elim0⟩
    rw [logMinor, det_isEmpty]; simp
  have hl : (blk G n (Fin.last m)).det = G.det := by
    have : blk G n (Fin.last m) = chg (uni n) G := rfl
    rw [this]
    exact (det_chg _ _).trans (by simp [FlagFibre.det_uni])
  have hm (j : Fin (m + 1)) : ‖ReciprocityTheory.ChartRestriction.G.FD.lminor ((uni n)ᴴ * Gᵀ * uni n) j‖ = Real.exp (logMinor G n j) := by
    obtain ⟨h1, h2⟩ := FlagFibre.FlagInt.re_facts (posDef_blk h n j)
    have : ReciprocityTheory.ChartRestriction.G.FD.lminor ((uni n)ᴴ * Gᵀ * uni n) j = (blk G n j).det := by
      rw [ReciprocityTheory.ChartRestriction.G.FD.lminor, ← det_transpose, transpose_submatrix, blk, chg]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [this, logMinor, Real.exp_log h1]
    conv_lhs => rw [h2, Complex.norm_real, Real.norm_of_nonneg h1.le]
  have hd : G.det.re ^ (m - 1) = Real.exp (((m : ℝ) - 1) * logMinor G n (Fin.last m)) := by
    cases m with
    | zero => simp [h0]
    | succ m =>
      rw [logMinor, hl, Nat.add_sub_cancel]
      push_cast
      rw [add_sub_cancel_right, Real.exp_nat_mul, Real.exp_log (det_re_pos h)]
  rw [abel, h0, jacDens, dens, hd, Finset.mul_sum]
  simp only [hm]
  have e (x : ℝ) : Real.exp x ^ (-2 : ℤ) = Real.exp (-2 * x) := by
    rw [neg_mul, Real.exp_neg, _root_.zpow_neg, show (2 : ℝ) * x = (2 : ℕ) * x by norm_num, Real.exp_nat_mul]
    norm_cast
  simp only [e, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  ring

theorem hasDerivAt_logMinor (G K : Matrix (Fin m) (Fin m) ℂ) {t : ℝ} (h : (G + (t : ℂ) • K).PosDef)
    (n : Low m → ℂ) (j : Fin (m + 1)) :
    HasDerivAt (fun s : ℝ => logMinor (G + (s : ℂ) • K) n j) (logMinorDer (G + (t : ℂ) • K) K n j) t := by
  refine ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_log_det (fun s : ℝ => blk (G + (s : ℂ) • K) n j) (blk K n j) t (fun a b => ?_)
    (posDef_blk h n j)
  have e (s : ℝ) : blk (G + (s : ℂ) • K) n j a b = blk G n j a b + (s : ℂ) * blk K n j a b := by
    have := blk_add_smul G K 1 s n j
    rw [one_smul, one_smul] at this
    rw [this]; rfl
  simp only [e]
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (blk K n j a b)).const_add (blk G n j a b)

theorem abs_logMinorDer_le {H K : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} (hc : 0 ≤ c) (h : H.PosDef)
    (h₁ : ((c : ℂ) • H + (1 : ℂ) • K).PosSemidef) (h₂ : ((c : ℂ) • H + (-1 : ℂ) • K).PosSemidef)
    (n : Low m → ℂ) (j : Fin (m + 1)) : |logMinorDer H K n j| ≤ c * m := by
  have hb := posDef_blk h n j
  have e (s : ℝ) (hs : ((c : ℂ) • H + (s : ℂ) • K).PosSemidef) : 0 ≤ c * (j : ℕ) + s * logMinorDer H K n j := by
    have := re_trace_mul_nonneg_of_posSemidef hb.inv.posSemidef (posSemidef_blk hs n j)
    rw [blk_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      nonsing_inv_mul _ hb.det_pos.ne'.isUnit, trace_add, trace_smul, trace_smul, trace_one] at this
    simpa [logMinorDer, blk] using this
  have e₁ := e 1 (by simpa using h₁)
  have e₂ := e (-1) (by simpa using h₂)
  have hj : c * (j : ℕ) ≤ c * m := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt_succ j.isLt) hc
  rw [abs_le]
  constructor <;> linarith

theorem exists_sandwich {G K : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (hK : K.IsHermitian) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, |u| ≤ 2 → ((c : ℂ) • G + (u : ℂ) • K).PosSemidef := by
  have hb : (Kᴴ * K + 1).PosSemidef := (posSemidef_conjTranspose_mul_self K).add PosSemidef.one
  have h1 := le_re_trace_mul_smul_inv hG.inv hb
  have h0 := re_trace_mul_nonneg_of_posSemidef hG.inv.posSemidef hb
  rw [nonsing_inv_nonsing_inv _ hG.det_pos.ne'.isUnit, le_iff] at h1
  set c₀ := RCLike.re (G⁻¹ * (Kᴴ * K + 1)).trace
  refine ⟨c₀ + 1, by positivity, fun u hu => ?_⟩
  have h2 := posSemidef_conjTranspose_mul_self (K + (u / 2 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℂ))
  have h3 : ((1 - (u / 2) ^ 2 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℂ)).PosSemidef :=
    PosSemidef.one.smul (by nlinarith [abs_le.1 hu])
  refine Eq.subst (motive := PosSemidef) (Eq.symm ?_) (((h1.add h2).add h3).add hG.posSemidef)
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, hK.eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    star_trivial, Complex.coe_smul]
  module

theorem exists_bound {G K : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (hK : K.IsHermitian) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ t ∈ Metric.ball (0 : ℝ) ε, (G + (t : ℂ) • K).PosDef ∧
      ∀ n j, |logMinorDer (G + (t : ℂ) • K) K n j| ≤ C := by
  obtain ⟨c, hc, h⟩ := exists_sandwich hG hK
  refine ⟨c⁻¹, by positivity, c * m, fun t ht => ?_⟩
  have ht' : |c * t| ≤ 1 := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    rw [abs_mul, abs_of_pos hc]
    exact ((mul_le_mul_of_nonneg_left ht.le hc.le).trans_eq (mul_inv_cancel₀ hc.ne'))
  have hp : (G + (t : ℂ) • K).PosDef := by
    have h1 := (h (2 * (c * t)) (by rw [abs_mul]; norm_num; simpa using ht')).smul
      (show (0 : ℝ) ≤ (2 * c)⁻¹ by positivity)
    convert (hG.smul (show (0 : ℝ) < 1 / 2 by norm_num)).add_posSemidef h1 using 1
    simp only [Complex.coe_smul, smul_add, smul_smul]
    rw [show (2 * c)⁻¹ * c = 1 / 2 by field_simp, show (2 * c)⁻¹ * (2 * (c * t)) = t by field_simp]
    module
  have h' := abs_le.1 ht'
  refine ⟨hp, abs_logMinorDer_le hc.le hp ?_ ?_⟩
  · convert h (c * t + 1) (abs_le.2 ⟨by linarith, by linarith⟩) using 1
    push_cast
    module
  · convert h (c * t - 1) (abs_le.2 ⟨by linarith, by linarith⟩) using 1
    push_cast
    module

theorem measurable_logMinorDer (G K : Matrix (Fin m) (Fin m) ℂ) (j : Fin (m + 1)) :
    Measurable fun n => logMinorDer G K n j := by
  have e (n : Low m → ℂ) : logMinorDer G K n j =
      ((blk G n j).det⁻¹ * ((blk G n j).adjugate * blk K n j).trace).re := by
    change ((blk G n j)⁻¹ * blk K n j).trace.re = _
    rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, trace_smul, smul_eq_mul]
  simp only [e]
  exact Complex.measurable_re.comp ((continuous_blk G j).matrix_det.measurable.inv.mul
    ((continuous_blk G j).matrix_adjugate.matrix_mul (continuous_blk K j)).matrix_trace.measurable)

theorem measurable_jacDens (G : Matrix (Fin m) (Fin m) ℂ) : Measurable (jacDens G) :=
  (FlagFibre.measurable_dens _).mul_const _

theorem integrable_jacDens {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) : Integrable (jacDens G) := by
  refine Integrable.mul_const ⟨(FlagFibre.measurable_dens _).aestronglyMeasurable, ?_⟩ _
  rw [hasFiniteIntegral_iff_ofReal (.of_forall (FlagFibre.dens_nonneg _)),
    FlagFibre.FlagInt.lintegral_dens m Gᵀ hG.transpose]
  exact ENNReal.ofReal_lt_top

theorem integral_jacDens_eq {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) :
    ∫ n, jacDens G n = 1 / GlobalTheory.TrueCx.flagConst m := by
  have h₁ := GlobalTheory.FlagFibre.FlagInt.lintegral_dens m Gᵀ hG.transpose
  have hd := det_re_pos hG
  have hp := GlobalTheory.TrueCx.flagConst_pos m
  simp only [jacDens]
  rw [integral_mul_const, integral_eq_lintegral_of_nonneg_ae (.of_forall (FlagFibre.dens_nonneg _))
    (FlagFibre.measurable_dens _).aestronglyMeasurable, h₁, det_transpose,
    ENNReal.toReal_ofReal (by positivity)]
  have e : G.det.re ^ (1 - (m : ℤ)) * G.det.re ^ (m - 1) = 1 := by
    cases m with
    | zero => simp
    | succ m =>
      rw [Nat.add_sub_cancel, ← zpow_natCast, ← zpow_add₀ hd.ne']
      simp
  rw [div_mul_eq_mul_div, e]

theorem integral_jacDens_mul_theta : ∀ (m : ℕ) (G K : Matrix (Fin m) (Fin m) ℂ), G.PosDef → K.IsHermitian →
    ∫ n : Low m → ℂ, jacDens G n * ∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) * theta G K n i = 0 := by
  intro m G K hG hK
  obtain ⟨ε, hε, C, h⟩ := exists_bound hG hK
  let L (t : ℝ) (n : Low m → ℂ) : ℝ := ∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) *
      (logMinor (G + (t : ℂ) • K) n i.castSucc - logMinor (G + (t : ℂ) • K) n i.succ)
  let S (t : ℝ) (n : Low m → ℂ) : ℝ := ∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) * theta (G + (t : ℂ) • K) K n i
  let B : ℝ := ∑ i : Fin m, |(m : ℝ) - 1 - 2 * (i : ℕ)| * (C + C)
  have hL (n) (t) (ht : t ∈ Metric.ball (0 : ℝ) ε) : HasDerivAt (L · n) (S t n) t :=
    HasDerivAt.fun_sum fun i _ => ((hasDerivAt_logMinor G K (h t ht).1 n _).sub
      (hasDerivAt_logMinor G K (h t ht).1 n _)).const_mul _
  have hS (n) (t) (ht : t ∈ Metric.ball (0 : ℝ) ε) : ‖S t n‖ ≤ B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ((h t ht).2 n _) ((h t ht).2 n _)))
      (abs_nonneg _)
  have h0 := Metric.mem_ball_self (x := (0 : ℝ)) hε
  have hB : 0 ≤ B := (norm_nonneg _).trans (hS 0 0 h0)
  have hJ (n) (t) (ht : t ∈ Metric.ball (0 : ℝ) ε) : jacDens (G + (t : ℂ) • K) n = Real.exp (L t n) :=
    jacDens_eq_exp (h t ht).1 n
  have hG0 : G + ((0 : ℝ) : ℂ) • K = G := by simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Low m → ℂ)))
    (F := fun (t : ℝ) n => jacDens (G + (t : ℂ) • K) n)
    (F' := fun (t : ℝ) n => jacDens (G + (t : ℂ) • K) n * S t n)
    (bound := fun n => jacDens G n * (Real.exp (B * ε) * B)) (Metric.ball_mem_nhds (0 : ℝ) hε)
    (.of_forall fun t => (measurable_jacDens _).aestronglyMeasurable) (integrable_jacDens (h 0 h0).1)
    ((measurable_jacDens _).mul (Finset.measurable_sum _ fun i _ =>
      ((measurable_logMinorDer _ _ _).sub (measurable_logMinorDer _ _ _)).const_mul _)).aestronglyMeasurable
    (.of_forall fun n t ht => by
      have h1 := (convex_ball (0 : ℝ) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx => (hL n x hx).hasDerivWithinAt) (hS n) h0 ht
      have h2 : L t n ≤ L 0 n + B * ε := by
        have h3 : ‖t - 0‖ ≤ ε := (mem_ball_iff_norm.1 ht).le
        have := (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left h3 hB))
        linarith
      have h4 := hJ n 0 h0
      rw [hG0] at h4
      rw [h4, hJ n t ht, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
      exact mul_le_mul (Real.exp_le_exp.2 h2) (hS n t ht) (norm_nonneg _) (Real.exp_pos _).le)
    ((integrable_jacDens hG).mul_const _)
    (.of_forall fun n t ht => by
      rw [hJ n t ht]
      refine (hL n t ht).exp.congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using hJ n s hs)
  have hc : HasDerivAt (fun t : ℝ => ∫ n, jacDens (G + (t : ℂ) • K) n) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (1 / GlobalTheory.TrueCx.flagConst m)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs using integral_jacDens_eq (h s hs).1
  have := key.2.unique hc
  simpa only [S, hG0] using this

end GlobalTheory.MixDens.Canon
