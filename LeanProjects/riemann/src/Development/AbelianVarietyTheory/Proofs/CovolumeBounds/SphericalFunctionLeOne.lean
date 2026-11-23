import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuous
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.BlockEmbConjTranspose
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsCompactHaarMeasure
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitiveOfGram
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.HalfVolumeLeviRecursionStatement
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.LeOne

lemma gv_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma meas_v {k r : ℕ} (hk : 1 ≤ k) {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {f : α → Mat k r} (hf : Continuous f) :
    Measurable fun t => ENNReal.ofReal (vHalf k r (f t)) ^ 2 := by
  have hm := (GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn k r hk).2.2.1
  have hf' : Continuous (Y := Mt k r) fun t => Matrix.of.symm (f t) := hf
  exact (ENNReal.measurable_ofReal.comp (hm.comp hf'.measurable)).pow_const 2

lemma cont_of {k r : ℕ} : Continuous fun κ : Mt k r => (Matrix.of κ : Mat k r) := continuous_id

lemma cont_lev (k i r' : ℕ) : Continuous (ιLev k i r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  unfold ιLev
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  all_goals exact continuous_const

lemma sqLen_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ sqLen v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma diag_re {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (a : Fin m) :
    ((Aᴴ * A) a a).re = sqLen fun i => A i a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sqLen, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma col_facts (k r : ℕ) (hk : 1 ≤ k) (a : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r (isoVec k r) a) (fvec k r (isoVec k r) a) = 0 ∧
      sqLen (fvec k r (isoVec k r) a) = 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic k r hk
  constructor
  · have := congrFun (congrFun h2 a) a
    rw [Matrix.mul_assoc] at this
    exact this
  · have := diag_re (frame k r) a
    rw [h1] at this
    rw [Matrix.one_apply_eq, Complex.one_re] at this
    exact this.symm

lemma sq_rpow {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    ENNReal.ofReal (s ^ (-((m : ℝ) / 2))) ^ 2 = ENNReal.ofReal (s ^ (-(m : ℝ))) := by
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hs _), ← Real.rpow_natCast, ← Real.rpow_mul hs]
  congr 2
  push_cast
  ring

lemma vHalf_zero (k : ℕ) (x : Mat k 0) :
    vHalf k 0 x = sqLen (x *ᵥ isoVec k 0) ^ (-((k : ℝ) / 2)) := by
  have : gram k 0 x (Fin.last 0) = sqLen (x *ᵥ isoVec k 0) := by
    unfold GlobalTheory.HCXi.gram
    rw [show ∀ M : Matrix (Fin ((Fin.last 0 : ℕ) + 1)) (Fin ((Fin.last 0 : ℕ) + 1)) ℂ, M.det = M 0 0 from
      fun M => Matrix.det_fin_one M, Matrix.submatrix_apply, diag_re]
    rfl
  unfold vHalf
  rw [this]
  simp

lemma base (k : ℕ) (μK : Measure (Mt k 0)) (hk : 1 ≤ k) (hμ : IsKMeas k 0 μK) (g : Mat k 0) (hg : g ∈ GV k 0) :
    (∫⁻ κ : Mt k 0, ENNReal.ofReal (vHalf k 0 (g * Matrix.of κ)) ^ 2 ∂μK) = 1 := by
  obtain ⟨h1, h2⟩ := col_facts k 0 hk (Fin.last 0)
  have h := GlobalTheory.HCXi.Poisson.poisson_integral k 0 μK (isoVec k 0) hk hμ h1 h2 g hg
  rw [← h]
  refine lintegral_congr fun κ => ?_
  rw [vHalf_zero, sq_rpow (sqLen_nonneg _)]
  simp

lemma step (k r' : ℕ) (hk : 1 ≤ k)
    (ih : ∀ μ : Measure (Mt k r'), IsKMeas k r' μ → ∀ g ∈ GV k r',
      (∫⁻ κ : Mt k r', ENNReal.ofReal (vHalf k r' (g * Matrix.of κ)) ^ 2 ∂μ) = 1)
    (μK : Measure (Mt k (1 + r'))) (hμ : IsKMeas k (1 + r') μK) (g : Mat k (1 + r')) (hg : g ∈ GV k (1 + r')) :
    (∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 ∂μK) = 1 := by
  obtain ⟨μ₁, hμ₁⟩ := GlobalTheory.HCXi.exists_isKMeas k r'
  have : IsProbabilityMeasure μK := ⟨hμ.2⟩
  have : IsProbabilityMeasure μ₁ := ⟨hμ₁.2⟩
  have hae : ∀ᵐ κ ∂μK, (Matrix.of κ : Mat k (1 + r')) ∈ Kset k (1 + r') := hμ.1.conc
  have hae₁ : ∀ᵐ y ∂μ₁, (Matrix.of y : Mat k r') ∈ Kset k r' := hμ₁.1.conc
  have hm : Measurable fun κ : Mt k (1 + r') => ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 :=
    meas_v hk (continuous_const.matrix_mul cont_of)
  have hm2 : Measurable fun q : Mt k r' × Mt k (1 + r') =>
      ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of q.2 * ιLev k 1 r' (Matrix.of q.1))) ^ 2 :=
    meas_v hk ((continuous_const.matrix_mul (cont_of.comp continuous_snd)).matrix_mul
      ((cont_lev k 1 r').comp (cont_of.comp continuous_fst)))
  have hsw := lintegral_lintegral_swap (μ := μ₁) (ν := μK)
    (f := fun (y : Mt k r') (κ : Mt k (1 + r')) =>
      ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ * ιLev k 1 r' (Matrix.of y))) ^ 2) hm2.aemeasurable
  have he : fvec k (1 + r') (isoVec k (1 + r')) ⟨0, Nat.succ_pos _⟩ = e0 k r' := by
    unfold fvec
    rw [dif_pos (show (0 : ℕ) < 1 + r' by omega)]
    rfl
  obtain ⟨h1, h2⟩ := col_facts k (1 + r') hk ⟨0, Nat.succ_pos _⟩
  rw [he] at h1 h2
  calc (∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 ∂μK)
      = ∫⁻ _y : Mt k r', (∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 ∂μK) ∂μ₁ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ y : Mt k r', ∫⁻ κ : Mt k (1 + r'),
          ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ * ιLev k 1 r' (Matrix.of y))) ^ 2 ∂μK ∂μ₁ := by
        refine lintegral_congr_ae (hae₁.mono fun y hy => ?_)
        have hrm : Measurable (rmulF (ιLev k 1 r' (Matrix.of y)) : Mt k (1 + r') → Mt k (1 + r')) :=
          Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
        dsimp only
        conv_lhs => rw [← hμ.1.right _ (GlobalTheory.HCXi.blockEmb_mem_Kset k r' _ hy)]
        rw [lintegral_map hm hrm]
        simp only [Matrix.mul_assoc]
        rfl
    _ = ∫⁻ κ : Mt k (1 + r'), ∫⁻ y : Mt k r',
          ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ * ιLev k 1 r' (Matrix.of y))) ^ 2 ∂μ₁ ∂μK := hsw
    _ = ∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ e0 k r') ^
          (-((2 * (1 + r') + k : ℕ) : ℝ))) ∂μK := by
        refine lintegral_congr_ae (hae.mono fun κ hκ => ?_)
        obtain ⟨g₁, hg₁, hv⟩ := GlobalTheory.T.half_volume_levi_recursion k r' hk _ (gv_mul hg hκ.1)
        have hm3 : Measurable fun y : Mt k r' => ENNReal.ofReal (vHalf k r' (g₁ * Matrix.of y)) ^ 2 :=
          meas_v hk (continuous_const.matrix_mul cont_of)
        dsimp only
        rw [← sq_rpow (sqLen_nonneg _), ← mul_one (ENNReal.ofReal _ ^ 2), ← ih μ₁ hμ₁ g₁ hg₁,
          ← lintegral_const_mul _ hm3]
        refine lintegral_congr_ae (hae₁.mono fun y hy => ?_)
        dsimp only
        rw [hv _ hy.1, ENNReal.ofReal_mul (Real.rpow_nonneg (sqLen_nonneg _) _), mul_pow]
    _ = 1 := GlobalTheory.HCXi.Poisson.poisson_integral k (1 + r') μK (e0 k r') hk hμ h1 h2 g hg

theorem lintegral_vHalf_sq : ∀ (k r : ℕ) (μK : Measure (Mt k r)), 1 ≤ k → IsKMeas k r μK → ∀ g ∈ GV k r,
    (∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (g * Matrix.of κ)) ^ 2 ∂μK) = 1 := by
  intro k r μK hk
  induction r with
  | zero => exact base k μK hk
  | succ r ih =>
    have key : ∀ s : ℕ, s = 1 + r → ∀ μ : Measure (Mt k s), IsKMeas k s μ → ∀ g ∈ GV k s,
        (∫⁻ κ : Mt k s, ENNReal.ofReal (vHalf k s (g * Matrix.of κ)) ^ 2 ∂μ) = 1 := by
      rintro s rfl
      exact step k r hk ih
    exact key _ (Nat.add_comm _ _) μK

end GlobalTheory.HCXi.LeOne

namespace GlobalTheory.HCXi

theorem two_mul_le_one_add_sq_ennreal (a : ℝ≥0∞) : 2 * a ≤ 1 + a ^ 2 := by
  induction a using ENNReal.recTopCoe with
  | top => simp
  | coe x =>
    have h : 2 * x ≤ 1 + x ^ 2 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      nlinarith [sq_nonneg ((x : ℝ) - 1)]
    exact_mod_cast h

theorem lintegral_le_one_of_lintegral_sq_eq_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hμ : μ Set.univ = 1) (f : X → ℝ≥0∞) (hf : ∫⁻ x, f x ^ 2 ∂μ = 1) : ∫⁻ x, f x ∂μ ≤ 1 := by
  have h : 2 * ∫⁻ x, f x ∂μ ≤ 2 * 1 := by
    calc 2 * ∫⁻ x, f x ∂μ = ∫⁻ x, 2 * f x ∂μ := (lintegral_const_mul' 2 f (by simp)).symm
      _ ≤ ∫⁻ x, (1 + f x ^ 2) ∂μ := lintegral_mono fun x => two_mul_le_one_add_sq_ennreal (f x)
      _ = ∫⁻ _, 1 ∂μ + ∫⁻ x, f x ^ 2 ∂μ := lintegral_add_left measurable_const _
      _ = 2 * 1 := by rw [hf, lintegral_const, hμ]; norm_num
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 h

theorem XiE_le_one : ∀ (k r : ℕ) (μK : Measure (Mt k r)), 1 ≤ k → IsKMeas k r μK →
    ∀ g ∈ GV k r, XiE k r μK g ≤ 1 := by
  intro k r μK hk hμ g hg
  exact lintegral_le_one_of_lintegral_sq_eq_one μK hμ.2 _ (LeOne.lintegral_vHalf_sq k r μK hk hμ g hg)

end GlobalTheory.HCXi
