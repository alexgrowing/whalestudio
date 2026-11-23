import Formalism.RealPlaceAnalysis.Complexify

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

theorem slm_sq_lintegral_le {f : ℝ → ENNReal} (hf : AEMeasurable f (volume.restrict (Ioc (0:ℝ) 1))) :
    (∫⁻ s in Ioc (0:ℝ) 1, f s) ^ (2:ℝ) ≤ ∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0:ℝ) 1))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, one_mul] at hH
  calc (∫⁻ s in Ioc (0:ℝ) 1, f s) ^ (2:ℝ)
      ≤ ((∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ)) ^ (1 / (2:ℝ))) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow hH (by norm_num)
    _ = ∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num

private lemma eLpNorm_two_rpow_two_eq_lintegral {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} (f : Y → ℂ) :
    eLpNorm f 2 ν ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ← ENNReal.rpow_mul]
  norm_num

theorem slm_eLpNorm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (r : X → ℂ) (D : ℝ → X → ℂ) (hD : Measurable (Function.uncurry D))
    (hr : ∀ x, r x = ∫ s in (0:ℝ)..1, D s x) (B : ENNReal)
    (hB : ∀ s ∈ Ioc (0:ℝ) 1, eLpNorm (D s) 2 μ ≤ B) : eLpNorm r 2 μ ≤ B := by
  have hmeas : ∀ x, Measurable fun s => D s x := fun x => hD.of_uncurry_right
  have hpt : ∀ x, ‖r x‖ₑ ≤ ∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ := fun x => by
    rw [hr x, intervalIntegral.integral_of_le zero_le_one]
    exact enorm_integral_le_lintegral_enorm _
  have hsq : ∀ s ∈ Ioc (0:ℝ) 1, ∫⁻ x, ‖D s x‖ₑ ^ (2:ℝ) ∂μ ≤ B ^ (2:ℝ) := fun s hs => by
    rw [← eLpNorm_two_rpow_two_eq_lintegral]
    exact ENNReal.rpow_le_rpow (hB s hs) (by norm_num)
  have hmain : eLpNorm r 2 μ ^ (2:ℝ) ≤ B ^ (2:ℝ) := by
    rw [eLpNorm_two_rpow_two_eq_lintegral]
    calc ∫⁻ x, ‖r x‖ₑ ^ (2:ℝ) ∂μ
        ≤ ∫⁻ x, (∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ) ^ (2:ℝ) ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num)
      _ ≤ ∫⁻ x, (∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ ^ (2:ℝ)) ∂μ :=
          lintegral_mono fun x => slm_sq_lintegral_le (hmeas x).enorm.aemeasurable
      _ = ∫⁻ s in Ioc (0:ℝ) 1, ∫⁻ x, ‖D s x‖ₑ ^ (2:ℝ) ∂μ :=
          lintegral_lintegral_swap (((hD.comp measurable_swap).enorm.pow_const (2:ℝ)).aemeasurable)
      _ ≤ ∫⁻ s in Ioc (0:ℝ) 1, B ^ (2:ℝ) := setLIntegral_mono' measurableSet_Ioc hsq
      _ = B ^ (2:ℝ) := by simp [Real.volume_Ioc]
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).mp hmain

section Mat

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}

theorem slm_cd_iff {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiffOn ℝ k f s ↔ ∀ i j, ContDiffOn ℝ k (fun x => f x i j) s := contDiffOn_pi.trans (forall_congr' fun _ => contDiffOn_pi)

theorem slm_cd_mul {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hg : ContDiffOn ℝ k g s) : ContDiffOn ℝ k (fun x => f x * g x) s := by
  rw [slm_cd_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hf i l).mul (hg l j)

theorem slm_cd_conjT {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x)ᴴ) s := by
  rw [slm_cd_iff] at hf ⊢
  intro i j
  have := (Complex.conjCLE.contDiff (n := k)).comp_contDiffOn (hf j i)
  simpa [Function.comp_def, Matrix.conjTranspose_apply] using this

theorem slm_cd_det {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x).det) s := by
  rw [slm_cd_iff] at hf
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => ?_
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem slm_cd_adj {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x).adjugate) s := by
  rw [slm_cd_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  apply slm_cd_det
  rw [slm_cd_iff] at hf ⊢
  intro a b
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne h]
    exact hf a b

theorem slm_cd_inv {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hd : ∀ x ∈ s, (f x).det ≠ 0) : ContDiffOn ℝ k (fun x => (f x)⁻¹) s := by
  have hdi : ContDiffOn ℝ k (fun x => ((f x).det)⁻¹) s := (slm_cd_det hf).inv hd
  have hadj := slm_cd_adj hf
  rw [slm_cd_iff] at hadj ⊢
  intro i j
  refine (hdi.mul (hadj i j)).congr fun x _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']

end Mat

section Ret

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

local notation "JJ" => Formalism.REAL.Jm

theorem slm_JJ (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : JJ ε * (JJ ε * X) = X := by
  rw [← Matrix.mul_assoc]
  have h : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  rw [h, Matrix.one_mul]

theorem slm_inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : Formalism.REAL.inUJ ε a)
    (hb : Formalism.REAL.inUJ ε b) : Formalism.REAL.inUJ ε (a * b) := by
  unfold Formalism.REAL.inUJ at ha hb ⊢
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]

def slmJi (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  JJ ε * gᴴ * JJ ε

private lemma Jm_mul_Jm_self_eq_one (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  simpa using slm_JJ ε 1

private lemma Jm_conjTranspose_eq_Jm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem slm_Ji_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) : slmJi ε g * g = 1 := by
  unfold slmJi
  unfold Formalism.REAL.inUJ at hg
  calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jm_mul_Jm_self_eq_one]

theorem slm_mul_Ji {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) : g * slmJi ε g = 1 := by
  rw [← Matrix.inv_eq_left_inv (slm_Ji_mul hg)]
  exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (slm_Ji_mul hg))

theorem slm_Ji_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (slmJi ε g) := by
  have h1 : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by
    have := slm_mul_Ji hg
    unfold slmJi at this
    simpa only [Matrix.mul_assoc] using this
  unfold Formalism.REAL.inUJ slmJi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_Jm, Matrix.mul_assoc,
    slm_JJ, h1, Matrix.mul_one]

def slmP (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Y - JJ ε * Yᴴ * JJ ε)

theorem skewAdjointPart_isSkewAdjoint (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.inG ε (slmP ε Y) := by
  have hs : (star (1 / 2 : ℂ)) = 1 / 2 := by simp
  unfold Formalism.REAL.inG slmP
  rw [Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_sub]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_Jm, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, slm_JJ, Jm_mul_Jm_self_eq_one, Matrix.mul_one]
  rw [← smul_add]
  simp

theorem skewAdjointPart_eq_self_of_isSkewAdjoint {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Formalism.REAL.inG ε Y) : slmP ε Y = Y := by
  unfold Formalism.REAL.inG at hY
  have h1 : Yᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
  have h2 : Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε = -Y := by
    calc Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Yᴴ * Formalism.REAL.Jm ε) := Matrix.mul_assoc _ _ _
      _ = -(Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y)) := by rw [h1, Matrix.mul_neg]
      _ = -Y := by rw [slm_JJ]
  unfold slmP
  rw [h2, sub_neg_eq_add, ← two_smul ℂ Y, smul_smul]
  norm_num

theorem slm_Y_inG {h : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) (hd : (h + 1).det ≠ 0) :
    Formalism.REAL.inG ε ((h - 1) * (h + 1)⁻¹) := by
  have hu : IsUnit (h + 1).det := isUnit_iff_ne_zero.mpr hd
  have hA1 : (h + 1) * (h + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hA2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((h + 1)⁻¹)ᴴ * ((h + 1)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hA1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hm : (h - 1)ᴴ * Formalism.REAL.Jm ε * (h + 1) + (h + 1)ᴴ * Formalism.REAL.Jm ε * (h - 1) = 0 := by
    unfold Formalism.REAL.inUJ at hh
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hh]
    abel
  unfold Formalism.REAL.inG
  generalize h + 1 = A at hA1 hA2 hm ⊢
  generalize h - 1 = B at hm ⊢
  calc (B * A⁻¹)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (B * A⁻¹)
      = (A⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm ε * A + Aᴴ * Formalism.REAL.Jm ε * B) * A⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hA1, hA2, Matrix.mul_one]
    _ = 0 := by rw [hm, Matrix.mul_zero, Matrix.zero_mul]

theorem slm_cay_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (hd : (1 - X).det ≠ 0) :
    Formalism.REAL.inUJ ε ((1 + X) * (1 - X)⁻¹) := by
  have hu : IsUnit (1 - X).det := isUnit_iff_ne_zero.mpr hd
  have hC1 : (1 - X) * (1 - X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hC2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((1 - X)⁻¹)ᴴ * ((1 - X)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hC1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hm : (1 + X)ᴴ * Formalism.REAL.Jm ε * (1 + X) = (1 - X)ᴴ * Formalism.REAL.Jm ε * (1 - X) := by
    unfold Formalism.REAL.inG at hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hX']
    abel
  unfold Formalism.REAL.inUJ
  calc ((1 + X) * (1 - X)⁻¹)ᴴ * Formalism.REAL.Jm ε * ((1 + X) * (1 - X)⁻¹)
      = ((1 - X)⁻¹)ᴴ * ((1 + X)ᴴ * Formalism.REAL.Jm ε * (1 + X)) * (1 - X)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - X)⁻¹)ᴴ * ((1 - X)ᴴ * Formalism.REAL.Jm ε * (1 - X)) * (1 - X)⁻¹ := by rw [hm]
    _ = Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc, hC1, hC2, Matrix.mul_one]

theorem slm_cay_left {h : Matrix (Fin n) (Fin n) ℂ} (hd : (h + 1).det ≠ 0)
    (hd2 : (1 - (h - 1) * (h + 1)⁻¹).det ≠ 0) :
    (1 + (h - 1) * (h + 1)⁻¹) * (1 - (h - 1) * (h + 1)⁻¹)⁻¹ = h := by
  have hu : IsUnit (h + 1).det := isUnit_iff_ne_zero.mpr hd
  have hA1 : (h + 1) * (h + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hc : (h + 1) * (h - 1) = (h - 1) * (h + 1) := by noncomm_ring
  have e : (h + 1) * ((h - 1) * (h + 1)⁻¹) = h - 1 := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, hA1, Matrix.mul_one]
  have key : 1 + (h - 1) * (h + 1)⁻¹ = h * (1 - (h - 1) * (h + 1)⁻¹) := by
    calc 1 + (h - 1) * (h + 1)⁻¹ = h - (h + 1) * ((h - 1) * (h + 1)⁻¹) + (h - 1) * (h + 1)⁻¹ := by
          rw [e]; abel
      _ = h * (1 - (h - 1) * (h + 1)⁻¹) := by noncomm_ring
  have hu2 : IsUnit (1 - (h - 1) * (h + 1)⁻¹).det := isUnit_iff_ne_zero.mpr hd2
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.mul_one]

def slmX (ε : Fin n → Bool) (g0 g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  slmP ε ((slmJi ε g0 * g - 1) * (slmJi ε g0 * g + 1)⁻¹)

def slmRet (ε : Fin n → Bool) (g0 g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  g0 * ((1 + slmX ε g0 g) * (1 - slmX ε g0 g)⁻¹)

def cayleyChartDomain (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | (slmJi ε g0 * g + 1).det ≠ 0}

def slmV (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  cayleyChartDomain ε g0 ∩ (fun g => (1 - slmX ε g0 g).det) ⁻¹' {0}ᶜ

theorem slm_X_cd (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmX ε g0) (cayleyChartDomain ε g0) := by
  have h1 : ContDiffOn ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => slmJi ε g0 * g) (cayleyChartDomain ε g0) :=
    slm_cd_mul contDiffOn_const contDiffOn_id
  have hA : ContDiffOn ℝ ∞ (fun g => slmJi ε g0 * g - 1) (cayleyChartDomain ε g0) := h1.sub contDiffOn_const
  have hB : ContDiffOn ℝ ∞ (fun g => slmJi ε g0 * g + 1) (cayleyChartDomain ε g0) := h1.add contDiffOn_const
  have hY := slm_cd_mul hA (slm_cd_inv hB fun g hg => hg)
  have hJYJ := slm_cd_mul (slm_cd_mul (contDiffOn_const (c := JJ ε)) (slm_cd_conjT hY))
    (contDiffOn_const (c := JJ ε))
  exact (hY.sub hJYJ).const_smul (1 / 2 : ℂ)

theorem cayleyChartDomain_isOpen (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : IsOpen (cayleyChartDomain ε g0) := by
  show IsOpen {g : Matrix (Fin n) (Fin n) ℂ | (slmJi ε g0 * g + 1).det ≠ 0}
  exact isOpen_ne_fun ((continuous_const.matrix_mul continuous_id).add continuous_const).matrix_det
    continuous_const

theorem slm_V_open (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : IsOpen (slmV ε g0) :=
  ContinuousOn.isOpen_inter_preimage (f := fun g => (1 - slmX ε g0 g).det)
    ((continuous_id.matrix_det).comp_continuousOn (continuousOn_const.sub (slm_X_cd ε g0).continuousOn))
    (cayleyChartDomain_isOpen ε g0) isOpen_compl_singleton

theorem slm_ret_cd (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmRet ε g0) (slmV ε g0) := by
  have hX : ContDiffOn ℝ ∞ (slmX ε g0) (slmV ε g0) := (slm_X_cd ε g0).mono fun g hg => hg.1
  have hM : ContDiffOn ℝ ∞ (fun g => 1 - slmX ε g0 g) (slmV ε g0) := contDiffOn_const.sub hX
  have hP : ContDiffOn ℝ ∞ (fun g => 1 + slmX ε g0 g) (slmV ε g0) := contDiffOn_const.add hX
  have hI := slm_cd_inv hM fun g hg => hg.2
  exact slm_cd_mul contDiffOn_const (slm_cd_mul hP hI)

theorem slm_ret_inUJ {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∀ g ∈ slmV ε g0, Formalism.REAL.inUJ ε (slmRet ε g0 g) := fun g hg => slm_inUJ_mul hg0 (slm_cay_inUJ (skewAdjointPart_isSkewAdjoint ε _) hg.2)

theorem slm_ret_self {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∀ g ∈ slmV ε g0, Formalism.REAL.inUJ ε g → slmRet ε g0 g = g := by
  intro g hg hgU
  have hh : Formalism.REAL.inUJ ε (slmJi ε g0 * g) := slm_inUJ_mul (slm_Ji_inUJ hg0) hgU
  have hd : (slmJi ε g0 * g + 1).det ≠ 0 := hg.1
  have hXY : slmX ε g0 g = (slmJi ε g0 * g - 1) * (slmJi ε g0 * g + 1)⁻¹ :=
    skewAdjointPart_eq_self_of_isSkewAdjoint (slm_Y_inG hh hd)
  have hd2 : (1 - slmX ε g0 g).det ≠ 0 := hg.2
  rw [hXY] at hd2
  show g0 * ((1 + slmX ε g0 g) * (1 - slmX ε g0 g)⁻¹) = g
  rw [hXY, slm_cay_left hd hd2, ← Matrix.mul_assoc, slm_mul_Ji hg0, Matrix.one_mul]

theorem slm_mem_V {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) : g0 ∈ slmV ε g0 := by
  have h1 : slmJi ε g0 * g0 = 1 := slm_Ji_mul hg0
  have hW : g0 ∈ cayleyChartDomain ε g0 := by
    show (slmJi ε g0 * g0 + 1).det ≠ 0
    rw [h1, ← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), Matrix.det_smul, Matrix.det_one]
    simp
  have hX0 : slmX ε g0 g0 = 0 := by
    unfold slmX slmP
    rw [h1]
    simp
  show g0 ∈ cayleyChartDomain ε g0 ∧ (1 - slmX ε g0 g0).det ≠ 0
  refine ⟨hW, ?_⟩
  rw [hX0]
  simp

theorem slm_exists_ret (ε : Fin n → Bool) {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∃ (V : Set (Matrix (Fin n) (Fin n) ℂ)) (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ),
      IsOpen V ∧ g0 ∈ V ∧ ContDiffOn ℝ ∞ γ V ∧ (∀ g ∈ V, Formalism.REAL.inUJ ε (γ g)) ∧
        ∀ g ∈ V, Formalism.REAL.inUJ ε g → γ g = g :=
  ⟨slmV ε g0, slmRet ε g0, slm_V_open ε g0, slm_mem_V hg0, slm_ret_cd ε g0, slm_ret_inUJ hg0, slm_ret_self hg0⟩

end Ret

end ReciprocityTheory.ChartRestriction.DS
