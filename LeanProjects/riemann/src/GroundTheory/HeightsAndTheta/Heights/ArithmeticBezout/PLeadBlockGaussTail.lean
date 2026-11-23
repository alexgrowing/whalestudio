import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadBlockGaussTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Finset

open scoped ENNReal

noncomputable section

namespace LeadBlockGaussTail

theorem lintegral_pi_prod {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] :
    ∀ (n : ℕ) (f : Fin n → E → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) = ∏ i, ∫⁻ y, f i y ∂μ
  | 0, f, _ => by simp
  | n + 1, f, hf => by
      have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
      let g : E × (Fin n → E) → ℝ≥0∞ := fun a => f 0 a.1 * ∏ i : Fin n, f i.succ (a.2 i)
      have hg : Measurable fun a : Fin n → E => ∏ i : Fin n, f i.succ (a i) :=
        Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
      calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ)
          = ∫⁻ x, g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0 x)
              ∂Measure.pi (fun _ => μ) := by
            refine lintegral_congr fun x => ?_
            simp [g, Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
            rfl
        _ = ∫⁻ a, g a ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) :=
            e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) g
        _ = (∫⁻ y, f 0 y ∂μ) * ∫⁻ x, ∏ i : Fin n, f i.succ (x i) ∂(Measure.pi fun _ : Fin n => μ) :=
            lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable
        _ = ∏ i, ∫⁻ y, f i y ∂μ := by
            rw [lintegral_pi_prod μ n _ (fun i => hf i.succ), Fin.prod_univ_succ]

def halfGauss : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2 / 2)))

theorem halfGauss_lt_top : halfGauss < ∞ := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (1 / 2 : ℂ))
    (by norm_num) 0 0).norm
  have h2 : Integrable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2 / 2))) := by
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.norm_exp]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  exact h2.lintegral_lt_top

def entryConst : ℝ := 4 * (2 * halfGauss.toReal + Real.pi)

theorem entryConst_pos : 0 < entryConst := by
  unfold entryConst
  have := Real.pi_pos
  have : 0 ≤ halfGauss.toReal := ENNReal.toReal_nonneg
  positivity

def ballInd (ρ : ℝ) (z : ℂ) : ℝ≥0∞ := {z : ℂ | |ρ| * ‖z‖ < 1}.indicator 1 z

theorem measurable_ballInd (ρ : ℝ) : Measurable (ballInd ρ) :=
  measurable_const.indicator (measurableSet_lt (by fun_prop) measurable_const)

theorem ballInd_le_one (ρ : ℝ) (z : ℂ) : ballInd ρ z ≤ 1 := by
  unfold ballInd Set.indicator
  split_ifs <;> simp

theorem ballInd_zero (z : ℂ) : ballInd 0 z = 1 := by
  simp [ballInd]

theorem exp_mul_pow_le {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p ≤ 1) :
    Real.exp (-t) * t ^ p ≤ 2 * Real.exp (-(t / 2)) := by
  have h1 := Real.add_one_le_exp (t / 2)
  have h2 : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (-(t / 2))
  have h5 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  interval_cases p
  · rw [pow_zero, mul_one, h2]; nlinarith
  · rw [pow_one, h2]; nlinarith [mul_pos h4 h4]

theorem entry_bound (ρ : ℝ) (p : ℕ) (hp : p ≤ 1) :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * ballInd ρ z ≤
      ENNReal.ofReal (entryConst / (1 + ρ ^ 2) ^ (p + 1)) := by
  have hG := halfGauss_lt_top
  have hG0 : 0 ≤ halfGauss.toReal := ENNReal.toReal_nonneg
  have hpi := Real.pi_pos
  have hq : 0 < (1 + ρ ^ 2) ^ (p + 1) := by positivity
  have h24 : (2 : ℝ) ^ (p + 1) ≤ 4 := by interval_cases p <;> norm_num
  rcases le_or_gt (ρ ^ 2) 1 with hρ | hρ
  · calc _ ≤ ∫⁻ z : ℂ, 2 * ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2 / 2))) := by
          refine lintegral_mono fun z => ?_
          calc _ ≤ ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * 1 := by
                gcongr; exact ballInd_le_one ρ z
            _ = ENNReal.ofReal (Real.exp (-‖z‖ ^ 2) * (‖z‖ ^ 2) ^ p) := by
                rw [mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            _ ≤ ENNReal.ofReal (2 * Real.exp (-(‖z‖ ^ 2 / 2))) :=
                ENNReal.ofReal_le_ofReal (exp_mul_pow_le (by positivity) hp)
            _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ = 2 * halfGauss := lintegral_const_mul' _ _ (by simp)
      _ = ENNReal.ofReal (2 * halfGauss.toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hG.ne]; simp
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hq]
          have h4 : (1 + ρ ^ 2) ^ (p + 1) ≤ 4 :=
            (pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24
          unfold entryConst
          nlinarith
  · have hρ0 : 0 < |ρ| := abs_pos.2 (by rintro rfl; norm_num at hρ)
    have hset : {z : ℂ | |ρ| * ‖z‖ < 1} = Metric.ball (0 : ℂ) |ρ|⁻¹ := by
      ext z
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
      rw [← one_div, lt_div_iff₀ hρ0, mul_comm]
    have hu : (|ρ|⁻¹) ^ 2 = (ρ ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
    calc _ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) *
          (Metric.ball (0 : ℂ) |ρ|⁻¹).indicator 1 z := by
          refine lintegral_mono fun z => ?_
          unfold ballInd
          rw [hset]
          by_cases hz : z ∈ Metric.ball (0 : ℂ) |ρ|⁻¹
          · rw [Set.indicator_of_mem hz]
            have hz' : ‖z‖ ^ 2 ≤ (ρ ^ 2)⁻¹ := by
              rw [Metric.mem_ball, dist_zero_right] at hz
              rw [← hu]; exact pow_le_pow_left₀ (norm_nonneg _) hz.le 2
            have he : ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) ≤ 1 :=
              ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z]))
            calc _ ≤ 1 * ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * 1 := by
                  gcongr
                  simp
              _ = _ := by simp
          · rw [Set.indicator_of_notMem hz]; simp
      _ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * volume (Metric.ball (0 : ℂ) |ρ|⁻¹) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one measurableSet_ball]
      _ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi)) := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (inv_nonneg.2 hρ0.le), hu,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hq]
          have hρ2 : 0 < ρ ^ 2 := by linarith
          have hu1 : (ρ ^ 2)⁻¹ * ρ ^ 2 = 1 := inv_mul_cancel₀ hρ2.ne'
          have hu0 : 0 < (ρ ^ 2)⁻¹ := inv_pos.2 hρ2
          have hule : (ρ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ.le
          have key : (ρ ^ 2)⁻¹ * (1 + ρ ^ 2) = (ρ ^ 2)⁻¹ + 1 := by rw [mul_add, hu1, mul_one]
          have h2 : ((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi) * (1 + ρ ^ 2) ^ (p + 1) =
              Real.pi * ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) := by
            rw [← key, mul_pow]; ring
          have h3 : ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) ≤ 4 :=
            (pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24
          rw [h2]
          unfold entryConst
          nlinarith

theorem norm_det_sq_le {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    ‖(coordPlaneBlock π).det‖ ^ 2 ≤ (Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2 := by
  have h1 : ‖(coordPlaneBlock π).det‖ ≤
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, norm_prod, coordPlaneBlock, Matrix.transpose_apply]
  calc ‖(coordPlaneBlock π).det‖ ^ 2
      ≤ (∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))
          (f := fun σ => ∏ i, ‖π i (Fin.castAdd k (σ i))‖)
        simpa [Finset.card_univ, Finset.prod_pow] using this

theorem linProj_smul_firstCoordVec {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) (i : Fin m) :
    linProj π ((r : ℂ) • firstCoordVec n) i = (r : ℂ) * π i c0 := by
  simp only [linProj, firstCoordVec]
  simp
  rw [Finset.sum_eq_single c0]
  · simp [hc0, mul_comm]
  · intro j _ hj
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (h.trans hc0.symm))
    simp [this]
  · simp

theorem ball_indicator_le {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) ≤
      ∏ i, ballInd r (π i c0) := by
  by_cases hv : linProj π ((r : ℂ) • firstCoordVec n) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1
  · rw [Set.indicator_of_mem hv]
    have : ∀ i, ballInd r (π i c0) = 1 := by
      intro i
      have hi := PiLp.norm_apply_le (linProj π ((r : ℂ) • firstCoordVec n)) i
      rw [linProj_smul_firstCoordVec π r c0 hc0 i, norm_mul, Complex.norm_real,
        Real.norm_eq_abs] at hi
      rw [Metric.mem_ball, dist_zero_right] at hv
      simp [ballInd, Set.indicator, show |r| * ‖π i c0‖ < 1 from hi.trans_lt hv]
    simp [this]
  · rw [Set.indicator_of_notMem hv]; exact bot_le

theorem matGauss_eq_prod {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    matGauss π = ∏ i, ∏ j, ENNReal.ofReal (Real.exp (-‖π i j‖ ^ 2)) := by
  unfold matGauss
  rw [← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]

def entryFn (r : ℝ) {n : ℕ} (c0 s j : Fin n) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ (if j = s then 1 else 0)) *
    ballInd (if j = c0 then r else 0) z

theorem integrand_le {m k : ℕ} (hm : 0 < m) (r : ℝ) (π : Fin m → Fin (m + k) → ℂ) :
    matGauss π * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) ≤
      ENNReal.ofReal (Fintype.card (Equiv.Perm (Fin m))) * ∑ σ : Equiv.Perm (Fin m),
        ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) := by
  have hc0 : ((Fin.castAdd k (⟨0, hm⟩ : Fin m) : Fin (m + k)) : ℕ) = 0 := rfl
  have hrow : ∀ σ : Equiv.Perm (Fin m),
      ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) =
      matGauss π * ENNReal.ofReal (∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) *
        ∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩)) := by
    intro σ
    rw [matGauss_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    simp only [entryFn, Finset.prod_mul_distrib]
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_single (Fin.castAdd k (σ i)) (fun j _ hj => by simp [hj]) (by simp)]
      simp
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj, ballInd_zero])
        (by simp)]
      simp
  simp_rw [hrow]
  calc _ ≤ matGauss π * (∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩))) *
        ENNReal.ofReal ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
          ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) := by
        gcongr
        · exact ball_indicator_le π r _ hc0
        · exact norm_det_sq_le π
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun σ _ => by positivity)]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring

theorem prod_entry_eq {m k : ℕ} (hm : 0 < m) (K r : ℝ) (σ : Equiv.Perm (Fin m)) :
    ∏ i : Fin m, ∏ j : Fin (m + k), K / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      K ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1) := by
  have hrow : ∀ i : Fin m, ∏ j : Fin (m + k),
      (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      (1 + r ^ 2) ^ ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) := by
    intro i
    rw [Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj]; simp)
      (by simp)]
    simp
  have hsum : ∑ i : Fin m,
      ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) = m + 1 := by
    have h : ∀ i : Fin m, (Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i)) ↔
        (σ.symm ⟨0, hm⟩ = i) := by
      intro i
      rw [(Fin.castAdd_injective _ _).eq_iff, Equiv.symm_apply_eq]
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [add_comm]
  simp_rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hrow,
    Finset.prod_pow_eq_pow_sum, hsum, ← pow_mul]
  ring_nf

theorem proof : LeadBlockGaussTail.Statement := by
  intro m k hm
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin m)) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hK := entryConst_pos
  refine ⟨N * (N * entryConst ^ (m * (m + k))), fun r => ?_⟩
  have hφ : ∀ s j : Fin (m + k), Measurable (entryFn r (Fin.castAdd k ⟨0, hm⟩) s j) := fun s j =>
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))).mul (measurable_ballInd _)
  have hrowm : ∀ σ : Equiv.Perm (Fin m), ∀ i : Fin m, Measurable fun x : Fin (m + k) → ℂ =>
      ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (x j) :=
    fun σ i => Finset.measurable_prod _ fun j _ => (hφ _ j).comp (measurable_pi_apply j)
  have hq : 0 < (1 + r ^ 2) ^ (m + 1) := by positivity
  calc _ ≤ ∫⁻ π : Fin m → Fin (m + k) → ℂ, ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) :=
        lintegral_mono (integrand_le hm r)
    _ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ∏ i, ∏ j, ∫⁻ z, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j z := by
        have hmeas : ∀ σ : Equiv.Perm (Fin m), Measurable fun π : Fin m → Fin (m + k) → ℂ =>
            ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) :=
          fun σ => Finset.measurable_prod _ fun i _ => (hrowm σ i).comp (measurable_pi_apply i)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun σ _ => hmeas σ)]
        congr 1
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [volume_pi, lintegral_pi_prod _ m _ (hrowm σ)]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [volume_pi, lintegral_pi_prod _ (m + k) _ (fun j => hφ _ j)]
    _ ≤ ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, ∏ j : Fin (m + k),
          ENNReal.ofReal (entryConst / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
            ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1)) := by
        gcongr with σ _ i _ j _
        exact entry_bound _ _ (by split_ifs <;> omega)
    _ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ENNReal.ofReal (entryConst ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1)) := by
        congr 1
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_congr rfl fun i _ =>
            (ENNReal.ofReal_prod_of_nonneg fun j _ => div_nonneg hK.le (by positivity)).symm,
          ← ENNReal.ofReal_prod_of_nonneg fun i _ =>
            Finset.prod_nonneg fun j _ => div_nonneg hK.le (by positivity),
          prod_entry_eq hm]
    _ = ENNReal.ofReal (N * (N * entryConst ^ (m * (m + k))) / (1 + r ^ 2) ^ (m + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hN0]
        congr 1
        rw [hN]
        ring

end LeadBlockGaussTail

end

end GroundTheory.Heights₂.Heights
