import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryMulVecEqOfFormEq

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section
namespace GlobalTheory.Amp.EntryLaw

def sq {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

theorem sq_nonneg' {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sq x := by
  unfold sq
  exact Finset.sum_nonneg fun i _ => by positivity

theorem sq_cont {n : ℕ} : Continuous (sq (n := n)) := by
  unfold sq
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).norm).pow 2

theorem sq_smul {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sq (c • x) = c ^ 2 * sq x := by
  unfold sq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem star_dot {n : ℕ} (x : Fin n → ℂ) : star x ⬝ᵥ x = (sq x : ℂ) := by
  unfold sq
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem le_sq {n : ℕ} (x : Fin n → ℂ) (i : Fin n) : ‖x i‖ ^ 2 ≤ sq x := by
  unfold sq
  exact Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)

def cone (k : ℕ) (t : ℝ) : Set (Fin (k + 1) → ℂ) :=
  {x | sq x ≤ 1 ∧ (1 - t) * sq x ≤ ‖x (Fin.last k)‖ ^ 2}

theorem cone_closed (k : ℕ) (t : ℝ) : IsClosed (cone k t) := by
  unfold cone
  exact (isClosed_le sq_cont continuous_const).inter
    (isClosed_le (continuous_const.mul sq_cont) ((continuous_apply _).norm.pow 2))

theorem volume_annulus (a b : ℝ) (ha : 0 ≤ a) :
    volume {z : ℂ | a ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ b} = ENNReal.ofReal (Real.pi * (b - a)) := by
  rcases lt_or_ge b a with hba | hab
  · have hempty : {z : ℂ | a ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ b} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro h
      linarith
    rw [hempty, measure_empty, ENNReal.ofReal_of_nonpos]
    nlinarith [Real.pi_pos]
  · have hb : 0 ≤ b := ha.trans hab
    have hset : {z : ℂ | a ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ b} =
        Metric.closedBall 0 (√b) \ Metric.ball 0 (√a) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        dist_zero_right, not_lt]
      have hz := norm_nonneg z
      have hsb := Real.sq_sqrt hb
      have hsa := Real.sq_sqrt ha
      have hb0 := Real.sqrt_nonneg b
      have ha0 := Real.sqrt_nonneg a
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · by_contra hc
          push Not at hc
          nlinarith
        · by_contra hc
          push Not at hc
          nlinarith
      · rintro ⟨h1, h2⟩
        constructor <;> nlinarith
    have hsub : Metric.ball (0 : ℂ) (√a) ⊆ Metric.closedBall 0 (√b) :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt hab))
    rw [hset, measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet measure_ball_lt_top.ne,
      Complex.volume_closedBall, Complex.volume_ball]
    have hpi : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt hb, Real.sq_sqrt ha, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_sub _ (mul_nonneg ha Real.pi_pos.le)]
    congr 1
    ring

theorem volume_cone_eq (k : ℕ) (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1) :
    volume (cone k t) = ∫⁻ y : Fin k → ℂ, ENNReal.ofReal (Real.pi * (1 - sq y / t)) := by
  have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k))
      volume (volume.prod volume) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure ℂ)) (Fin.last k)
  have hSc : IsClosed {p : ℂ × (Fin k → ℂ) | (1 - t) * sq p.2 / t ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 1 - sq p.2} :=
    (isClosed_le ((continuous_const.mul (sq_cont.comp continuous_snd)).div_const t)
      (continuous_fst.norm.pow 2)).inter
      (isClosed_le (continuous_fst.norm.pow 2) (continuous_const.sub (sq_cont.comp continuous_snd)))
  have hpre : cone k t = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k) ⁻¹'
      {p : ℂ × (Fin k → ℂ) | (1 - t) * sq p.2 / t ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 1 - sq p.2} := by
    ext x
    have hsplit : sq x = sq (Fin.removeNth (Fin.last k) x) + ‖x (Fin.last k)‖ ^ 2 := by
      unfold sq
      rw [Fin.sum_univ_castSucc]
      simp [Fin.removeNth, Fin.succAbove_last]
    simp only [cone, Set.mem_ofPred_eq, Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply]
    rw [hsplit, div_le_iff₀ h0]
    have := sq_nonneg' (Fin.removeNth (Fin.last k) x)
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hpre, he.measure_preimage hSc.measurableSet.nullMeasurableSet, Measure.prod_apply_symm hSc.measurableSet]
  refine lintegral_congr fun y => ?_
  have hy := sq_nonneg' y
  rw [show (fun z : ℂ => (z, y)) ⁻¹' {p : ℂ × (Fin k → ℂ) | (1 - t) * sq p.2 / t ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 1 - sq p.2}
      = {z : ℂ | (1 - t) * sq y / t ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1 - sq y} from rfl,
    volume_annulus _ _ (div_nonneg (mul_nonneg (sub_nonneg.2 h1) hy) h0.le)]
  congr 1
  field_simp
  ring

theorem volume_cone (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    volume (cone k t) = ENNReal.ofReal (t ^ k) * volume (cone k 1) := by
  have hpos : ∀ s : ℝ, 0 < s → s ≤ 1 →
      volume (cone k s) = ENNReal.ofReal (s ^ k) * volume (cone k 1) := by
    intro s hs0 hs1
    rw [volume_cone_eq k s hs0 hs1, volume_cone_eq k 1 one_pos le_rfl]
    have hc : (√s)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hs0).ne'
    have hF : Measurable fun y : Fin k → ℂ => ENNReal.ofReal (Real.pi * (1 - sq y / 1)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.sub (sq_cont.measurable.div_const _)))
    have hcomp : ∫⁻ y : Fin k → ℂ, ENNReal.ofReal (Real.pi * (1 - sq y / s)) =
        ∫⁻ y : Fin k → ℂ, ENNReal.ofReal (Real.pi * (1 - sq ((√s)⁻¹ • y) / 1)) := by
      refine lintegral_congr fun y => ?_
      rw [sq_smul, inv_pow, Real.sq_sqrt hs0.le, div_one, inv_mul_eq_div]
    have hd : Module.finrank ℝ (Fin k → ℂ) = 2 * k := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [hcomp, ← lintegral_map hF (measurable_const_smul _), Measure.map_addHaar_smul volume hc,
      lintegral_smul_measure, smul_eq_mul]
    congr 2
    rw [hd, abs_of_nonneg (by positivity), pow_mul, inv_pow, Real.sq_sqrt hs0.le, inv_pow, inv_inv]
  have hfin : volume (cone k 1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Fin (k + 1) → ℂ)) (r := 1)).ne
      (measure_mono ?_)
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h := (le_sq x i).trans hx.1
    nlinarith [norm_nonneg (x i)]
  rcases h0.lt_or_eq with ht | ht
  · exact hpos t ht h1
  · subst ht
    rw [zero_pow (by omega : k ≠ 0), ENNReal.ofReal_zero, zero_mul]
    refine le_antisymm ?_ (by simp)
    have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ k) * volume (cone k 1)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((continuous_pow k).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rw [zero_pow (by omega : k ≠ 0)] at h
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h) (Or.inr hfin)
      rwa [ENNReal.ofReal_zero, zero_mul] at h2
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
    rw [← hpos s hs.1 hs.2]
    refine measure_mono fun x hx => ⟨hx.1, ?_⟩
    have := sq_nonneg' x
    have := hx.2
    nlinarith [hs.1]

theorem volume_cone_one_ne_zero (k : ℕ) : volume (cone k 1) ≠ 0 := by
  have hr : (0 : ℝ) < 1 / (k + 1) := by positivity
  refine (lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : Fin (k + 1) → ℂ) hr) (measure_mono ?_)).ne'
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have hxi : ∀ i, ‖x i‖ ≤ 1 / (k + 1) := fun i => (norm_le_pi_norm x i).trans hx.le
  have hk : (1 : ℝ) ≤ k + 1 := by have := k.cast_nonneg (α := ℝ); linarith
  have hr1 : (1 / ((k : ℝ) + 1)) * ((k : ℝ) + 1) = 1 := by field_simp
  refine ⟨?_, by rw [sub_self, zero_mul]; positivity⟩
  calc sq x = ∑ i, ‖x i‖ ^ 2 := rfl
    _ ≤ ∑ _i : Fin (k + 1), (1 / ((k : ℝ) + 1)) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hxi i) 2
    _ = ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) ^ 2 := by simp
    _ ≤ 1 := by nlinarith

theorem volume_cone_one_ne_top (k : ℕ) : volume (cone k 1) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Fin (k + 1) → ℂ)) (r := 1)).ne
    (measure_mono ?_)
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h := (le_sq x i).trans hx.1
  nlinarith [norm_nonneg (x i)]

theorem measurePreserving_vecMul {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (h : gᴴ * g = 1) :
    MeasurePreserving (fun x : Fin n → ℂ => x ᵥ* g) volume volume := by
  have hdet : LinearMap.det ((Matrix.vecMulLinear g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, ← Matrix.mulVecLin_transpose, ← Matrix.toLin'_apply',
      LinearMap.det_toLin', Matrix.det_transpose, Algebra.norm_complex_apply]
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self] at h1
    exact_mod_cast h1
  refine ⟨(continuous_id.matrix_vecMul continuous_const).measurable, ?_⟩
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.vecMulLinear g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  exact hmap

theorem sq_vecMul {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (h : gᴴ * g = 1) (x : Fin n → ℂ) :
    sq (x ᵥ* g) = sq x := by
  have h' : g * gᴴ = 1 := mul_eq_one_comm.mp h
  have key : star (x ᵥ* g) ⬝ᵥ (x ᵥ* g) = star x ⬝ᵥ x := by
    rw [Matrix.star_vecMul, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h',
      Matrix.one_mulVec, dotProduct_comm]
  rw [star_dot, star_dot] at key
  exact_mod_cast key

theorem exists_row {n : ℕ} (l : Fin n) (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ h : Matrix (Fin n) (Fin n) ℂ, hᴴ * h = 1 ∧ 0 < sq x ∧ x = √(sq x) • h l := by
  have hs : 0 < sq x := by
    refine lt_of_le_of_ne (sq_nonneg' x) fun h0 => hx ?_
    funext i
    have h1 := le_sq x i
    rw [← h0] at h1
    have h2 : ‖x i‖ = 0 := by nlinarith [norm_nonneg (x i)]
    simpa using h2
  have hsu : sq ((√(sq x))⁻¹ • x) = 1 := by
    rw [sq_smul, inv_pow, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
  have he : star (Pi.single l (1 : ℂ)) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single l 1) = 1 := by
    simp
  obtain ⟨γ, hγ, hγe⟩ := GlobalTheory.exists_unitary_mulVec_eq_of_form_eq ℂ n 1 (by simp) (by simp)
    (Pi.single l 1) (star ((√(sq x))⁻¹ • x))
    (by rw [he, Matrix.one_mulVec, star_star, dotProduct_comm, star_dot, hsu, Complex.ofReal_one])
    (by rw [he]; exact one_ne_zero)
  rw [Matrix.mul_one] at hγ
  refine ⟨γᴴ, by rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hγ, hs, ?_⟩
  have hrow : γᴴ l = (√(sq x))⁻¹ • x := by
    funext j
    have hj := congrFun hγe j
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hj
    rw [Matrix.conjTranspose_apply]
    rw [hj, Pi.star_apply, star_star]
  rw [hrow, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hs).ne', one_smul]

theorem measure_entry : ∀ (k : ℕ) (μ : Measure (PI.MtM (k + 1))), 1 ≤ k →
    PI.IsHaarOnM (UH (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) μ → μ Set.univ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} = ENNReal.ofReal (t ^ k) := by
  intro k μ hk hμ hμ1 t ht0 ht1
  obtain ⟨hσ, -, hnull, hinv⟩ := hμ
  have hU : ∀ᵐ g ∂μ, (Matrix.of g)ᴴ * Matrix.of g = 1 := by
    filter_upwards [ae_iff.mpr hnull] with g hg
    simpa [UH] using hg
  have hE'm : MeasurableSet {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2} :=
    (isClosed_le continuous_const
      (((continuous_apply (Fin.last k)).comp (continuous_apply (Fin.last k))).norm.pow 2)).measurableSet

  have hEE : μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} =
      μ {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2} := by
    refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
    filter_upwards [hU] with g hg
    have hc : star (fun i => g i (Fin.last k)) ⬝ᵥ (fun i => g i (Fin.last k)) = 1 := by
      have h2 := congrFun (congrFun hg (Fin.last k)) (Fin.last k)
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h2
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply] at h2
      simpa only [dotProduct, Pi.star_apply] using h2
    rw [star_dot] at hc
    have h1 : sq (fun i => g i (Fin.last k)) = 1 := by exact_mod_cast hc
    have hle := le_sq (fun i => g i (Fin.last k)) (Fin.last k)
    rw [h1] at hle
    show |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t ↔ 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    constructor <;> intro h <;> linarith

  have hcont : Continuous fun q : PI.MtM (k + 1) × (Fin (k + 1) → ℂ) => q.2 ᵥ* Matrix.of q.1 :=
    continuous_snd.matrix_vecMul continuous_fst
  have hSm : MeasurableSet {q : PI.MtM (k + 1) × (Fin (k + 1) → ℂ) | q.2 ᵥ* Matrix.of q.1 ∈ cone k t} :=
    ((cone_closed k t).preimage hcont).measurableSet

  have hA : (μ.prod volume) {q : PI.MtM (k + 1) × (Fin (k + 1) → ℂ) | q.2 ᵥ* Matrix.of q.1 ∈ cone k t} =
      volume (cone k t) := by
    rw [Measure.prod_apply hSm]
    have h2 : ∀ᵐ g ∂μ, volume (Prod.mk g ⁻¹'
        {q : PI.MtM (k + 1) × (Fin (k + 1) → ℂ) | q.2 ᵥ* Matrix.of q.1 ∈ cone k t}) = volume (cone k t) := by
      filter_upwards [hU] with g hg
      exact (measurePreserving_vecMul (Matrix.of g) hg).measure_preimage
        (cone_closed k t).measurableSet.nullMeasurableSet
    rw [lintegral_congr_ae h2, lintegral_const, hμ1, mul_one]

  have hB : (μ.prod volume) {q : PI.MtM (k + 1) × (Fin (k + 1) → ℂ) | q.2 ᵥ* Matrix.of q.1 ∈ cone k t} =
      μ {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2} * volume (cone k 1) := by
    rw [Measure.prod_apply_symm hSm, ← lintegral_indicator_const (cone_closed k 1).measurableSet]
    refine lintegral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Fin (k + 1) → ℂ))] with x hx0
    have hx : x ≠ 0 := hx0
    by_cases hx1 : sq x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ cone k 1 from ⟨hx1, by rw [sub_self, zero_mul]; positivity⟩)]
      obtain ⟨h, hh, hs, hxe⟩ := exists_row (Fin.last k) x hx
      have hhU : h ∈ UH (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := by
        simpa [UH] using hh
      have hlc : Continuous (PI.lmulQ h) := by
        unfold PI.lmulQ
        exact continuous_const.matrix_mul continuous_id
      have hlm : Measurable (PI.lmulQ h) := hlc.measurable
      calc μ ((fun g => (g, x)) ⁻¹'
            {q : PI.MtM (k + 1) × (Fin (k + 1) → ℂ) | q.2 ᵥ* Matrix.of q.1 ∈ cone k t})
          = μ (PI.lmulQ h ⁻¹' {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2}) := by
            refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
            filter_upwards [hU] with g hg
            have e1 : sq (x ᵥ* Matrix.of g) = sq x := sq_vecMul _ hg x
            have hv : x ᵥ* Matrix.of g = √(sq x) • (h (Fin.last k) ᵥ* Matrix.of g) := by
              rw [← Matrix.smul_vecMul, ← hxe]
            have e2 : ‖(x ᵥ* Matrix.of g) (Fin.last k)‖ ^ 2 =
                sq x * ‖(h * Matrix.of g) (Fin.last k) (Fin.last k)‖ ^ 2 := by
              rw [hv, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
                Real.sq_sqrt (sq_nonneg' x)]
              rfl
            show sq (x ᵥ* Matrix.of g) ≤ 1 ∧ (1 - t) * sq (x ᵥ* Matrix.of g) ≤
                ‖(x ᵥ* Matrix.of g) (Fin.last k)‖ ^ 2 ↔
              1 - t ≤ ‖(h * Matrix.of g) (Fin.last k) (Fin.last k)‖ ^ 2
            rw [e1, e2]
            constructor
            · rintro ⟨-, h2⟩
              exact le_of_mul_le_mul_left (by linarith) hs
            · intro hN
              have := mul_le_mul_of_nonneg_left hN hs.le
              exact ⟨hx1, by linarith⟩
        _ = μ.map (PI.lmulQ h) {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2} :=
            (Measure.map_apply hlm hE'm).symm
        _ = μ {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2} := by
            rw [hinv h hhU]
    · rw [Set.indicator_of_notMem (fun hm => hx1 hm.1)]
      refine measure_mono_null ?_ (ae_iff.mp hU)
      intro g hg hgU
      have e1 : sq (x ᵥ* Matrix.of g) = sq x := sq_vecMul _ hgU x
      exact hx1 (e1 ▸ hg.1)
  have key : μ {g : PI.MtM (k + 1) | 1 - t ≤ ‖g (Fin.last k) (Fin.last k)‖ ^ 2} * volume (cone k 1) =
      ENNReal.ofReal (t ^ k) * volume (cone k 1) := by
    rw [← hB, hA, volume_cone k hk t ht0 ht1]
  rw [hEE]
  exact (ENNReal.mul_left_inj (volume_cone_one_ne_zero k) (volume_cone_one_ne_top k)).mp key

end GlobalTheory.Amp.EntryLaw
