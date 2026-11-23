import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartLim

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def expC (k r : ℕ) : lieE (UWb k r) → Mt k r :=
  fun x i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j

theorem bBall_eq (k r : ℕ) (ρ : ℝ) : bBall k r ρ = expC k r '' Metric.ball 0 ρ := rfl

def HaarDens : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh ∧
    ∃ δ : lieE (UWb k r) → ℝ≥0∞, ContinuousAt δ 0 ∧ δ 0 ≠ 0 ∧ δ 0 ≠ ⊤ ∧
      ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → νh (bBall k r ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x

namespace GE

variable {k r : ℕ}

def p0 (k r : ℕ) : Fin (2 * r + k + 1) := wI k r 0

theorem firstMiddle_val : (p0 k r).val = r := by
  show r + (0 : Fin (k + 1)).val = r
  simp

theorem splitHermForm_firstMiddle_apply (j : Fin (2 * r + k + 1)) (hj : j ≠ p0 k r) : Hpk k r (p0 k r) j = 0 := by
  have hv := firstMiddle_val (k := k) (r := r)
  simp only [Hpk]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega)

theorem splitHermForm_apply_firstMiddle (i : Fin (2 * r + k + 1)) (hi : i ≠ p0 k r) : Hpk k r i (p0 k r) = 0 := by
  have hv := firstMiddle_val (k := k) (r := r)
  simp only [Hpk]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega)

def dg (k r : ℕ) (u : ℂ) : Mat k r := diagonal fun i => if i = p0 k r then u else 1

theorem dg_uh (u : ℂ) (hu : star u * u = 1) : dg k r u ∈ UH (Hpk k r) := by
  show (dg k r u)ᴴ * Hpk k r * dg k r u = Hpk k r
  unfold dg
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul]
  by_cases hi : i = p0 k r <;> by_cases hj : j = p0 k r
  · subst hi
    subst hj
    simp only [Pi.star_apply, if_true]
    linear_combination (Hpk k r (p0 k r) (p0 k r)) * hu
  · subst hi
    simp only [Pi.star_apply, if_true, if_neg hj, splitHermForm_firstMiddle_apply j hj, mul_zero, zero_mul]
  · subst hj
    simp only [Pi.star_apply, if_true, if_neg hi, splitHermForm_apply_firstMiddle i hi, mul_zero, zero_mul]
  · simp only [Pi.star_apply, if_neg hi, if_neg hj, star_one, one_mul, mul_one]

theorem dg_fix (u : ℂ) (e : Fin (2 * r + k + 1)) (he : e ≠ p0 k r) : dg k r u *ᵥ bvec e = bvec e := by
  funext x
  unfold dg
  rw [Matrix.mulVec_diagonal]
  by_cases hx : x = e
  · subst hx
    simp [he]
  · simp [bvec, hx]

theorem dg_mem (u : ℂ) (hu : star u * u = 1) : dg k r u ∈ UWb k r := by
  show dg k r u ∈ UH (Hpk k r) ∧ ∀ a : Fin r, dg k r u *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
    dg k r u *ᵥ bvec (esI k r a) = bvec (esI k r a)
  have hv := firstMiddle_val (k := k) (r := r)
  refine ⟨dg_uh u hu, fun a => ⟨dg_fix u _ ?_, dg_fix u _ ?_⟩⟩
  · intro h
    have h1 : (eI k r a).val = (p0 k r).val := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have h3 := a.isLt
    omega
  · intro h
    have h1 : (esI k r a).val = (p0 k r).val := congrArg Fin.val h
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    have h3 := a.isLt
    omega

def dV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := fun i => if i = p0 k r then Complex.I else 0

theorem exp_dV (t : ℝ) : NormedSpace.exp ((t : ℂ) • diagonal (dV k r)) = dg k r (Complex.exp (t * Complex.I)) := by
  unfold dg
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  simp only [Pi.smul_apply, dV, smul_eq_mul]
  split_ifs
  · rw [Complex.exp_eq_exp_ℂ]
  · rw [mul_zero, NormedSpace.exp_zero]

theorem unit_exp (t : ℝ) : star (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem lie_nontrivial : Nontrivial (lieE (UWb k r)) := by
  rw [Submodule.nontrivial_iff_ne_bot, Submodule.ne_bot_iff]
  refine ⟨(WithLp.equiv 2 _).symm (realifyFun (diagonal (dV k r))), Submodule.subset_span
    ⟨diagonal (dV k r), (show diagonal (dV k r) ∈ lieOf (UWb k r) from fun t => by
      rw [exp_dV]
      exact dg_mem _ (unit_exp t)), rfl⟩, ?_⟩
  intro h
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) =>
    x (p0 k r, p0 k r, true)) h
  simp [realifyFun, dV] at h1

theorem haarOn_smul (S : Set (Mat k r)) (ν : Measure (Mt k r)) (c : ℝ≥0) (hc : c ≠ 0) (h : IsHaarOn S ν) :
    IsHaarOn S (c • ν) := by
  refine ⟨?_, ?_, ?_, fun s hs => ?_⟩
  · have := h.1
    infer_instance
  · intro h0
    apply h.2.1
    rw [← Measure.measure_univ_eq_zero]
    have h1 := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simpa [hc] using h1
  · rw [Measure.smul_apply, h.2.2.1, smul_zero]
  · rw [Measure.map_smul, h.2.2.2 s hs]

theorem tBall_mass (ν : Measure (Mt k r)) (h : IsHaarOn (UWb k r) ν) (m : Mat k r) (hm : m ∈ UWb k r) (ρ : ℝ) :
    ν (tBall k r m ρ) = ν (bBall k r ρ) := by
  have hinv := HU.uwb_inv hm
  have hB : MeasurableSet (bBall k r ρ) := measurableSet_expBall k r (UWb k r) ρ
  calc ν (tBall k r m ρ) = ν (lmulM m⁻¹ ⁻¹' bBall k r ρ) := rfl
    _ = (ν.map (lmulM m⁻¹)) (bBall k r ρ) := (Measure.map_apply (HU.lmulM_cont _).measurable hB).symm
    _ = ν (bBall k r ρ) := by rw [h.2.2.2 _ hinv]

end GE

open GE in

theorem gaugeExists_of (hH : HaarDens) (hL : ChartLim) : GaugeExists := by
  intro k r hk
  obtain ⟨νh, hνh, δ, hδc, hδ0, hδt, ε, hε, hball⟩ := hH k r hk
  set c : ℝ≥0 := ((δ 0).toNNReal)⁻¹ with hcdef
  have hc : c ≠ 0 := inv_ne_zero (ENNReal.toNNReal_pos hδ0 hδt).ne'
  have hg : IsHaarOn (UWb k r) (c • νh) := haarOn_smul _ _ c hc hνh
  have hup : ∀ᶠ x in 𝓝 (0 : lieE (UWb k r)), δ x < δ 0 + 1 :=
    hδc.eventually (gt_mem_nhds (ENNReal.lt_add_right hδt one_ne_zero))
  have hlo : ∀ᶠ x in 𝓝 (0 : lieE (UWb k r)), δ 0 / 2 < δ x :=
    hδc.eventually (lt_mem_nhds (ENNReal.half_lt_self hδ0 hδt))
  obtain ⟨ε', hε', hε'b⟩ := Metric.eventually_nhds_iff.mp (hup.and hlo)
  refine ⟨c • νh, hg, ⟨min ε ε', lt_min hε hε', fun ρ hρ hρε => ?_⟩, fun m hm => ?_⟩
  · have hρ1 : ρ < ε := hρε.trans_le (min_le_left _ _)
    have hρ2 : ρ < ε' := hρε.trans_le (min_le_right _ _)
    have hbd : ∀ x ∈ Metric.ball (0 : lieE (UWb k r)) ρ, δ x < δ 0 + 1 ∧ δ 0 / 2 < δ x :=
      fun x hx => hε'b ((Metric.mem_ball.mp hx).trans hρ2)
    have hmeas : MeasurableSet (Metric.ball (0 : lieE (UWb k r)) ρ) := measurableSet_ball
    have hvpos : 0 < volume (Metric.ball (0 : lieE (UWb k r)) ρ) := Metric.measure_ball_pos _ _ hρ
    have hvfin : volume (Metric.ball (0 : lieE (UWb k r)) ρ) < ⊤ := measure_ball_lt_top
    have hI : νh (bBall k r ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x := hball ρ hρ hρ1
    have hlow : δ 0 / 2 * volume (Metric.ball (0 : lieE (UWb k r)) ρ) ≤ νh (bBall k r ρ) := by
      rw [hI, ← setLIntegral_const]
      exact setLIntegral_mono' hmeas fun x hx => (hbd x hx).2.le
    have hhigh : νh (bBall k r ρ) ≤ (δ 0 + 1) * volume (Metric.ball (0 : lieE (UWb k r)) ρ) := by
      rw [hI, ← setLIntegral_const]
      exact setLIntegral_mono' hmeas fun x hx => (hbd x hx).1.le
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    constructor
    · exact ENNReal.mul_pos (by exact_mod_cast hc)
        (lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.half_pos hδ0).ne' hvpos.ne') hlow).ne'
    · exact ENNReal.mul_lt_top ENNReal.coe_lt_top
        (lt_of_le_of_lt hhigh (ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨hδt.lt_top, ENNReal.one_lt_top⟩) hvfin))
  · have := lie_nontrivial (k := k) (r := r)
    have hlim := hL (lieE (UWb k r)) (Mt k r) (expC k r) νh δ hδc hδt
      ⟨ε, hε, fun ρ h1 h2 => by rw [← bBall_eq]; exact hball ρ h1 h2⟩
    have key : (fun ρ : ℝ => ((c • νh) (tBall k r m ρ)).toReal / bVol k r ρ) = fun ρ => (c : ℝ) *
        ((νh (expC k r '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal) := by
      funext ρ
      rw [tBall_mass _ hg m hm ρ, Measure.smul_apply, ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul, bBall_eq,
        bVol, mul_div_assoc]
    have h1 : (c : ℝ) * (δ 0).toReal = 1 := by
      rw [hcdef, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
      exact inv_mul_cancel₀ (ENNReal.toReal_pos hδ0 hδt).ne'
    rw [key]
    have h2 := hlim.const_mul (c : ℝ)
    rwa [h1] at h2

theorem gaugeExists_of_dens (hH : HaarDens) : GaugeExists := gaugeExists_of hH chartLim

end PI.RhsWLim.W
