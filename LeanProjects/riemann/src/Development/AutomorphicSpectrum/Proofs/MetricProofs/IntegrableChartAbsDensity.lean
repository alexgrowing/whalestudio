import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog

open Set GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open scoped ENNReal

variable {n : ℕ}

def graphHom (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin n) ℂ) (fun i => X i) f)

theorem graphHom_castSucc (f : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom f (X i.castSucc) = X i := by
  simp [graphHom]

theorem graphHom_last (f : MvPolynomial (Fin n) ℂ) : graphHom f (X (Fin.last n)) = f := by
  simp [graphHom]

theorem graphHom_surjective (f : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom f) := by
  intro q
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨C a, by simp [graphHom]⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨a * X i.castSucc, by rw [map_mul, graphHom_castSucc]⟩

theorem eval_graphHom (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval x (graphHom f q) =
      eval (Fin.snoc (α := fun _ => ℂ) x (eval x f)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    induction i using Fin.lastCases with
    | last => simp [graphHom_last]
    | cast i => simp [graphHom_castSucc]

def graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
  RingHom.ker ((Ideal.Quotient.mk J).comp (graphHom f).toRingHom)

theorem graphIdeal_surjective (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (graphHom f).toRingHom) :=
  (Ideal.Quotient.mk_surjective).comp (graphHom_surjective f)

theorem graphIdeal_isPrime {J : Ideal (MvPolynomial (Fin n) ℂ)} (f : MvPolynomial (Fin n) ℂ)
    (hJ : J.IsPrime) : (graphIdeal J f).IsPrime := by
  haveI := hJ
  exact RingHom.ker_isPrime _

theorem graphIdeal_dim (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J f) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
  ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (graphIdeal_surjective J f))

theorem linForm_last : linForm (Pi.single (Fin.last n) (1 : ℂ)) =
    (X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℂ) := by
  unfold linForm
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem linForm_last_not_mem {J : Ideal (MvPolynomial (Fin n) ℂ)} {f : MvPolynomial (Fin n) ℂ}
    (hf : f ∉ J) : linForm (Pi.single (Fin.last n) (1 : ℂ)) ∉ graphIdeal J f := by
  rw [linForm_last]
  intro h
  apply hf
  have : (Ideal.Quotient.mk J) (graphHom f (X (Fin.last n))) = 0 := h
  rw [graphHom_last] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

def dropLast (w : EuclideanSpace ℂ (Fin (n + 1))) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i => w i.castSucc

def addLast (z : EuclideanSpace ℂ (Fin n)) (t : ℂ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (fun i => z i) t)

theorem dropLast_addLast (z : EuclideanSpace ℂ (Fin n)) (t : ℂ) : dropLast (addLast z t) = z := by
  ext i
  simp [dropLast, addLast]

theorem norm_sq_addLast (z : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    ‖addLast z t‖ ^ 2 = ‖z‖ ^ 2 + ‖t‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [addLast]

theorem lipschitz_dropLast : LipschitzWith 1 (dropLast (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, NNReal.coe_one, one_mul]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_castSucc]
  have : 0 ≤ dist (a (Fin.last n)) (b (Fin.last n)) ^ 2 := by positivity
  simpa [dropLast] using this

theorem slab_bound (d : ℕ) {J : Ideal (MvPolynomial (Fin n) ℂ)} (f : MvPolynomial (Fin n) ℂ) (R : ℝ)
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hf : f ∉ J) :
    ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩
        {z | ‖eval (fun i => z i) f‖ ≤ ε}) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, α, hα, hC⟩ := VarSlabMeasure.full (n + 1) d (graphIdeal J f)
    (Pi.single (Fin.last n) (1 : ℂ)) (R + 1) (graphIdeal_isPrime f hJ)
    ((graphIdeal_dim J f).trans hdim) (linForm_last_not_mem hf)
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  refine le_trans ?_ (hC ε hε hε1)
  have hsub : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖eval (fun i => z i) f‖ ≤ ε} ⊆
      dropLast '' (zeroSetEuc (graphIdeal J f) ∩ {w | ‖w‖ ≤ R + 1} ∩
        {w | ‖∑ j, (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) j * w j‖ ≤ ε}) := by
    rintro z ⟨⟨hzJ, hzR⟩, hzf⟩
    have hzR' : ‖z‖ ≤ R := hzR
    have hzf' : ‖eval (fun i => z i) f‖ ≤ ε := hzf
    refine ⟨addLast z (eval (fun i => z i) f), ⟨⟨?_, ?_⟩, ?_⟩, dropLast_addLast _ _⟩
    · intro q hq
      have h1 : graphHom f q ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hq
      have h2 := eval_graphHom f (fun i => z i) q
      rw [hzJ _ h1] at h2
      exact h2.symm
    · have h0 : 0 ≤ R := (norm_nonneg z).trans hzR'
      have h1 := norm_sq_addLast z (eval (fun i => z i) f)
      have h2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR' 2
      have h3 : ‖eval (fun i => z i) f‖ ^ 2 ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (hzf'.trans hε1)
      show ‖addLast z (eval (fun i => z i) f)‖ ≤ R + 1
      refine abs_le_of_sq_le_sq' ?_ (by linarith) |>.2
      nlinarith
    · show ‖∑ j, (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) j * _‖ ≤ ε
      rw [Finset.sum_eq_single (Fin.last n)]
      · simpa [addLast] using hzf'
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
  refine (measure_mono hsub).trans ?_
  have := lipschitz_dropLast.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity)
    (zeroSetEuc (graphIdeal J f) ∩ {w | ‖w‖ ≤ R + 1} ∩
        {w | ‖∑ j, (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) j * w j‖ ≤ ε})
  simpa using this

theorem bounded_part_finite (d : ℕ) {J : Ideal (MvPolynomial (Fin n) ℂ)} (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ {z | ‖z‖ ≤ R}) < ⊤ := by
  have hsub : zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} ⊆
      zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  exact (measure_mono hsub).trans_lt (HilbertSamuel.Closed.MassFinite n d J hJ hdim (R + 1))

theorem lintegral_lt_top (d : ℕ) {J : Ideal (MvPolynomial (Fin n) ℂ)} (f : MvPolynomial (Fin n) ℂ)
    (R : ℝ) (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hf : f ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖eval (fun i => z i) f‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := slab_bound d f R hJ hdim hf
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ := bounded_part_finite d R hJ hdim
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => eval (fun i => z i) f :=
    (MvPolynomial.continuous_eval f).comp (PiLp.continuous_ofLp 2 _)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖eval (fun i => z i) f‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
    hcont.continuousOn
  set M : ℝ := max B 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((hB z ?_).trans (le_max_left _ _))
    rw [mem_closedBall_zero_iff]
    exact hz.2

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖eval (fun i => z i) f‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (eval (fun i => z i) f)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right B 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

theorem integrable_chartAbsDens_log :
    ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R C : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A → f ∉ J →
    (∀ i, GroundTheory.Heights₂.Heights.SmoothNear (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (φ i)) →
    Integrable (chartAbsDens J A
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x f‖| + C) φ) := by
  intro n d J A f φ R C hJ hdim hA hf hφ
  have hcont : Continuous fun x : Fin n → ℂ => eval x f := MvPolynomial.continuous_eval f
  have hgm : Measurable fun x : Fin n → ℂ => |Real.log ‖eval x f‖| + C :=
    ((Real.measurable_log.comp hcont.norm.measurable).abs).add_const C
  refine ⟨(SheetSumMeasurable.proof n d J A _ φ hJ hdim hA
    (hgm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable, ?_⟩
  obtain ⟨K, hK, hDK⟩ := HilbertSamuel.Closed.ChartMassCompare n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hgm).trans_lt (ENNReal.mul_lt_top hK ?_)
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ L * R} with hSdef
  have hsub : zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) |
      WithLp.ofLp z ∈ Metric.closedBall (0 : Fin n → ℂ) R} ⊆ S := by
    rintro z ⟨hz, hzB⟩
    refine ⟨hz, ?_⟩
    have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
    exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ := bounded_part_finite d (L * R) hJ hdim
  have hlog := lintegral_lt_top d f (L * R) hJ hdim hf
  have hcontE : Continuous fun z : EuclideanSpace ℂ (Fin n) => eval (fun i => z i) f :=
    (MvPolynomial.continuous_eval f).comp (PiLp.continuous_ofLp 2 _)
  have hFm : Measurable fun z : EuclideanSpace ℂ (Fin n) => Real.log ‖eval (fun i => z i) f‖ :=
    Real.measurable_log.comp hcontE.norm.measurable
  have hle : ∀ z : EuclideanSpace ℂ (Fin n),
      ‖|Real.log ‖eval (WithLp.ofLp z) f‖| + C‖ₑ ≤
        ‖Real.log ‖eval (fun i => z i) f‖‖ₑ + ‖C‖ₑ := by
    intro z
    refine (enorm_add_le _ _).trans ?_
    have : ‖|Real.log ‖eval (WithLp.ofLp z) f‖|‖ₑ = ‖Real.log ‖eval (fun i => z i) f‖‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]
    rw [this]
  refine lt_of_le_of_lt (lintegral_mono fun z => hle z) ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨hlog, ENNReal.mul_lt_top enorm_lt_top hSfin⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog

end
