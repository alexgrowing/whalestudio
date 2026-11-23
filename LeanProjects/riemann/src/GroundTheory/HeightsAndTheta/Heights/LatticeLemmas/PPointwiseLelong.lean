import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ProbabilityTheory Real

noncomputable section

namespace PointwiseLelong

variable {N : ℕ}

theorem eval_smul {Q : MvPolynomial (Fin N) ℂ} {d : ℕ} (hQ : Q.IsHomogeneous d) (t : ℂ)
    (x : Fin N → ℂ) : eval (t • x) Q = t ^ d * eval x Q := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hQ.degree_eq_sum_deg_support hm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem differentiable_eval_line (Q : MvPolynomial (Fin N) ℂ) (v u : Fin N → ℂ) :
    Differentiable ℂ fun w : ℂ => eval (v + w • u) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact differentiable_const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hp.mul (by fun_prop)

theorem log_norm_le_circleAverage {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0) :
    Real.log ‖g 0‖ ≤ circleAverage (fun z => Real.log ‖g z‖) 0 1 := by
  have han : AnalyticOnNhd ℂ g (Metric.closedBall 0 |1|) := fun z _ => hg.analyticAt z
  rw [han.circleAverage_log_norm one_ne_zero h0]
  refine le_add_of_nonneg_left (finsum_nonneg fun u => ?_)
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |1|
  · refine mul_nonneg (by exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u) ?_
    rw [one_mul, zero_sub, norm_neg, Real.log_inv]
    refine neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) ?_)
    simpa using hu
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
    simp

theorem integral_phaseLaw (f : ℝ → ℝ) :
    ∫ θ, f θ ∂phaseLaw = (2 * π)⁻¹ * ∫ θ in -π..π, f θ := by
  rw [phaseLaw, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ioc,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul]
  congr 2
  ring

theorem phase_bound {Q : MvPolynomial (Fin N) ℂ} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (p t : Fin N → ℂ) (hp : eval p Q ≠ 0) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    Real.log ‖eval p Q‖ + d * Real.log r ≤
      ∫ θ, Real.log ‖eval (((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t) Q‖ ∂phaseLaw := by
  set g : ℂ → ℂ := fun w => eval ((r : ℂ) • p + w • ((b : ℂ) • t)) Q with hg
  have hgd : Differentiable ℂ g := differentiable_eval_line Q _ _
  have hg0 : g 0 = (r : ℂ) ^ d * eval p Q := by
    simp only [hg, zero_smul, add_zero]
    exact eval_smul hQ _ _
  have hg0' : g 0 ≠ 0 := by
    rw [hg0]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hp
  have hlog0 : Real.log ‖g 0‖ = Real.log ‖eval p Q‖ + d * Real.log r := by
    rw [hg0, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.log_mul (pow_ne_zero _ hr.ne') (norm_ne_zero_iff.mpr hp), Real.log_pow]
    ring

  have hpt : ∀ θ : ℝ, Real.log ‖eval (((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t) Q‖ =
      Real.log ‖g (circleMap 0 1 (-θ))‖ := by
    intro θ
    have he : Complex.exp (θ * Complex.I) * Complex.exp ((-θ : ℝ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      push_cast
      simp
    have hv : ((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t =
        Complex.exp (θ * Complex.I) • ((r : ℂ) • p + Complex.exp ((-θ : ℝ) * Complex.I) • ((b : ℂ) • t)) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, he, one_mul, mul_comm (r : ℂ)]
    rw [hv, eval_smul hQ, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul]
    simp [hg, circleMap]
  have hper : Function.Periodic (fun θ => Real.log ‖g (circleMap 0 1 θ)‖) (2 * π) :=
    (periodic_circleMap 0 1).comp (fun z => Real.log ‖g z‖)
  have hint : ∫ θ in -π..π, Real.log ‖g (circleMap 0 1 (-θ))‖ =
      ∫ θ in (0 : ℝ)..2 * π, Real.log ‖g (circleMap 0 1 θ)‖ := by
    rw [intervalIntegral.integral_comp_neg (fun θ => Real.log ‖g (circleMap 0 1 θ)‖), neg_neg]
    have := hper.intervalIntegral_add_eq (-π) 0
    rwa [show -π + 2 * π = π by ring, zero_add] at this
  rw [← hlog0, integral_phaseLaw]
  simp_rw [hpt]
  rw [hint]
  have hJ := log_norm_le_circleAverage hgd hg0'
  rwa [circleAverage_def, smul_eq_mul] at hJ

theorem measurable_normalize :
    Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) => sphereNormalize (HermNorm.std N) 1 u (0, j) := by
  refine measurable_pi_lambda _ fun j => ?_
  exact ((Complex.measurable_ofReal.comp (LogInt.measurable_groupNorm _ 0)).inv).mul
    (measurable_pi_apply _)

theorem volume_sphereBall_ne_zero : volume (sphereBall (HermNorm.std N) 1) ≠ 0 :=
  (volume_ballProd_pos (HermNorm.std N) 1).ne'

theorem volume_sphereBall_ne_top : volume (sphereBall (HermNorm.std N) 1) ≠ ⊤ :=
  (volume_ballProd_lt_top (HermNorm.std N) 1).ne

theorem isProbabilityMeasure_phaseLaw : IsProbabilityMeasure phaseLaw :=
  cond_isProbabilityMeasure_of_finite (by simp [Real.pi_pos]) (by simp)

theorem isProbabilityMeasure_sphereLaw : IsProbabilityMeasure (sphereLaw N) := by
  have := cond_isProbabilityMeasure_of_finite (volume_sphereBall_ne_zero (N := N))
    volume_sphereBall_ne_top
  exact Measure.isProbabilityMeasure_map measurable_normalize.aemeasurable

theorem sphereMean_eq_integral {f : (Fin N → ℂ) → ℝ} (hf : Measurable f) :
    sphereMean (HermNorm.std N) 1 (fun u => f (fun j => u (0, j))) = ∫ z, f z ∂sphereLaw N := by
  rw [sphereLaw, integral_map measurable_normalize.aemeasurable hf.aestronglyMeasurable,
    sphereMean_eq, average, Measure.restrict_apply_univ]
  rfl

theorem integrable_sphereLaw {f : (Fin N → ℂ) → ℝ} (hf : Measurable f)
    (hi : SphereIntegrable (HermNorm.std N) 1 (fun u => f (fun j => u (0, j)))) :
    Integrable f (sphereLaw N) := by
  rw [sphereLaw, integrable_map_measure hf.aestronglyMeasurable measurable_normalize.aemeasurable]
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr volume_sphereBall_ne_zero)

theorem sphereIntegrable_log {Q : MvPolynomial (Fin N) ℂ} (hQ : Q ≠ 0) :
    SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) := by
  have hinj : Function.Injective (fun j : Fin N => ((0 : Fin 1), j)) :=
    fun a b h => (Prod.ext_iff.mp h).2
  have h0 : rename (fun j : Fin N => ((0 : Fin 1), j)) Q ≠ 0 := by
    intro h
    exact hQ (rename_injective _ hinj (by rw [h, map_zero]))
  have := (LogInt.integrableOn_log_mahler (HermNorm.std N) _ h0).1
  simp only [eval_rename, Function.comp_def] at this
  exact this

theorem sphereIntegrable_coord {p : Fin N → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖coordAlong p (fun j ↦ u (0, j))‖) := by
  have h : (∑ j, X ((0 : Fin 1), j) * C (star (p j)) : MvPolynomial (Fin 1 × Fin N) ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eval fun ij : Fin 1 × Fin N => p ij.2) h0
    simp only [map_sum, map_mul, eval_X, eval_C, map_zero] at this
    have hj : ∀ j, p j * star (p j) = ((‖p j‖ ^ 2 : ℝ) : ℂ) := fun j => by
      rw [Complex.star_def, Complex.mul_conj']
      push_cast
      ring
    simp_rw [hj] at this
    rw [← Complex.ofReal_sum, hp] at this
    simp at this
  have := (LogInt.integrableOn_log_mahler (HermNorm.std N) _ h).1
  simp only [map_sum, map_mul, eval_X, eval_C] at this
  exact this

theorem continuous_coordAlong (p : Fin N → ℂ) : Continuous (coordAlong p) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const

theorem measurable_orthoDir (p : Fin N → ℂ) : Measurable (orthoDir p) := by
  have hc : Continuous fun z => z - coordAlong p z • p :=
    continuous_id.sub ((continuous_coordAlong p).smul continuous_const)
  have hn : Continuous (HermNorm.std N).norm := (HermNorm.std N).li_continuous_norm
  exact ((Complex.measurable_ofReal.comp (hn.comp hc).measurable).inv).smul hc.measurable

def radialMap (p z : Fin N → ℂ) : ℝ × (Fin N → ℂ) := (‖coordAlong p z‖, orthoDir p z)

def polarMap (p z : Fin N → ℂ) : ℝ × (ℝ × (Fin N → ℂ)) :=
  (Complex.arg (coordAlong p z), radialMap p z)

def polarIntegrand (Q : MvPolynomial (Fin N) ℂ) (p : Fin N → ℂ) (x : ℝ × (ℝ × (Fin N → ℂ))) : ℝ :=
  Real.log ‖eval (((x.2.1 : ℂ) * Complex.exp (x.1 * Complex.I)) • p +
    ((√(1 - x.2.1 ^ 2) : ℝ) : ℂ) • x.2.2) Q‖

theorem measurable_radialMap (p : Fin N → ℂ) : Measurable (radialMap p) :=
  (continuous_norm.comp (continuous_coordAlong p)).measurable.prodMk (measurable_orthoDir p)

theorem measurable_polarMap (p : Fin N → ℂ) : Measurable (polarMap p) :=
  (Complex.measurable_arg.comp (continuous_coordAlong p).measurable).prodMk (measurable_radialMap p)

theorem measurable_polarIntegrand (Q : MvPolynomial (Fin N) ℂ) (p : Fin N → ℂ) :
    Measurable (polarIntegrand Q p) := by
  have hc : Continuous fun x : ℝ × (ℝ × (Fin N → ℂ)) =>
      ((x.2.1 : ℂ) * Complex.exp (x.1 * Complex.I)) • p + ((√(1 - x.2.1 ^ 2) : ℝ) : ℂ) • x.2.2 := by
    fun_prop
  exact Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval Q).comp hc)).measurable

theorem main_bound (h1 : SphereProjectionLaw.Statement) {d : ℕ} {Q : MvPolynomial (Fin N) ℂ}
    (hQ0 : Q ≠ 0) (hQ : Q.IsHomogeneous d) (p : Fin N → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hQp : eval p Q ≠ 0) :
    Real.log ‖eval p Q‖ - d * (harmonic (N - 1) : ℝ) / 2 ≤
      sphereMean (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) := by
  have := isProbabilityMeasure_sphereLaw (N := N)
  have := isProbabilityMeasure_phaseLaw
  have hF : Measurable fun z : Fin N → ℂ => Real.log ‖eval z Q‖ :=
    Real.measurable_log.comp (continuous_norm.comp (MvPolynomial.continuous_eval Q)).measurable
  have hFi : Integrable (fun z => Real.log ‖eval z Q‖) (sphereLaw N) :=
    integrable_sphereLaw hF (sphereIntegrable_log hQ0)
  rw [sphereMean_eq_integral hF]
  obtain ⟨hN1, hN2⟩ := h1 N p hp
  rcases Nat.lt_or_ge N 2 with hN | hN
  ·
    obtain rfl : N = 1 := by
      rcases N with _ | _ | N
      · simp at hp
      · rfl
      · omega
    have hp' : ‖p 0‖ ^ 2 = 1 := by simpa using hp
    have hae : ∀ᵐ z ∂sphereLaw 1, Real.log ‖eval z Q‖ = Real.log ‖eval p Q‖ := by
      filter_upwards [hN1 rfl] with z hz
      have hpp : star (p 0) * p 0 = 1 := by
        rw [Complex.star_def, Complex.conj_mul']
        exact_mod_cast hp'
      have hzp : z = coordAlong p z • p := by
        funext i
        rw [Subsingleton.elim i 0]
        simp only [coordAlong, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
        calc z 0 = z 0 * (star (p 0) * p 0) := by rw [hpp, mul_one]
          _ = _ := by ring
      rw [hzp, eval_smul hQ, norm_mul, norm_pow, hz, one_pow, one_mul]
    rw [integral_congr_ae hae, integral_const]
    simp
  · obtain ⟨hdec, hprod, hsq⟩ := hN2 hN
    have hρ := measurable_radialMap p
    have hψ := measurable_polarMap p
    have hG := measurable_polarIntegrand Q p
    have : IsProbabilityMeasure ((sphereLaw N).map (radialMap p)) :=
      Measure.isProbabilityMeasure_map hρ.aemeasurable
    have hmap : (sphereLaw N).map (polarMap p) = phaseLaw.prod ((sphereLaw N).map (radialMap p)) :=
      hprod

    have hae : (fun z => Real.log ‖eval z Q‖) =ᵐ[sphereLaw N] fun z => polarIntegrand Q p (polarMap p z) := by
      filter_upwards [hdec] with z hz
      simp only [polarIntegrand, polarMap, radialMap, Complex.norm_mul_exp_arg_mul_I]
      rw [← hz.1]
    have hGi : Integrable (polarIntegrand Q p) (phaseLaw.prod ((sphereLaw N).map (radialMap p))) := by
      rw [← hmap, integrable_map_measure hG.aestronglyMeasurable hψ.aemeasurable]
      exact hFi.congr hae
    have hint : ∫ z, Real.log ‖eval z Q‖ ∂sphereLaw N =
        ∫ y, ∫ θ, polarIntegrand Q p (θ, y) ∂phaseLaw ∂((sphereLaw N).map (radialMap p)) := by
      rw [integral_congr_ae hae, ← integral_map hψ.aemeasurable hG.aestronglyMeasurable, hmap,
        integral_prod_symm _ hGi]

    have hpos : ∀ᵐ y ∂((sphereLaw N).map (radialMap p)), 0 < y.1 := by
      have hsqm : Measurable fun z => ‖coordAlong p z‖ ^ 2 :=
        ((continuous_norm.comp (continuous_coordAlong p)).pow 2).measurable
      have h0 : ∀ᵐ x ∂((sphereLaw N).map fun z => ‖coordAlong p z‖ ^ 2), x ≠ 0 := by
        rw [hsq]
        refine (withDensity_absolutelyContinuous _ _).ae_le (?_ : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0)
        rw [ae_iff]
        simp
      have h0' := ae_of_ae_map hsqm.aemeasurable h0
      rw [ae_map_iff hρ.aemeasurable (measurableSet_lt measurable_const measurable_fst)]
      filter_upwards [h0'] with z hz
      have h2 : 0 ≤ ‖coordAlong p z‖ := norm_nonneg _
      show 0 < ‖coordAlong p z‖
      refine lt_of_le_of_ne h2 fun h => hz ?_
      rw [← h]
      simp
    have hlow : ∀ᵐ y ∂((sphereLaw N).map (radialMap p)),
        Real.log ‖eval p Q‖ + d * Real.log y.1 ≤ ∫ θ, polarIntegrand Q p (θ, y) ∂phaseLaw := by
      filter_upwards [hpos] with y hy
      have := phase_bound hQ p y.2 hQp hy (√(1 - y.1 ^ 2))
      simp only [polarIntegrand]
      exact this

    have hmc : Measurable fun z => Real.log ‖coordAlong p z‖ :=
      Real.measurable_log.comp (continuous_norm.comp (continuous_coordAlong p)).measurable
    have hml : Measurable fun y : ℝ × (Fin N → ℂ) => Real.log y.1 :=
      Real.measurable_log.comp measurable_fst
    have hlogν : Integrable (fun y : ℝ × (Fin N → ℂ) => Real.log y.1) ((sphereLaw N).map (radialMap p)) := by
      rw [integrable_map_measure hml.aestronglyMeasurable hρ.aemeasurable]
      exact integrable_sphereLaw hmc (sphereIntegrable_coord hp)
    have hmean : ∫ y, Real.log y.1 ∂((sphereLaw N).map (radialMap p)) = -(harmonic (N - 1) : ℝ) / 2 := by
      rw [integral_map hρ.aemeasurable hml.aestronglyMeasurable]
      exact (sphereMean_eq_integral hmc).symm.trans (sphereMeanLinear N p hp)
    rw [hint]
    calc Real.log ‖eval p Q‖ - d * (harmonic (N - 1) : ℝ) / 2
        = ∫ y, (Real.log ‖eval p Q‖ + d * Real.log y.1) ∂((sphereLaw N).map (radialMap p)) := by
          rw [integral_add (integrable_const _) (hlogν.const_mul _), integral_const,
            integral_const_mul, hmean]
          simp
          ring
      _ ≤ _ := integral_mono_ae ((integrable_const _).add (hlogν.const_mul _))
          hGi.integral_prod_right hlow

theorem exists_max (hN : 1 ≤ N) (Q : MvPolynomial (Fin N) ℂ) :
    ∃ p : Fin N → ℂ, ∑ j, ‖p j‖ ^ 2 = 1 ∧
      ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖eval z Q‖ ≤ ‖eval p Q‖ := by
  let S := {z : Fin N → ℂ | ∑ j, ‖z j‖ ^ 2 = 1}
  have hcont : Continuous fun z : Fin N → ℂ => ∑ j, ‖z j‖ ^ 2 := by fun_prop
  have hcl : IsClosed S := isClosed_eq hcont continuous_const
  have hb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin N → ℂ)) (r := 1)).subset fun z hz => ?_
    have hz' : ∑ j, ‖z j‖ ^ 2 = 1 := hz
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    have hj : ‖z j‖ ^ 2 ≤ 1 := by
      rw [← hz']
      exact Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun i _ => sq_nonneg ‖z i‖)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (z j)]
  have hne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hN⟩ 1, ?_⟩
    show ∑ j, ‖(Pi.single ⟨0, hN⟩ (1 : ℂ) : Fin N → ℂ) j‖ ^ 2 = 1
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [hj]) (by simp)]
    simp
  obtain ⟨p, hpS, hmax⟩ := (Metric.isCompact_of_isClosed_isBounded hcl hb).exists_isMaxOn hne
    (continuous_norm.comp (MvPolynomial.continuous_eval Q)).continuousOn
  exact ⟨p, hpS, fun z hz => isMaxOn_iff.mp hmax z hz⟩

theorem eval_ne_zero_of_max {d : ℕ} {Q : MvPolynomial (Fin N) ℂ} (hQ0 : Q ≠ 0)
    (hQ : Q.IsHomogeneous d) {p : Fin N → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hmax : ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖eval z Q‖ ≤ ‖eval p Q‖) : eval p Q ≠ 0 := by
  intro hzero
  have hS : ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → eval z Q = 0 := fun z hz => by
    have := hmax z hz
    rw [hzero, norm_zero] at this
    exact norm_le_zero_iff.mp this
  apply hQ0
  apply hQ.eq_zero_of_forall_eval_eq_zero
  intro x
  by_cases hx : x = 0
  · subst hx
    have := eval_smul hQ 0 p
    rw [zero_smul, hS p hp, mul_zero] at this
    exact this
  · have hT : 0 < ∑ j, ‖x j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
      exact Finset.sum_pos' (fun i _ => sq_nonneg _)
        ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr (by simpa using hj)) 2⟩
    have hρ : 0 < √(∑ j, ‖x j‖ ^ 2) := Real.sqrt_pos.mpr hT
    have hsq : √(∑ j, ‖x j‖ ^ 2) ^ 2 = ∑ j, ‖x j‖ ^ 2 := Real.sq_sqrt hT.le
    have hs : ∑ j, ‖((((√(∑ i, ‖x i‖ ^ 2))⁻¹ : ℝ) : ℂ) • x) j‖ ^ 2 = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow,
        ← Finset.mul_sum]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hρ.le), inv_pow, hsq, inv_mul_cancel₀ hT.ne']
    have hxe : x = ((√(∑ j, ‖x j‖ ^ 2) : ℝ) : ℂ) • ((((√(∑ j, ‖x j‖ ^ 2))⁻¹ : ℝ) : ℂ) • x) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hρ.ne', Complex.ofReal_one, one_smul]
    rw [hxe, eval_smul hQ, hS _ hs, mul_zero]

end PointwiseLelong

open PointwiseLelong in

theorem PointwiseLelong.proof (h1 : SphereProjectionLaw.Statement) : PointwiseLelong.Statement := by
  intro N d Q hQ0 hQ
  refine ⟨fun p hp hQp => ⟨sphereIntegrable_log hQ0, main_bound h1 hQ0 hQ p hp hQp⟩, fun hN => ?_⟩
  obtain ⟨p, hp, hmax⟩ := exists_max hN Q
  have hQp := eval_ne_zero_of_max hQ0 hQ hp hmax
  have hsup : (⨆ z : {z : Fin N → ℂ // ∑ j, ‖z j‖ ^ 2 = 1}, ‖eval (z : Fin N → ℂ) Q‖) =
      ‖eval p Q‖ := by
    have : Nonempty {z : Fin N → ℂ // ∑ j, ‖z j‖ ^ 2 = 1} := ⟨⟨p, hp⟩⟩
    exact le_antisymm (ciSup_le fun z => hmax z z.2)
      (le_ciSup_of_le ⟨‖eval p Q‖, by rintro _ ⟨z, rfl⟩; exact hmax z z.2⟩ ⟨p, hp⟩ le_rfl)
  rw [hsup]
  exact main_bound h1 hQ0 hQ p hp hQp

end

end GroundTheory.Heights₂.Heights
