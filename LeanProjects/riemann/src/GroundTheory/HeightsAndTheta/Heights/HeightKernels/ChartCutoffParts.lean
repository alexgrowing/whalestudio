import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartCutoffEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyCocycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartIntegrationByPartsSymmetry

section Potentials

variable {e : ℕ}

theorem contDiff_gbPot_of_le {D : ℕ} (m : ℕ) : ContDiff ℝ m (gbPot (D := D)) := by
  have hs : ContDiff ℝ m fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2 :=
    contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))
  have hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2 := fun y => by positivity
  exact (hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'

theorem contDiff_hermChartPot_of_le (m : ℕ) {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ContDiff ℝ m (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact ((contDiff_gbPot_of_le m).comp
    (contDiff_const.add (ChartMongeAmpereAffineInvariance.realCLE P hP).contDiff)).add contDiff_const

theorem levi_eq_re (φ : (Fin e → ℂ) → ℝ) (z ξ : Fin e → ℂ) :
    levi φ z ξ = (star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ)).re := by
  have key : star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star (star ξ)) (star (star ξ)) := by
    simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
    exact sum_mul_leviC _ _ _
  rw [key, star_star]
  simp [leviC, levi]

theorem levi_hermChartPot_nonneg {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (z ξ : Fin e → ℂ) :
    0 ≤ levi (hermChartPot M) z ξ := by
  obtain ⟨C, hC⟩ := ChartHessCompare.proof HermFormCompare.proof e M M hM hM
  have hp : (hessC (hermChartPot M) z).PosSemidef := (hC z).1.posSemidef
  rw [levi_eq_re]
  exact (Complex.nonneg_iff.mp (hp.dotProduct_mulVec_nonneg (star ξ))).1

end Potentials

section Cutoff

variable {D : ℕ}

theorem chartCutoff_apply (k : ℕ) (y : Fin D → ℂ) :
    chartCutoff k y = Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2) := rfl

theorem contDiff_chartCutoff (k : ℕ) (m : ℕ) : ContDiff ℝ m (chartCutoff (D := D) k) := by
  have hs : ContDiff ℝ m fun y : Fin D → ℂ => ∑ i, ‖y i‖ ^ 2 :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub (hs.div_const _))

theorem chartCutoff_nonneg (k : ℕ) (y : Fin D → ℂ) : 0 ≤ chartCutoff k y := Real.smoothTransition.nonneg _

theorem chartCutoff_le_one (k : ℕ) (y : Fin D → ℂ) : chartCutoff k y ≤ 1 := Real.smoothTransition.le_one _

theorem chartCutoff_eq_one {k : ℕ} {y : Fin D → ℂ} (h : ∑ i, ‖y i‖ ^ 2 ≤ ((k : ℝ) + 1) ^ 2) :
    chartCutoff k y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have : (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2 ≤ 1 := (div_le_one hk).mpr h
  linarith

theorem chartCutoff_eq_zero {k : ℕ} {y : Fin D → ℂ} (h : 2 * ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2) :
    chartCutoff k y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have : 2 ≤ (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2 := (le_div_iff₀ hk).mpr h
  linarith

theorem chartCutoff_mono (y : Fin D → ℂ) : Monotone fun k : ℕ => chartCutoff k y := by
  intro a b hab
  simp only [chartCutoff_apply]
  apply Real.smoothTransition.monotone
  have hab' : ((a : ℝ) + 1) ^ 2 ≤ ((b : ℝ) + 1) ^ 2 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    gcongr
  have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
  have := div_le_div_of_nonneg_left hs (by positivity) hab'
  linarith

theorem tendsto_chartCutoff (y : Fin D → ℂ) : Tendsto (fun k : ℕ => chartCutoff k y) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.sqrt (∑ i, ‖y i‖ ^ 2))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  apply chartCutoff_eq_one
  have h0 : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
  have hs : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc ∑ i, ‖y i‖ ^ 2 = Real.sqrt (∑ i, ‖y i‖ ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2

theorem hasCompactSupport_chartCutoff (k : ℕ) : HasCompactSupport (chartCutoff (D := D) k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) (2 * ((k : ℝ) + 1))) fun y hy => ?_
  apply chartCutoff_eq_zero
  have hr : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hy
  simp only [not_forall, not_le] at hy
  obtain ⟨i, hi⟩ := hy
  have h1 : ‖y i‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : (2 * ((k : ℝ) + 1)) ^ 2 ≤ ‖y i‖ ^ 2 := pow_le_pow_left₀ hr hi.le 2
  nlinarith [sq_nonneg ((k : ℝ) + 1)]

theorem fderiv_chartCutoff_eq_zero {k : ℕ} {y : Fin D → ℂ} (h : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2) :
    fderiv ℝ (chartCutoff k) y = 0 := by
  have hc : Continuous fun z : Fin D → ℂ => ∑ i, ‖z i‖ ^ 2 := by fun_prop
  have hopen : IsOpen {z : Fin D → ℂ | ∑ i, ‖z i‖ ^ 2 < ((k : ℝ) + 1) ^ 2} := isOpen_lt hc continuous_const
  have hev : chartCutoff k =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with z hz
    exact chartCutoff_eq_one (le_of_lt hz)
  rw [hev.fderiv_eq]
  simp

end Cutoff

section GradDens

variable {D : ℕ}

theorem gradMat_eq_zero_left {v w : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : fderiv ℝ v z = 0) :
    gradMat v w z = 0 := by
  ext j k
  simp [gradMat, dz_cplx, h]

theorem gradDens_eq_zero_of_gradMat {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {v w : (Fin (n + 1) → ℂ) → ℝ}
    {z : Fin (n + 1) → ℂ} (h : gradMat v w z = 0) : gradDens φ v w z = 0 := by
  have h0 := mdisc_cons_smul_fst (0 : ℂ) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) fun i => hessC (φ i) z
  simp only [smul_zero, zero_mul] at h0
  simp [gradDens, h, h0]

theorem gradDens_chartCutoff_left {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : (Fin (n + 1) → ℂ) → ℝ)
    {k : ℕ} {y : Fin (n + 1) → ℂ} (h : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2) :
    gradDens φ (chartCutoff k) w y = 0 :=
  gradDens_eq_zero_of_gradMat (gradMat_eq_zero_left (fderiv_chartCutoff_eq_zero h))

theorem continuous_mdisc {X : Type*} [TopologicalSpace X] {F : X → Fin D → Matrix (Fin D) (Fin D) ℂ}
    (hF : ∀ k, Continuous fun x => F x k) : Continuous fun x => mdisc (F x) := by
  unfold mdisc
  refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
  exact (continuous_finsetSum _ fun k _ => hF k).matrix_det

theorem continuous_hessC {φ : (Fin D → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (hessC φ) := by
  have h1 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hH : ∀ a b : Fin D → ℂ, Continuous fun z => fderiv ℝ (fderiv ℝ φ) z a b := fun a b =>
    (h1.clm_apply continuous_const).clm_apply continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((Complex.continuous_ofReal.comp ((hH _ _).add (hH _ _))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp ((hH _ _).sub (hH _ _))))).div_const _

theorem continuous_gradMat {v w : (Fin D → ℂ) → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    Continuous (gradMat v w) := by
  have hv' : ∀ a, Continuous fun z => fderiv ℝ v z a := fun a =>
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hw' : ∀ a, Continuous fun z => fderiv ℝ w z a := fun a =>
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [gradMat, dz_cplx, dzb_cplx]
  exact (((Complex.continuous_ofReal.comp (hv' _)).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp (hv' _)))).div_const 2).mul
    (((Complex.continuous_ofReal.comp (hw' _)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (hw' _)))).div_const 2)

theorem continuous_gradDens {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {v w : (Fin (n + 1) → ℂ) → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    Continuous (gradDens φ v w) := by
  unfold gradDens
  refine continuous_const.mul (Complex.continuous_re.comp (continuous_mdisc fun k => ?_))
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using continuous_gradMat hv hw
  · simpa using continuous_hessC (hφ i)

theorem hasCompactSupport_gradDens_left {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {v : (Fin (n + 1) → ℂ) → ℝ} (w : (Fin (n + 1) → ℂ) → ℝ) (hv : HasCompactSupport v) :
    HasCompactSupport (gradDens φ v w) := by
  refine (hv.fderiv (𝕜 := ℝ)).mono fun z hz => ?_
  rw [Function.mem_support] at hz ⊢
  exact fun h0 => hz (gradDens_eq_zero_of_gradMat (gradMat_eq_zero_left h0))

theorem parts_cutoff {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {ψ u w : (Fin (n + 1) → ℂ) → ℝ} (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (hu : ContDiff ℝ 3 u) (hw : ContDiff ℝ 3 w) :
    Integrable (fun y => ψ y * u y * maDens (Fin.cons w φ) y) ∧
      Integrable (fun y => ψ y * gradDens φ u w y) ∧
      Integrable (fun y => u y * gradDens φ ψ w y) ∧
      ∫ y, ψ y * u y * maDens (Fin.cons w φ) y =
        -(∫ y, ψ y * gradDens φ u w y) - ∫ y, u y * gradDens φ ψ w y := by
  have hv : ContDiff ℝ 3 (fun y => ψ y * u y) := hψ.mul hu
  have hvc : HasCompactSupport (fun y => ψ y * u y) := hψc.mul_right
  have hyp : PartsHyp φ (fun y => ψ y * u y) w Set.univ :=
    ⟨isOpen_univ, hv.contDiffOn, hvc, Set.subset_univ _, hw.contDiffOn, fun i => (hφ i).contDiffOn⟩
  obtain ⟨h1, -, -, h4, -⟩ := parts_thm n φ _ w Set.univ hyp
  have h21 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => (hφ i).of_le (by norm_num)
  have hone : ((1 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hg1 : Integrable (fun y => ψ y * gradDens φ u w y) :=
    (hψ.continuous.mul (continuous_gradDens h21 (hu.of_le hone) (hw.of_le hone))).integrable_of_hasCompactSupport
      hψc.mul_right
  have hg2 : Integrable (fun y => u y * gradDens φ ψ w y) :=
    (hu.continuous.mul (continuous_gradDens h21 (hψ.of_le hone) (hw.of_le hone))).integrable_of_hasCompactSupport
      (hasCompactSupport_gradDens_left φ w hψc).mul_left
  refine ⟨?_, hg1, hg2, ?_⟩
  · simpa [IntegrableOn, Measure.restrict_univ] using h1
  · have hL : ∀ y, gradDens φ (fun y => ψ y * u y) w y = ψ y * gradDens φ u w y + u y * gradDens φ ψ w y :=
      fun y => (gradDensLeibniz_thm n φ ψ u w y (hψ.differentiable (by norm_num) y)
        (hu.differentiable (by norm_num) y)).1
    have h4' : ∫ y, ψ y * u y * maDens (Fin.cons w φ) y = -∫ y, gradDens φ (fun y => ψ y * u y) w y := by
      simpa [maInt, gradInt, Measure.restrict_univ] using h4
    rw [h4']
    simp_rw [hL]
    rw [integral_add hg1 hg2]
    ring

end GradDens

section Chart

variable {n : ℕ}

theorem gradDens_chart_comm {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v w : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    gradDens (fun i => hermChartPot (T i)) v w y = gradDens (fun i => hermChartPot (T i)) w v y :=
  gradDensSymm_thm n _ v w Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn) y
    (Set.mem_univ _)

theorem gradDens_chart_nonneg {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    0 ≤ gradDens (fun i => hermChartPot (T i)) v v y :=
  gradDensNonneg_thm n _ v Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn)
    (fun i z _ ξ => levi_hermChartPot_nonneg (hT i) z ξ) y (Set.mem_univ _)

theorem abs_gradDens_chart_le {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v w : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    |gradDens (fun i => hermChartPot (T i)) v w y| ≤
      Real.sqrt (gradDens (fun i => hermChartPot (T i)) v v y) *
        Real.sqrt (gradDens (fun i => hermChartPot (T i)) w w y) := by
  have hcs := gradDensCauchySchwarz_thm n (fun i => hermChartPot (T i)) v w Set.univ isOpen_univ
    (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn)
    (fun i z _ ξ => levi_hermChartPot_nonneg (hT i) z ξ) y (Set.mem_univ _)
  rw [← Real.sqrt_mul (gradDens_chart_nonneg hT v y)]
  exact Real.abs_le_sqrt hcs

theorem cons_hermChartPot (C : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) :
    (fun j => hermChartPot ((Fin.cons C T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j)) =
      (Fin.cons (hermChartPot C) fun i => hermChartPot (T i) : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

theorem hessC_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Fin D → ℂ) :
    hessC (fun y => f y - g y) z = hessC f z - hessC g z := by
  have h1 : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h2 : fderiv ℝ (fderiv ℝ fun y => f y - g y) z = fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ g) z := by
    rw [h1]
    exact fderiv_sub (hf1 z) (hg1 z)
  ext i j
  simp only [hessC, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem maDensity_cons_sub {f g : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDensity (Fin.cons (fun y => f y - g y) φ) z = maDensity (Fin.cons f φ) z - maDensity (Fin.cons g φ) z := by
  have hcons : ∀ h : (Fin (n + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons h φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
        (Fin.cons (hessC h z) fun i => hessC (φ i) z : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    intro h
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hsub : hessC (fun y => f y - g y) z = (1 : ℂ) • hessC f z + (-1 : ℂ) • hessC g z := by
    rw [hessC_sub hf hg z]
    simp [sub_eq_add_neg]
  have key := mdisc_cons_smul_add (1 : ℂ) (-1) (hessC f z) (hessC g z) fun i => hessC (φ i) z
  change ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc fun k => hessC ((Fin.cons (fun y => f y - g y) φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re =
    ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (mdisc fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re -
      ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (mdisc fun k => hessC ((Fin.cons g φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re
  rw [hcons, hcons, hcons, hsub, key]
  simp only [one_mul, neg_one_mul, Complex.add_re, Complex.neg_re]
  ring

theorem integrable_pot_mul_maDensity {A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ}
    {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (hD : D.PosDef) (hT : ∀ i, (T i).PosDef) :
    Integrable (fun y : Fin (n + 1) → ℂ => (hermChartPot A y - hermChartPot B y) *
      maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y') fun i => hermChartPot (T i)) y) := by
  have hs : ∀ X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef →
      ∀ j, ((Fin.cons X T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j).PosDef := by
    intro X hX j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hX
    · simpa using hT i
  have h1 := ChartEnergyCocycleAlt.integrable_pairing hA hB (hs C hC)
  have h2 := ChartEnergyCocycleAlt.integrable_pairing hA hB (hs D hD)
  refine (h1.sub h2).congr (Eventually.of_forall fun y => ?_)
  simp only [ChartEnergyCocycleAlt.dens, cons_hermChartPot]
  rw [maDensity_cons_sub (contDiff_hermChartPot_of_le 2 hC) (contDiff_hermChartPot_of_le 2 hD)]
  simp only [Pi.sub_apply]
  ring

end Chart

end ChartIntegrationByPartsSymmetry

end

end GroundTheory.Heights₂.Heights
