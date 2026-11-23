import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartCutoffEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartCutoffEnergyAlt

def sqn {D : ℕ} (y : Fin D → ℂ) : ℝ := ∑ i, ‖y i‖ ^ 2

theorem sqn_nonneg {D : ℕ} (y : Fin D → ℂ) : 0 ≤ sqn y :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem sqn_smul {D : ℕ} (c : ℝ) (y : Fin D → ℂ) : sqn (c • y) = c ^ 2 * sqn y := by
  simp only [sqn, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem contDiff_sqn {D : ℕ} : ContDiff ℝ 1 (sqn (D := D)) := by
  unfold sqn
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℂ).comp (contDiff_apply ℝ ℂ i)

theorem chartCutoff_eq {D : ℕ} (k : ℕ) (y : Fin D → ℂ) :
    chartCutoff k y = Real.smoothTransition (2 - sqn y / ((k : ℝ) + 1) ^ 2) := rfl

theorem chartCutoff_zero_eq {D : ℕ} (y : Fin D → ℂ) :
    chartCutoff 0 y = Real.smoothTransition (2 - sqn y) := by
  rw [chartCutoff_eq]; norm_num

theorem chartCutoff_scale {D : ℕ} (k : ℕ) :
    (chartCutoff k : (Fin D → ℂ) → ℝ) = fun y => chartCutoff 0 (((k : ℝ) + 1)⁻¹ • y) := by
  funext y
  rw [chartCutoff_eq, chartCutoff_zero_eq, sqn_smul, inv_pow]
  congr 1
  ring

theorem contDiff_chartCutoff {D : ℕ} (k : ℕ) : ContDiff ℝ 1 (chartCutoff k : (Fin D → ℂ) → ℝ) := by
  have h : (chartCutoff k : (Fin D → ℂ) → ℝ) =
      fun y => Real.smoothTransition (2 - sqn y / ((k : ℝ) + 1) ^ 2) := rfl
  rw [h]
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_sqn.div_const _))

theorem fderiv_chartCutoff_zero_eq_zero {D : ℕ} {x : Fin D → ℂ} (hx : sqn x < 1) :
    fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) x = 0 := by
  have hev : (chartCutoff 0 : (Fin D → ℂ) → ℝ) =ᶠ[nhds x] fun _ => 1 := by
    filter_upwards [(contDiff_sqn.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds hx] with x' hx'
    rw [chartCutoff_zero_eq]
    exact Real.smoothTransition.one_of_one_le (by simp only [Set.mem_preimage, Set.mem_Iio] at hx'; linarith)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

theorem hasCompactSupport_chartCutoff_zero {D : ℕ} :
    HasCompactSupport (chartCutoff 0 : (Fin D → ℂ) → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 2) fun x hx => ?_
  rw [chartCutoff_zero_eq]
  apply Real.smoothTransition.zero_of_nonpos
  obtain ⟨i, hi⟩ : ∃ i, 2 < ‖x i‖ := by
    by_contra h
    push Not at h
    exact hx (mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr h))
  have : ‖x i‖ ^ 2 ≤ sqn x :=
    Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  nlinarith

theorem norm_fderiv_chartCutoff_le {D : ℕ} (k : ℕ) (y : Fin D → ℂ) :
    ‖fderiv ℝ (chartCutoff k : (Fin D → ℂ) → ℝ) y‖ ≤
      ((k : ℝ) + 1)⁻¹ * ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (((k : ℝ) + 1)⁻¹ • y)‖ := by
  rw [chartCutoff_scale k]
  set c : ℝ := ((k : ℝ) + 1)⁻¹ with hcdef
  have hc : 0 < c := by positivity
  have hd : DifferentiableAt ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (c • y) :=
    (contDiff_chartCutoff 0).differentiable (by norm_num) _
  have hL : HasFDerivAt (fun y : Fin D → ℂ => c • y) (c • ContinuousLinearMap.id ℝ (Fin D → ℂ)) y := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) y).const_smul c
  rw [show (fun y : Fin D → ℂ => chartCutoff 0 (c • y)) = chartCutoff 0 ∘ fun y => c • y from rfl,
    (hd.hasFDerivAt.comp y hL).fderiv]
  calc _ ≤ ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (c • y)‖ * ‖c • ContinuousLinearMap.id ℝ (Fin D → ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (c • y)‖ * c := by
        gcongr
        rw [norm_smul, Real.norm_of_nonneg hc.le]
        exact mul_le_of_le_one_right hc.le ContinuousLinearMap.norm_id_le
    _ = _ := mul_comm _ _

end ChartCutoffEnergyAlt

namespace ChartCutoffEnergyAlt

open ReciprocityTheory.AnForm.A

theorem fderiv_cplx {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z)
    (h : Fin D → ℂ) : fderiv ℝ (cplx v) z h = ((fderiv ℝ v z h : ℝ) : ℂ) := by
  have hc := (Complex.ofRealCLM.hasFDerivAt (x := v z)).comp z hv.hasFDerivAt
  rw [show cplx v = Complex.ofRealCLM ∘ v from rfl, hc.fderiv]
  rfl

theorem dzb_eq_star_dz {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z)
    (j : Fin D) : dzb j (cplx v) z = star (dz j (cplx v) z) := by
  simp only [dz, dzb, fderiv_cplx hv]
  apply Complex.ext <;> simp

theorem norm_dz_le {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z)
    (j : Fin D) : ‖dz j (cplx v) z‖ ≤ ‖fderiv ℝ v z‖ := by
  simp only [dz, fderiv_cplx hv]
  have h1 : ‖(Pi.single j (1 : ℂ) : Fin D → ℂ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have h2 : ‖(Complex.I • Pi.single j (1 : ℂ) : Fin D → ℂ)‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_I, one_mul]; exact h1
  have hn := norm_nonneg (fderiv ℝ v z)
  have b1 := ((fderiv ℝ v z).le_opNorm (Pi.single j 1)).trans (mul_le_of_le_one_right hn h1)
  have b2 := ((fderiv ℝ v z).le_opNorm (Complex.I • Pi.single j 1)).trans (mul_le_of_le_one_right hn h2)
  have ht := norm_sub_le ((fderiv ℝ v z (Pi.single j 1) : ℂ))
    (Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ))
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real] at ht
  rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
  linarith

theorem gradMat_eq {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z) :
    gradMat v v z = vecMulVec (fun j => dz j (cplx v) z) (star fun j => dz j (cplx v) z) := by
  ext j k
  simp only [gradMat, vecMulVec_apply, Pi.star_apply, dzb_eq_star_dz hv]

theorem posSemidef_sub_vecMulVec {D : ℕ} (a : Fin D → ℂ) :
    (((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - vecMulVec a (star a)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨(isHermitian_one.smul ?_).sub (posSemidef_vecMulVec_self_star a).1, fun x => ?_⟩
  · show star ((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) = ((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ)
    simp
  set w : ℂ := star a ⬝ᵥ x with hw
  have hform : star x ⬝ᵥ ((((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - vecMulVec a (star a)) *ᵥ x)
      = (((∑ j, ‖a j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, dotProduct_sub, dotProduct_smul,
      op_smul_eq_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h1 : star x ⬝ᵥ x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h2 : star x ⬝ᵥ a = star w := by
      simp only [hw, dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h1, h2, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hform]
  refine Complex.zero_le_real.mpr (sub_nonneg.mpr ?_)
  have hcs : ‖w‖ ≤ ∑ j, ‖a j‖ * ‖x j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Pi.star_apply]
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖x j‖)
  calc ‖w‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖x j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ ≤ _ := hcs2

theorem mdisc_cons_smul_one {n : ℕ} (l m : ℂ) :
    mdisc (Fin.cons (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (fun _ : Fin n => m • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = l * m ^ n := by
  obtain ⟨f, hf⟩ := exists_multilinearMap_eq_mdisc (D := n + 1)
  have h : (Fin.cons (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (fun _ : Fin n => m • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun i => (Fin.cons l (fun _ : Fin n => m) : Fin (n + 1) → ℂ) i • (fun _ => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [h, ← hf, f.map_smul_univ, hf, mdisc_const, det_one, Fin.prod_cons]
  simp

end ChartCutoffEnergyAlt

namespace ChartCutoffEnergyAlt

open ReciprocityTheory.AnForm.A

theorem hessC_eq_cxHessian {D : ℕ} (φ : (Fin D → ℂ) → ℝ) : hessC φ = cxHessian φ := rfl

theorem star_dotProduct_self_eq {D : ℕ} (x : Fin D → ℂ) : star x ⬝ᵥ x = ((sqn x : ℝ) : ℂ) := by
  simp only [sqn, dotProduct, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem hess_bound {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin e → ℂ, (hessC (hermChartPot M) y).PosSemidef ∧
      ((((C / (1 + sqn y)) : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) - hessC (hermChartPot M) y).PosSemidef := by
  obtain ⟨C0, hC0⟩ := ChartHessCompare.proof HermFormCompare.proof e M M hM hM
  obtain ⟨a, ha, hMa⟩ := HermFormCompare.proof (e + 1) M 1 hM PosDef.one
  obtain ⟨a', ha', haM⟩ := HermFormCompare.proof (e + 1) 1 M PosDef.one hM
  obtain ⟨B, hMB, hB⟩ := ChartDensityIntegrableAlt.exists_conjTranspose_mul_self hM
  refine ⟨a * a' / 2, by positivity, fun y => ⟨?_, ?_⟩⟩
  · rw [hessC_eq_cxHessian]; exact (hC0 y).1.posSemidef
  subst hMB
  rw [hessC_eq_cxHessian, posSemidef_iff_dotProduct_mulVec]
  refine ⟨(isHermitian_one.smul ?_).sub (ChartHessianComparison.hess_isHermitian B hB y), fun x => ?_⟩
  · show star (((a * a' / 2 / (1 + sqn y)) : ℝ) : ℂ) = _
    simp
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    ChartHessianComparison.hess_form_eq B hB, star_dotProduct_self_eq, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  refine Complex.zero_le_real.mpr (sub_nonneg.mpr ?_)
  have hle := ChartHessianComparison.hessForm_le B hB y x 0
  simp only [zero_smul, sub_zero] at hle
  set w : Fin (e + 1) → ℂ := Fin.cons 0 (star x) with hw
  set v : Fin (e + 1) → ℂ := Fin.cons 1 y with hv
  have hw1 := hMa w
  have hv1 := haM v
  rw [one_mulVec, star_dotProduct_self_eq, Complex.ofReal_re] at hw1 hv1
  have hsw : sqn w = sqn x := by
    simp [sqn, hw, Fin.sum_univ_succ]
  have hsv : sqn v = 1 + sqn y := by
    simp [sqn, hv, Fin.sum_univ_succ]
  rw [hsw] at hw1
  rw [hsv] at hv1
  set qw := (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re
  set qv := (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re
  have hS := sqn_nonneg y
  have hX := sqn_nonneg x
  have hqv : 0 < qv := pos_of_mul_pos_right (show 0 < a' * qv by linarith) ha'.le
  have hr : 1 ≤ a' * qv / (1 + sqn y) := (one_le_div (by linarith)).mpr hv1
  calc _ ≤ qw / (2 * qv) := hle
    _ ≤ a * sqn x / (2 * qv) := by gcongr
    _ ≤ a * a' / 2 / (1 + sqn y) * sqn x := by
      rw [div_le_iff₀ (by positivity)]
      calc a * sqn x = a * sqn x * 1 := (mul_one _).symm
        _ ≤ a * sqn x * (a' * qv / (1 + sqn y)) := by gcongr
        _ = _ := by ring

theorem gradDens_le {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (hv : DifferentiableAt ℝ v y) (μ : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, (hessC (φ i) y).PosSemidef ∧
      (((μ : ℝ) : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - hessC (φ i) y).PosSemidef) :
    gradDens φ v v y ≤
      ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * ((n + 1) * (‖fderiv ℝ v y‖ ^ 2 * μ ^ n)) := by
  set a : Fin (n + 1) → ℂ := fun j => dz j (cplx v) y with ha
  set l : ℝ := ∑ j, ‖a j‖ ^ 2 with hl
  have hmono := mdisc_re_mono (Fin.cons (gradMat v v y) fun i => hessC (φ i) y)
    (Fin.cons ((l : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      fun _ : Fin n => (μ : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (by
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [gradMat_eq hv]; exact posSemidef_vecMulVec_self_star a
      · simp only [Fin.cons_succ]; exact (hφ i).1)
    (by
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [gradMat_eq hv]; exact posSemidef_sub_vecMulVec a
      · simp only [Fin.cons_succ]; exact (hφ i).2)
  rw [mdisc_cons_smul_one, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at hmono
  have hle : l ≤ (n + 1) * ‖fderiv ℝ v y‖ ^ 2 := by
    calc l ≤ ∑ _j : Fin (n + 1), ‖fderiv ℝ v y‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_dz_le hv j) 2
      _ = _ := by simp
  unfold gradDens
  have hc : 0 ≤ ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) := by positivity
  refine mul_le_mul_of_nonneg_left (hmono.trans ?_) hc
  calc l * μ ^ n ≤ ((n + 1) * ‖fderiv ℝ v y‖ ^ 2) * μ ^ n := mul_le_mul_of_nonneg_right hle (pow_nonneg hμ n)
    _ = _ := by ring

theorem finrank_eq (n : ℕ) : Module.finrank ℝ (Fin (n + 1) → ℂ) = 2 * n + 2 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  ring

end ChartCutoffEnergyAlt

open ChartCutoffEnergyAlt in

theorem ChartCutoffEnergy.proof : ChartCutoffEnergy.Statement := by
  intro n T hT
  choose C hC0 hC using fun i => hess_bound (hT i)
  set C' : ℝ := ∑ i, C i with hC'
  have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun i _ => hC0 i
  have hH : ∀ i y, (hessC (hermChartPot (T i)) y).PosSemidef ∧
      ((((C' / (1 + sqn y)) : ℝ) : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
        hessC (hermChartPot (T i)) y).PosSemidef := by
    intro i y
    refine ⟨(hC i y).1, ?_⟩
    have hle : C i ≤ C' := Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
    have hd : 0 ≤ C' / (1 + sqn y) - C i / (1 + sqn y) := by
      rw [← sub_div]; exact div_nonneg (sub_nonneg.mpr hle) (by linarith [sqn_nonneg y])
    have h := (PosSemidef.one.smul (Complex.zero_le_real.mpr hd)).add (hC i y).2
    rw [show C' / (1 + sqn y) = (C' / (1 + sqn y) - C i / (1 + sqn y)) + C i / (1 + sqn y) by ring,
      Complex.ofReal_add, add_smul, add_sub_assoc]
    exact h
  set F : (Fin (n + 1) → ℂ) → ℝ := fun x => ‖fderiv ℝ (chartCutoff 0 : (Fin (n + 1) → ℂ) → ℝ) x‖ ^ 2 with hF
  have hFint : Integrable F := by
    have hcont : Continuous F := ((contDiff_chartCutoff 0).continuous_fderiv (by norm_num)).norm.pow 2
    have hsupp : HasCompactSupport F :=
      (hasCompactSupport_chartCutoff_zero.fderiv (𝕜 := ℝ)).comp_left (g := fun t => ‖t‖ ^ 2) (by simp)
    exact hcont.integrable_of_hasCompactSupport hsupp
  set K0 : ℝ := ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * ((n + 1) * C' ^ n) with hK0
  have hK0n : 0 ≤ K0 := by positivity
  refine ⟨K0 * ∫ x, F x, fun k => ?_⟩
  set c : ℝ := ((k : ℝ) + 1)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set g : (Fin (n + 1) → ℂ) → ℝ := fun y => K0 * c ^ (2 * n + 2) * F (c • y) with hg
  have hgint : Integrable g := (hFint.comp_smul hc0.ne').const_mul _
  have hgI : ∫ y, g y = K0 * ∫ x, F x := by
    simp only [hg]
    rw [integral_const_mul, Measure.integral_comp_smul, finrank_eq, smul_eq_mul,
      abs_of_pos (by positivity), mul_assoc, ← mul_assoc (c ^ (2 * n + 2)), mul_inv_cancel₀ (by positivity), one_mul]
  have hpt : ∀ y, ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ g y := by
    intro y
    have hS := sqn_nonneg y
    have hv : DifferentiableAt ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y :=
      (contDiff_chartCutoff k).differentiable (by norm_num) y
    have h1 := gradDens_le _ _ y hv (C' / (1 + sqn y)) (div_nonneg hC'0 (by linarith)) (fun i => hH i y)
    have h2 := norm_fderiv_chartCutoff_le (D := n + 1) k y
    rw [← hc] at h2
    have h3 : ‖fderiv ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y‖ ^ 2 ≤ c ^ 2 * F (c • y) := by
      simp only [hF]
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : ‖fderiv ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y‖ ^ 2 * (C' / (1 + sqn y)) ^ n ≤
        c ^ 2 * F (c • y) * (C' ^ n * c ^ (2 * n)) := by
      by_cases hF0 : F (c • y) = 0
      · have h0 : ‖fderiv ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y‖ ^ 2 = 0 :=
          le_antisymm (by simpa [hF0] using h3) (by positivity)
        rw [h0, hF0]; simp
      · have hne : fderiv ℝ (chartCutoff 0 : (Fin (n + 1) → ℂ) → ℝ) (c • y) ≠ 0 := fun h =>
          hF0 (by simp [hF, h])
        have hs : 1 ≤ sqn (c • y) := by
          by_contra h
          push Not at h
          exact hne (fderiv_chartCutoff_zero_eq_zero h)
        rw [sqn_smul] at hs
        have hμ : C' / (1 + sqn y) ≤ C' * c ^ 2 := by
          rw [div_le_iff₀ (by linarith)]
          have : 1 ≤ c ^ 2 * (1 + sqn y) := by nlinarith [sq_nonneg c]
          nlinarith
        have hμ' : (C' / (1 + sqn y)) ^ n ≤ C' ^ n * c ^ (2 * n) := by
          calc _ ≤ (C' * c ^ 2) ^ n := pow_le_pow_left₀ (div_nonneg hC'0 (by linarith)) hμ n
            _ = _ := by rw [mul_pow, ← pow_mul]
        exact mul_le_mul h3 hμ' (by positivity) (by positivity)
    calc _ ≤ _ := h1
      _ ≤ ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
            ((n + 1) * (c ^ 2 * F (c • y) * (C' ^ n * c ^ (2 * n)))) := by gcongr
      _ = g y := by simp only [hg, hK0]; ring
  by_cases hi : Integrable (fun y =>
      ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y)
  · exact (integral_mono hi hgint hpt).trans hgI.le
  · rw [integral_undef hi]
    exact mul_nonneg hK0n (integral_nonneg fun x => by positivity)

end

end GroundTheory.Heights₂.Heights
