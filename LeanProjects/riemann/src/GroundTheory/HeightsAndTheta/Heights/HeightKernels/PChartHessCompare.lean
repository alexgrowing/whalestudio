import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsHermFormCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDensityIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramHess
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace ChartHessianComparison

section Gram

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}

def gramHess (u : F) (d : Fin e → F) : Matrix (Fin e) (Fin e) ℂ :=
  Matrix.of fun i j => (⟪u, u⟫_ℂ * ⟪d j, d i⟫_ℂ - ⟪u, d i⟫_ℂ * ⟪d j, u⟫_ℂ) / (2 * ⟪u, u⟫_ℂ ^ 2)

theorem gramHess_isHermitian (u : F) (d : Fin e → F) : (gramHess u d).IsHermitian := by
  ext i j
  simp only [gramHess, conjTranspose_apply, of_apply, star_div₀, star_sub, star_mul', star_pow,
    Complex.star_def, inner_conj_symm, map_ofNat]
  ring

theorem gramHess_form (u : F) (d : Fin e → F) (x : Fin e → ℂ) :
    star x ⬝ᵥ (gramHess u d *ᵥ x) =
      (⟪u, u⟫_ℂ * ⟪∑ i, star (x i) • d i, ∑ i, star (x i) • d i⟫_ℂ -
        ⟪u, ∑ i, star (x i) • d i⟫_ℂ * ⟪∑ i, star (x i) • d i, u⟫_ℂ) / (2 * ⟪u, u⟫_ℂ ^ 2) := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_mul_sum]
  simp only [dotProduct, mulVec, gramHess, of_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_numer_eq (u D : F) (hu : u ≠ 0) :
    (⟪u, u⟫_ℂ * ⟪D, D⟫_ℂ - ⟪u, D⟫_ℂ * ⟪D, u⟫_ℂ) / (2 * ⟪u, u⟫_ℂ ^ 2) =
      ((‖D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u‖ ^ 2 / (2 * ‖u‖ ^ 2) : ℝ) : ℂ) := by
  have hN0 : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hu
  have hNr : (starRingEnd ℂ) ⟪u, u⟫_ℂ = ⟪u, u⟫_ℂ := inner_conj_symm u u
  have hq : ⟪D, u⟫_ℂ = (starRingEnd ℂ) ⟪u, D⟫_ℂ := (inner_conj_symm D u).symm
  have hexp : ⟪D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u, D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u⟫_ℂ =
      ⟪D, D⟫_ℂ - ⟪u, D⟫_ℂ * (starRingEnd ℂ) ⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, map_div₀, hNr, hq]
    field_simp
    ring
  have hn1 : ⟪D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u, D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u⟫_ℂ =
      ((‖D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u‖ : ℝ) : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _
  have hn2 : ⟪u, u⟫_ℂ = ((‖u‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u
  push_cast
  rw [← hn1, ← hn2, hexp, hq]
  field_simp

theorem norm_sub_proj_le (u D : F) (hu : u ≠ 0) (s : ℂ) :
    ‖D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u‖ ^ 2 ≤ ‖D - s • u‖ ^ 2 := by
  have hN0 : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hu
  have hNr : (starRingEnd ℂ) ⟪u, u⟫_ℂ = ⟪u, u⟫_ℂ := inner_conj_symm u u
  have hq : ⟪D, u⟫_ℂ = (starRingEnd ℂ) ⟪u, D⟫_ℂ := (inner_conj_symm D u).symm
  set t := ⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ with ht
  have horth : ⟪D - t • u, (t - s) • u⟫_ℂ = 0 := by
    simp only [inner_smul_right, inner_sub_left, inner_smul_left, ht, map_div₀, hNr, hq]
    field_simp
    ring
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hsum : D - t • u + (t - s) • u = D - s • u := by
    rw [sub_smul]; abel
  rw [hsum] at h
  nlinarith [mul_self_nonneg ‖(t - s) • u‖]

theorem cxHessian_affine [CompleteSpace F] (c : F) (L : (Fin e → ℂ) →L[ℂ] F) (y : Fin e → ℂ)
    (h0 : c + L y ≠ 0) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪c + L y', c + L y'⟫_ℂ).re) y =
      gramHess (c + L y) (fun j => L (Pi.single j 1)) := by
  have hu : ∀ᶠ y' in nhds y, AnalyticAt ℂ (fun y' => c + L y') y' :=
    Filter.Eventually.of_forall fun y' => analyticAt_const.add (L.analyticAt y')
  have hd : fderiv ℂ (fun y' => c + L y') y = L := by
    rw [fderiv_const_add]; exact L.fderiv
  ext i j
  rw [ChartGram.cxHessian_half_log hu h0 i j, hd]
  rfl

theorem cxHessian_affine_form [CompleteSpace F] (c : F) (L : (Fin e → ℂ) →L[ℂ] F) (y x : Fin e → ℂ)
    (h0 : c + L y ≠ 0) :
    star x ⬝ᵥ (cxHessian (fun y' => 2⁻¹ * Real.log (⟪c + L y', c + L y'⟫_ℂ).re) y *ᵥ x) =
      ((‖L (star x) - (⟪c + L y, L (star x)⟫_ℂ / ⟪c + L y, c + L y⟫_ℂ) • (c + L y)‖ ^ 2 /
        (2 * ‖c + L y‖ ^ 2) : ℝ) : ℂ) := by
  have hD : ∑ i, star (x i) • L (Pi.single i 1) = L (star x) := by
    simp_rw [← L.map_smul, ← map_sum]
    congr 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [cxHessian_affine c L y h0, gramHess_form, hD, gram_numer_eq _ _ h0]

end Gram

section Chart

variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

def chartLin : (Fin e → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin (e + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (B *ᵥ (Fin.cons 0 y : Fin (e + 1) → ℂ))
      map_add' := fun y z => by
        have h : (Fin.cons 0 (y + z) : Fin (e + 1) → ℂ) = Fin.cons 0 y + Fin.cons 0 z := by
          funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp
        rw [h, mulVec_add, WithLp.toLp_add]
      map_smul' := fun a y => by
        have h : (Fin.cons 0 (a • y) : Fin (e + 1) → ℂ) = a • Fin.cons 0 y := by
          funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp
        rw [h, mulVec_smul, WithLp.toLp_smul]
        rfl }

theorem chartLin_apply (y : Fin e → ℂ) :
    chartLin B y = WithLp.toLp 2 (B *ᵥ (Fin.cons 0 y : Fin (e + 1) → ℂ)) := rfl

def chartConst : EuclideanSpace ℂ (Fin (e + 1)) :=
  WithLp.toLp 2 (B *ᵥ (Fin.cons 1 0 : Fin (e + 1) → ℂ))

theorem chart_add (y : Fin e → ℂ) :
    chartConst B + chartLin B y = WithLp.toLp 2 (B *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) := by
  have h : (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 0 + Fin.cons 0 y := by
    funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp
  rw [chartConst, chartLin_apply, h, mulVec_add, WithLp.toLp_add]

theorem chart_sub (y z : Fin e → ℂ) (t : ℂ) :
    chartLin B z - t • (chartConst B + chartLin B y) =
      WithLp.toLp 2 (B *ᵥ ((Fin.cons 0 z : Fin (e + 1) → ℂ) - t • Fin.cons 1 y)) := by
  rw [chart_add, chartLin_apply, mulVec_sub, mulVec_smul, WithLp.toLp_sub, WithLp.toLp_smul]

theorem inner_toLp_mulVec (v w : Fin (e + 1) → ℂ) :
    ⟪(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))), WithLp.toLp 2 (B *ᵥ w)⟫_ℂ =
      star v ⬝ᵥ ((Bᴴ * B) *ᵥ w) := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem norm_sq_toLp_mulVec (v : Fin (e + 1) → ℂ) :
    ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1)))‖ ^ 2 = (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re := by
  rw [← inner_toLp_mulVec]
  have h : ⟪(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))), WithLp.toLp 2 (B *ᵥ v)⟫_ℂ =
      ((‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1)))‖ : ℝ) : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem toLp_mulVec_ne_zero (hB : B.det ≠ 0) {v : Fin (e + 1) → ℂ} (hv : v ≠ 0) :
    (WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))) ≠ 0 := by
  intro h
  apply hv
  apply eq_zero_of_mulVec_eq_zero hB
  have := congrArg WithLp.ofLp h
  simpa using this

theorem hermChartPot_eq :
    hermChartPot (Bᴴ * B) = fun y => 2⁻¹ * Real.log (⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ).re := by
  funext y
  unfold hermChartPot
  rw [← inner_toLp_mulVec, ← chart_add, Real.log_sqrt (show (0 : ℝ) ≤
    (⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ).re from inner_self_nonneg (𝕜 := ℂ))]
  ring

def hessForm (y x : Fin e → ℂ) : ℝ :=
  ‖chartLin B (star x) - (⟪chartConst B + chartLin B y, chartLin B (star x)⟫_ℂ /
      ⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ) • (chartConst B + chartLin B y)‖ ^ 2 /
    (2 * ‖chartConst B + chartLin B y‖ ^ 2)

theorem chart_ne_zero (hB : B.det ≠ 0) (y : Fin e → ℂ) : chartConst B + chartLin B y ≠ 0 := by
  rw [chart_add]
  refine toLp_mulVec_ne_zero B hB fun h => ?_
  have := congrFun h 0
  simp at this

theorem hess_form_eq (hB : B.det ≠ 0) (y x : Fin e → ℂ) :
    star x ⬝ᵥ (cxHessian (hermChartPot (Bᴴ * B)) y *ᵥ x) = (hessForm B y x : ℂ) := by
  rw [hermChartPot_eq, cxHessian_affine_form _ _ _ _ (chart_ne_zero B hB y)]
  rfl

theorem hess_isHermitian (hB : B.det ≠ 0) (y : Fin e → ℂ) :
    (cxHessian (hermChartPot (Bᴴ * B)) y).IsHermitian := by
  rw [hermChartPot_eq, cxHessian_affine _ _ _ (chart_ne_zero B hB y)]
  exact gramHess_isHermitian _ _

theorem hessForm_le (hB : B.det ≠ 0) (y x : Fin e → ℂ) (s : ℂ) :
    hessForm B y x ≤
      (star ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y) ⬝ᵥ
          ((Bᴴ * B) *ᵥ ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y))).re /
        (2 * (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Bᴴ * B) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re) := by
  have hu := chart_ne_zero B hB y
  unfold hessForm
  rw [← norm_sq_toLp_mulVec, ← norm_sq_toLp_mulVec, ← chart_sub, ← chart_add]
  exact div_le_div_of_nonneg_right (norm_sub_proj_le _ _ hu s) (by positivity)

theorem hessForm_eq (y x : Fin e → ℂ) :
    ∃ s : ℂ, hessForm B y x =
      (star ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y) ⬝ᵥ
          ((Bᴴ * B) *ᵥ ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y))).re /
        (2 * (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Bᴴ * B) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re) := by
  refine ⟨⟪chartConst B + chartLin B y, chartLin B (star x)⟫_ℂ /
      ⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ, ?_⟩
  unfold hessForm
  rw [← norm_sq_toLp_mulVec, ← norm_sq_toLp_mulVec, ← chart_sub, ← chart_add]

theorem hessForm_pos (hB : B.det ≠ 0) (y : Fin e → ℂ) {x : Fin e → ℂ} (hx : x ≠ 0) :
    0 < hessForm B y x := by
  have hu := chart_ne_zero B hB y
  unfold hessForm
  rw [chart_sub]
  refine div_pos (pow_pos (norm_pos_iff.mpr (toLp_mulVec_ne_zero B hB fun h => hx ?_)) 2)
    (by have := norm_pos_iff.mpr hu; positivity)
  set t := ⟪chartConst B + chartLin B y, chartLin B (star x)⟫_ℂ /
      ⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ
  have h0 : t = 0 := by simpa using congrFun h 0
  funext k
  have hk := congrFun h k.succ
  simp [h0] at hk
  simpa using hk

end Chart

end ChartHessianComparison

open ChartHessianComparison in

theorem ChartHessCompare.proof (hCmp : HermFormCompare.Statement) : ChartHessCompare.Statement := by
  intro e M N hM hN
  obtain ⟨B, hMB, hB⟩ := ChartDensityIntegrableAlt.exists_conjTranspose_mul_self hM
  obtain ⟨B', hNB, hB'⟩ := ChartDensityIntegrableAlt.exists_conjTranspose_mul_self hN
  obtain ⟨a, ha, hMN⟩ := hCmp (e + 1) M N hM hN
  obtain ⟨a', ha', hNM⟩ := hCmp (e + 1) N M hN hM
  subst hMB hNB
  refine ⟨a * a', fun y => ⟨?_, ?_⟩⟩
  · refine PosDef.of_dotProduct_mulVec_pos (hess_isHermitian B hB y) fun x hx => ?_
    rw [hess_form_eq B hB]
    exact Complex.zero_lt_real.mpr (hessForm_pos B hB y hx)
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨((hess_isHermitian B' hB' y).smul ?_).sub (hess_isHermitian B hB y), fun x => ?_⟩
    · show star ((a * a' : ℝ) : ℂ) = ((a * a' : ℝ) : ℂ)
      simp
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hess_form_eq B hB,
      hess_form_eq B' hB', smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    refine Complex.zero_le_real.mpr (sub_nonneg.mpr ?_)
    obtain ⟨s, hs⟩ := hessForm_eq B' y x
    have h1 := hessForm_le B hB y x s
    rw [hs]
    set w := (Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y with hw
    set v := (Fin.cons 1 y : Fin (e + 1) → ℂ) with hv
    have hv0 : v ≠ 0 := fun h => by simpa [hv] using congrFun h 0
    have hqv : 0 < (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re := by
      rw [← norm_sq_toLp_mulVec]
      have := norm_pos_iff.mpr (toLp_mulVec_ne_zero B hB hv0)
      positivity
    have hqv' : 0 < (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re := by
      rw [← norm_sq_toLp_mulVec]
      have := norm_pos_iff.mpr (toLp_mulVec_ne_zero B' hB' hv0)
      positivity
    have hqw' : 0 ≤ (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re := by
      rw [← norm_sq_toLp_mulVec]
      positivity
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    set r := (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re / (2 * (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re) with hr
    have hr0 : 0 ≤ r := by positivity
    have e1 : (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re = r * (2 * (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re) := by
      rw [hr, div_mul_cancel₀ _ (by positivity)]
    calc (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re ≤ a * (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re := hMN w
      _ = a * r * 2 * (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re := by rw [e1]; ring
      _ ≤ a * r * 2 * (a' * (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re) := by gcongr; exact hNM v
      _ = a * a' * r * (2 * (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re) := by ring

end

end GroundTheory.Heights₂.Heights
