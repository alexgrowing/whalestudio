import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve

noncomputable section

open MeasureTheory Filter Topology
open scoped ZeroAtInfty ContDiff

namespace GlobalTheory.CompanionTheory.WaveCurve.Decay

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.WaveCurve

local notation "sg(" y ")" => (((y : ℝ) : ℂ) ^ (1 / 2 : ℂ))

def ct (φ : ℝ → ℝ) (y : ℝ) : ℂ := ∫ t, (φ t : ℂ) * chj 0 t y

def Tst (φ : ℝ → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

lemma Tst.deriv {φ : ℝ → ℝ} (h : Tst φ) : Tst (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.1 h.1).2, h.2.deriv⟩

lemma Tst.cont {φ : ℝ → ℝ} (h : Tst φ) : Continuous fun t => (φ t : ℂ) :=
  Complex.continuous_ofReal.comp h.1.continuous

lemma Tst.cs {φ : ℝ → ℝ} (h : Tst φ) : HasCompactSupport fun t => (φ t : ℂ) :=
  h.2.comp_left Complex.ofReal_zero

lemma chj_add_two (j : ℕ) (t y : ℝ) : chj (j + 2) t y = (y : ℂ) * chj j t y := by
  have h : (sg(y)) ^ 2 = (y : ℂ) := by
    simpa using Complex.cpow_nat_inv_pow (y : ℂ) (n := 2) (by norm_num)
  have hp : Even (j + 2) ↔ Even j := by simp [Nat.even_add]
  unfold chj
  simp only [hp, pow_add, h]
  ring

lemma chj_zero (t y : ℝ) : chj 0 t y = Complex.cosh ((t : ℂ) * sg(y)) := by
  simp [chj]

lemma chj_cont (j : ℕ) (y : ℝ) : Continuous fun t => chj j t y :=
  continuous_iff_continuousAt.2 fun t => (chj_hasDerivAt j t y).continuousAt

lemma ibp {φ : ℝ → ℝ} (h : Tst φ) (j : ℕ) (y : ℝ) :
    ∫ t, (φ t : ℂ) * chj (j + 1) t y = - ∫ t, ((deriv φ t : ℝ) : ℂ) * chj j t y := by
  have hd : ∀ t, HasDerivAt (fun t => (φ t : ℂ)) ((deriv φ t : ℝ) : ℂ) t := fun t =>
    ((h.1.differentiable (by simp)) t).hasDerivAt.ofReal_comp
  have i : ∀ (ψ : ℝ → ℝ), Tst ψ → ∀ k : ℕ,
      Integrable ((fun t => (ψ t : ℂ)) * (fun t => chj k t y)) := fun ψ hψ k =>
    (hψ.cont.mul (chj_cont k y)).integrable_of_hasCompactSupport hψ.cs.mul_right
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hd t)
    (fun t _ => chj_hasDerivAt j t y) (i φ h (j + 1)) (i _ h.deriv j) (i φ h j)

lemma ct_two {φ : ℝ → ℝ} (h : Tst φ) (y : ℝ) :
    (y : ℂ) * ct φ y = ct (deriv (deriv φ)) y := by
  unfold ct
  rw [← integral_const_mul]
  have e : ∀ t, (y : ℂ) * ((φ t : ℂ) * chj 0 t y) = (φ t : ℂ) * chj (1 + 1) t y := by
    intro t
    rw [show chj (1 + 1) t y = chj (0 + 2) t y from rfl, chj_add_two 0]
    ring
  simp_rw [e]
  rw [ibp h 1 y, ibp h.deriv 0 y, neg_neg]

lemma ct_pow (m : ℕ) {φ : ℝ → ℝ} (h : Tst φ) :
    ∃ ψ, Tst ψ ∧ ∀ y : ℝ, (y : ℂ) ^ m * ct φ y = ct ψ y := by
  induction m with
  | zero => exact ⟨φ, h, fun y => by simp⟩
  | succ m ih =>
    obtain ⟨ψ, hψ, e⟩ := ih
    refine ⟨deriv (deriv ψ), hψ.deriv.deriv, fun y => ?_⟩
    rw [← ct_two hψ, ← e, pow_succ]
    ring

lemma ct_continuous {φ : ℝ → ℝ} (h : Tst φ) : Continuous (ct φ) := by
  have hc : Continuous fun p : ℝ × ℝ => chj 0 p.2 p.1 := by
    simp only [chj_zero]
    exact Complex.continuous_cosh.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      (sg_continuous.comp continuous_fst))
  have hf : Continuous (Function.uncurry fun (y t : ℝ) => (φ t : ℂ) * chj 0 t y) :=
    (h.cont.comp continuous_snd).mul hc
  have := continuous_parametric_integral_of_continuous (μ := volume) hf h.2
  convert this using 2 with y
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
  simp [image_eq_zero_of_notMem_tsupport ht]

lemma ct_bound (c : ℝ) {φ : ℝ → ℝ} (h : Tst φ) :
    ∃ B : ℝ, ∀ y, ‖(cut c y : ℂ) * ct φ y‖ ≤ B := by
  set A := Real.sqrt (max (c + 1) 0) with hA
  have hi : Integrable fun t => ‖(φ t : ℂ)‖ * Real.exp (|t| * A) :=
    (h.cont.norm.mul (by fun_prop)).integrable_of_hasCompactSupport h.cs.norm.mul_right
  refine ⟨∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A), fun y => ?_⟩
  have hB : 0 ≤ ∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A) :=
    integral_nonneg fun t => by positivity
  rcases le_or_gt (c + 1) y with hy | hy
  · simpa [cut_eq_zero hy] using hB
  · have h1 : ‖ct φ y‖ ≤ ∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A) := by
      refine norm_integral_le_of_norm_le hi (Eventually.of_forall fun t => ?_)
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h2 := hyp_le 0 t y
      rw [chj_zero]
      simp only [Even.zero, if_true] at h2
      refine h2.trans (Real.exp_le_exp.2 ?_)
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (max_le_max_right _ hy.le)) (abs_nonneg _)
    have h3 : ‖(cut c y : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg c y)]
      exact cut_le_one c y
    rw [norm_mul]
    calc _ ≤ 1 * ∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A) :=
          mul_le_mul h3 h1 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

lemma tst_of_bump {g : ℝ → ℝ} {T : ℝ} (hb : IsBump g T) : Tst g := by
  refine ⟨hb.1, HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun t ht => ?_⟩
  refine hb.2.2 t ?_
  simpa [Real.norm_eq_abs] using ht

lemma hg_pow {g : ℝ → ℝ} (h : Tst g) (c : ℝ) (m : ℕ) :
    ∃ ψ, Tst ψ ∧ ∀ y : ℝ, (y : ℂ) ^ m * hg c g y = (cut c y : ℂ) * ct ψ y := by
  obtain ⟨ψ, hψ, e⟩ := ct_pow m h
  refine ⟨ψ, hψ, fun y => ?_⟩
  rw [← e]
  show (y : ℂ) ^ m * ((cut c y : ℂ) * ct g y) = _
  ring

lemma hg_continuous {g : ℝ → ℝ} (h : Tst g) (c : ℝ) (m : ℕ) :
    Continuous fun y : ℝ => (y : ℂ) ^ m * hg c g y := by
  obtain ⟨ψ, hψ, e⟩ := hg_pow h c m
  simp only [e]
  exact (Complex.continuous_ofReal.comp (cut_continuous c)).mul (ct_continuous hψ)

lemma hg_tendsto {g : ℝ → ℝ} (h : Tst g) (c : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ m * hg c g y) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨ψ, hψ, e⟩ := hg_pow h c (m + 1)
  obtain ⟨B, hB⟩ := ct_bound c hψ
  have hn : Tendsto (fun y : ℝ => ‖y‖) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop
  refine squeeze_zero_norm' (a := fun y : ℝ => B * ‖y‖⁻¹) ?_ ?_
  · filter_upwards [hn.eventually_gt_atTop 0] with y hy
    rw [← div_eq_mul_inv, le_div_iff₀ hy]
    have h1 := hB y
    have h2 : (y : ℂ) ^ m * (y : ℂ) * hg c g y = ((y : ℂ) ^ m * hg c g y) * (y : ℂ) := by ring
    rw [← e, pow_succ, h2, norm_mul, Complex.norm_real] at h1
    exact h1
  · simpa using (tendsto_inv_atTop_zero.comp hn).const_mul B

def ev (y : ℝ) : C₀(ℝ, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact f.toBCF.norm_coe_le_norm y)

lemma ev_apply (y : ℝ) (f : C₀(ℝ, ℂ)) : ev y f = f y := rfl

theorem pwdecay : PWdecay := by
  intro c g T hb
  have hT := tst_of_bump hb
  refine ⟨fun m => ⟨hg_continuous hT c m, hg_tendsto hT c m⟩, fun N hN => ?_⟩
  set R : ℝ → ℂ := fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y with hR
  have hW : Continuous fun y : ℝ => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) fun y => by positivity)
  have hg0 := hg_continuous hT c 0
  have ht0 := hg_tendsto hT c 0
  simp only [pow_zero, one_mul] at hg0 ht0
  have hRc : Continuous R := hW.mul hg0
  have hRt : Tendsto R (cocompact ℝ) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun y => ‖hg c g y‖) (fun y => ?_) (by simpa using ht0.norm)
    rw [hR, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |((1 + y ^ 2) ^ N)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [sq_nonneg y]))
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hF : Continuous fun t => toC0 (wv c N 0 t) :=
    continuous_iff_continuousAt.2 fun t => (fcurve c N 0 (by omega) t).2.continuousAt
  have hH : Integrable fun t => (g t : ℂ) • toC0 (wv c N 0 t) :=
    (hT.cont.smul hF).integrable_of_hasCompactSupport hT.cs.smul_right
  ext y
  rw [coe_toC0 hRc hRt, ← ev_apply y, ← (ev y).integral_comp_comm hH]
  have e : ∀ t, ev y ((g t : ℂ) • toC0 (wv c N 0 t)) =
      ((cut c y * ((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * ((g t : ℂ) * chj 0 t y) := by
    intro t
    have h1 := (fcurve c N 0 (by omega) t).1
    rw [map_smul, ev_apply, coe_toC0 h1.1 h1.2, smul_eq_mul]
    unfold wv
    ring
  simp_rw [e]
  rw [integral_const_mul, hR]
  show _ = _ * ((cut c y : ℂ) * ct g y)
  unfold ct
  push_cast
  ring

end GlobalTheory.CompanionTheory.WaveCurve.Decay
