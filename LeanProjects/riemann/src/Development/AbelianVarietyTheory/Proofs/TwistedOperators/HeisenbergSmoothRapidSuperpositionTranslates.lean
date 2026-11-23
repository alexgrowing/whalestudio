import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau

open MeasureTheory Complex
open scoped ContDiff Real

noncomputable section

namespace GlobalTheory.RealWeil

namespace Superpos

variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) (y : Y) : ℂ :=
  cexp (2 * π * I * (om v (ι y) : ℂ))

def Mom (ν : Measure Y) (h : Y → ℂ) : Prop :=
  Continuous h ∧ ∀ n : ℕ, Integrable (fun y => ‖y‖ ^ n * ‖h y‖) ν

def itg (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B) (ι : Y →L[ℝ] V) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) : B :=
  (h y * ph om ι v y) • ρ (ι y) (g v)

theorem norm_ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) (y : Y) : ‖ph om ι v y‖ = 1 := by
  unfold ph
  rw [show (2 * π * I * (om v (ι y) : ℂ)) = ((2 * π * om v (ι y) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) : Continuous (ph om ι v) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ((om v).continuous.comp ι.continuous)))

variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}

theorem continuous_itg (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Continuous h) (g : V → B) (v : V) :
    Continuous (itg om ρ ι h g v) :=
  (hh.mul (continuous_ph om ι v)).smul ((hρ.2.2.2 (g v)).comp ι.continuous)

theorem norm_itg (hρ : IsHeis (fun x y => om x y) ρ) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) :
    ‖itg om ρ ι h g v y‖ = ‖h y‖ * ‖g v‖ := by
  simp [itg, norm_smul, norm_ph, hρ.2.2.1]

theorem integrable_itg (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) (g : V → B) (v : V) :
    Integrable (itg om ρ ι h g v) ν := by
  refine Integrable.mono' ((hh.2 0).mul_const ‖g v‖) (continuous_itg hρ hh.1 g v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_itg hρ]; simp

def dh (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (h : Y → ℂ) (z : V) (y : Y) : ℂ :=
  h y * (2 * π * I * (om z (ι y) : ℂ))

theorem mom_dh {h : Y → ℂ} (hh : Mom ν h) (z : V) : Mom ν (dh om ι h z) := by
  refine ⟨hh.1.mul (continuous_const.mul (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous))),
    fun n => ?_⟩
  refine Integrable.mono' ((hh.2 (n + 1)).const_mul (2 * π * ‖om‖ * ‖z‖ * ‖ι‖))
    ((continuous_norm.pow n).mul (continuous_norm.comp (hh.1.mul (continuous_const.mul
      (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous)))))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ‖om z (ι y)‖ ≤ ‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖) :=
    (om.le_opNorm₂ z (ι y)).trans (by gcongr; exact ι.le_opNorm y)
  have e2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [Real.norm_of_nonneg (by positivity), dh, norm_mul, norm_mul (2 * π * I : ℂ), e2, Complex.norm_real]
  have := Real.pi_pos
  have hy := norm_nonneg y
  have hhy := norm_nonneg (h y)
  calc ‖y‖ ^ n * (‖h y‖ * (2 * π * ‖om z (ι y)‖)) ≤ ‖y‖ ^ n * (‖h y‖ * (2 * π * (‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖)))) := by
        gcongr
    _ = 2 * π * ‖om‖ * ‖z‖ * ‖ι‖ * (‖y‖ ^ (n + 1) * ‖h y‖) := by ring

def dI (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B) (ι : Y →L[ℝ] V) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) :
    V →L[ℝ] B :=
  (h y * ph om ι v y) • (((ρ (ι y)).restrictScalars ℝ).comp (fderiv ℝ g v)) +
    (h y • (ph om ι v y • ((2 * π * I : ℂ) • (Complex.ofRealCLM.comp (om.flip (ι y)))))).smulRight (ρ (ι y) (g v))

theorem dI_apply (h : Y → ℂ) (g : V → B) (v : V) (y : Y) (z : V) :
    dI om ρ ι h g v y z = itg om ρ ι (dh om ι h z) g v y + itg om ρ ι h (fun w => fderiv ℝ g w z) v y := by
  simp only [dI, itg, dh, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul, smul_smul]
  rw [add_comm]
  congr 2
  ring

theorem hasFDerivAt_itg {g : V → B} (hg : Differentiable ℝ g) (h : Y → ℂ) (v : V) (y : Y) :
    HasFDerivAt (fun w => itg om ρ ι h g w y) (dI om ρ ι h g v y) v := by
  have b1 : HasFDerivAt (fun w : V => ((om w (ι y) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om.flip (ι y))) v :=
    (Complex.ofRealCLM.comp (om.flip (ι y))).hasFDerivAt
  have b2 := ((b1.const_mul (2 * π * I : ℂ)).cexp).const_mul (h y)
  have b3 : HasFDerivAt (fun w => ρ (ι y) (g w)) (((ρ (ι y)).restrictScalars ℝ).comp (fderiv ℝ g v)) v :=
    ((ρ (ι y)).restrictScalars ℝ).hasFDerivAt.comp v (hg v).hasFDerivAt
  exact b2.smul b3

theorem norm_dh_le (h : Y → ℂ) (z : V) (y : Y) :
    ‖dh om ι h z y‖ ≤ 2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖ := by
  have e1 : ‖om z (ι y)‖ ≤ ‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖) :=
    (om.le_opNorm₂ z (ι y)).trans (by gcongr; exact ι.le_opNorm y)
  have e2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [dh, norm_mul, norm_mul (2 * π * I : ℂ), e2, Complex.norm_real]
  have := Real.pi_pos
  have hhy := norm_nonneg (h y)
  calc ‖h y‖ * (2 * π * ‖om z (ι y)‖) ≤ ‖h y‖ * (2 * π * (‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖))) := by gcongr
    _ = 2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖ := by ring

theorem continuous_dI (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Continuous h) (g : V → B) (v : V) :
    Continuous (dI om ρ ι h g v) := by
  refine continuous_clm_apply.2 fun z => ?_
  simp only [dI_apply]
  exact (continuous_itg hρ (hh.mul (continuous_const.mul
    (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous)))) g v).add (continuous_itg hρ hh _ v)

theorem exists_bound (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v₀ : V) : ∃ bd : Y → ℝ, Integrable bd ν ∧
      ∀ y, ∀ v ∈ Metric.closedBall v₀ 1, ‖dI om ρ ι h g v y‖ ≤ bd y := by
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall v₀ 1).exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨Cd, hCd⟩ :=
    (isCompact_closedBall v₀ 1).exists_bound_of_continuousOn (hg.continuous_fderiv (by simp)).continuousOn
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg v₀ (Metric.mem_closedBall_self zero_le_one))
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd v₀ (Metric.mem_closedBall_self zero_le_one))
  have hK : 0 ≤ 2 * π * ‖om‖ * ‖ι‖ * Cg := by have := Real.pi_pos; positivity
  refine ⟨fun y => ‖h y‖ * (Cd + 2 * π * ‖om‖ * ‖ι‖ * Cg * ‖y‖), ?_, fun y v hv => ?_⟩
  · refine (((hh.2 0).const_mul Cd).add ((hh.2 1).const_mul (2 * π * ‖om‖ * ‖ι‖ * Cg))).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, pow_zero, pow_one]
    ring
  · refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg _) (add_nonneg hCd0 (mul_nonneg hK (norm_nonneg _)))) fun z => ?_
    rw [dI_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_itg hρ, norm_itg hρ]
    have hDz : ‖fderiv ℝ g v z‖ ≤ Cd * ‖z‖ :=
      ((fderiv ℝ g v).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hCd v hv) (norm_nonneg _))
    calc ‖dh om ι h z y‖ * ‖g v‖ + ‖h y‖ * ‖fderiv ℝ g v z‖
        ≤ (2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖) * Cg + ‖h y‖ * (Cd * ‖z‖) :=
          add_le_add (mul_le_mul (norm_dh_le h z y) (hCg v hv) (norm_nonneg _) (by have := Real.pi_pos; positivity))
            (mul_le_mul_of_nonneg_left hDz (norm_nonneg _))
      _ = ‖h y‖ * (Cd + 2 * π * ‖om‖ * ‖ι‖ * Cg * ‖y‖) * ‖z‖ := by ring

theorem hasFDerivAt_int (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v₀ : V) :
    HasFDerivAt (fun v => ∫ y, itg om ρ ι h g v y ∂ν) (∫ y, dI om ρ ι h g v₀ y ∂ν) v₀ := by
  obtain ⟨bd, hbd, hb⟩ := exists_bound hρ hh hg v₀
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.closedBall_mem_nhds v₀ one_pos)
    (Filter.Eventually.of_forall fun v => (continuous_itg hρ hh.1 g v).aestronglyMeasurable)
    (integrable_itg hρ hh g v₀) (continuous_dI hρ hh.1 g v₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y v hv => hb y v hv) hbd
    (Filter.Eventually.of_forall fun y v _ => hasFDerivAt_itg (hg.differentiable (by simp)) h v y)

theorem fderiv_int_apply (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v z : V) :
    fderiv ℝ (fun v => ∫ y, itg om ρ ι h g v y ∂ν) v z =
      (∫ y, itg om ρ ι (dh om ι h z) g v y ∂ν) + ∫ y, itg om ρ ι h (fun w => fderiv ℝ g w z) v y ∂ν := by
  obtain ⟨bd, hbd, hb⟩ := exists_bound hρ hh hg v
  have hi : Integrable (dI om ρ ι h g v) ν := hbd.mono' (continuous_dI hρ hh.1 g v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hb y v (Metric.mem_closedBall_self zero_le_one))
  rw [(hasFDerivAt_int hρ hh hg v).fderiv, ContinuousLinearMap.integral_apply hi]
  simp only [dI_apply]
  exact integral_add (integrable_itg hρ (mom_dh hh z) g v) (integrable_itg hρ hh _ v)

theorem contDiff_int (hρ : IsHeis (fun x y => om x y) ρ) (n : ℕ) : ∀ h : Y → ℂ, Mom ν h → ∀ g : V → B,
    ContDiff ℝ ∞ g → ContDiff ℝ n fun v => ∫ y, itg om ρ ι h g v y ∂ν := by
  induction n with
  | zero =>
    intro h hh g hg
    exact contDiff_zero.2 (Differentiable.continuous fun v => (hasFDerivAt_int hρ hh hg v).differentiableAt)
  | succ n ih =>
    intro h hh g hg
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun v => (hasFDerivAt_int hρ hh hg v).differentiableAt, by simp, fun z => ?_⟩
    simp only [fderiv_int_apply hρ hh hg]
    have hg' : ContDiff ℝ ∞ fun w => fderiv ℝ g w z :=
      (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (ih _ (mom_dh hh z) g hg).add (ih h hh _ hg')

end Superpos

theorem sm_superpos : ∀ (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν : MeasureTheory.Measure Y) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → GlobalTheory.RealWeil.IsHeis (fun x y => om x y) ρ → ∀ (ι : Y →L[ℝ] V) (c : Y → ℂ), Continuous c → (∀ n : ℕ, MeasureTheory.Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) → ∀ f : B, GlobalTheory.RealWeil.Sm ρ f → GlobalTheory.RealWeil.Sm ρ (∫ y, c y • ρ (ι y) f ∂ν) := by
  intro V Y _ _ _ _ _ _ _ _ ν B _ _ _ om ρ hom hρ ι c hc hm f hf
  have skew : ∀ v w, om w v = -om v w := by
    intro v w
    have := hom (v + w)
    simp only [map_add, ContinuousLinearMap.add_apply, hom] at this
    linarith
  have comm : ∀ v w b, ρ v (ρ w b) = cexp (2 * π * I * (om v w : ℂ)) • ρ w (ρ v b) := by
    intro v w b
    rw [hρ.2.1 v w, hρ.2.1 w v, smul_smul, ← Complex.exp_add, add_comm w v]
    simp only [skew v w]
    congr 2
    push_cast
    ring
  have hint : Integrable (fun y => c y • ρ (ι y) f) ν := by
    refine Integrable.mono' ((hm 0).mul_const ‖f‖) (hc.smul ((hρ.2.2.2 f).comp ι.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simp [norm_smul, hρ.2.2.1]
  have e : (fun v => ρ v (∫ y, c y • ρ (ι y) f ∂ν)) =
      fun v => ∫ y, Superpos.itg om ρ ι c (fun w => ρ w f) v y ∂ν := by
    funext v
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Superpos.itg, Superpos.ph, map_smul, comm v (ι y), smul_smul]
  unfold Sm
  rw [e]
  exact contDiff_infty.2 fun n => Superpos.contDiff_int hρ n c ⟨hc, hm⟩ _ hf

end GlobalTheory.RealWeil
