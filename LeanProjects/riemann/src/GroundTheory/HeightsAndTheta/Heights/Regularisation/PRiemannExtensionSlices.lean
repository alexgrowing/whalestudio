import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StRiemannSlices
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood

open scoped Real

noncomputable section

namespace RiemannExtensionSlices

theorem torusMap_zero_mem {n : ℕ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : Fin n → ℝ) :
    torusMap (0 : Fin n → ℂ) (fun _ => r) θ ∈ ball (0 : Fin n → ℂ) 1 ∧
      ∀ i, torusMap (0 : Fin n → ℂ) (fun _ => r) θ i ≠ 0 := by
  refine ⟨closedBall_subset_ball hr1 (torusMap_mem_closedBall 0 hr0.le θ), fun i h => ?_⟩
  have h1 := norm_torusMap_sub (0 : Fin n → ℂ) hr0.le θ i
  rw [h, Pi.zero_apply, sub_zero, norm_zero] at h1
  exact hr0.ne h1

theorem continuous_comp_torusMap_zero {n : ℕ} {G : (Fin n → ℂ) → ℂ}
    (hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous fun θ => G (torusMap (0 : Fin n → ℂ) (fun _ => r) θ) :=
  continuous_iff_continuousAt.2 fun θ =>
    (hd _ (torusMap_zero_mem hr0 hr1 θ).1 (torusMap_zero_mem hr0 hr1 θ).2).continuousAt.comp
      (continuous_torusMap 0 r).continuousAt

theorem cons_mem_ball_one {n : ℕ} {x : ℂ} (hx : ‖x‖ < 1) {y : Fin n → ℂ}
    (hy : y ∈ ball (0 : Fin n → ℂ) 1) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball 0 1 := by
  refine (mem_ball_pi_iff one_pos).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using (mem_ball_pi_iff one_pos).mp hy j

theorem cons_ne_zero {n : ℕ} {x : ℂ} (hx : x ≠ 0) {y : Fin n → ℂ} (hy : ∀ i, y i ≠ 0) :
    ∀ i, (Fin.cons x y : Fin (n + 1) → ℂ) i ≠ 0 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using hy j

theorem cauchy_torus_off_axes : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ) →
    (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c)) →
    ∀ r : ℝ, 0 < r → r < 1 → ∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) →
    (∯ ζ in T(0, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, _, _, r, _, _, z, _, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z 0]
  | n + 1, G, hd, hlim, r, hr0, hr1, z, hz, hzW => by
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) 0 (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (continuous_comp_torusMap_zero hd hr0 hr1)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap 0 r)).sub continuous_const
    rw [torusIntegral_succ hint]
    have hz1 : z ∈ ball (0 : Fin (n + 1) → ℂ) 1 := ball_subset_ball hr1.le hz
    have hz' : Fin.tail z ∈ ball (0 : Fin n → ℂ) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'1 : Fin.tail z ∈ ball (0 : Fin n → ℂ) 1 := ball_subset_ball hr1.le hz'
    have hzW' : ∀ i, Fin.tail z i ≠ 0 := fun i => hzW i.succ
    have key : EqOn (fun x => ∯ y in T((0 : Fin (n + 1) → ℂ) ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere ((0 : Fin (n + 1) → ℂ) 0) r) := by
      intro x hx
      have hxn : ‖x‖ = r := by simpa using hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hxn
        exact hr0.ne hxn
      have hx1 : ‖x‖ < 1 := hxn ▸ hr1
      have hd' : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) →
          DifferentiableAt ℂ (fun y => G (Fin.cons x y)) ζ := fun ζ hζ hζW =>
        (hd _ (cons_mem_ball_one hx1 hζ) (cons_ne_zero hx0 hζW)).comp ζ (differentiable_cons_right x ζ)
      have hlim' : ∀ w ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → w j ≠ 0) →
          ∃ c : ℂ, Tendsto (fun t : ℂ => (fun y => G (Fin.cons x y)) (Function.update w i t))
            (𝓝[≠] 0) (𝓝 c) := by
        intro w hw i hwi
        have hne : ∀ j, j ≠ i.succ → (Fin.cons x w : Fin (n + 1) → ℂ) j ≠ 0 := by
          intro j hj
          induction j using Fin.cases with
          | zero => simpa using hx0
          | succ k => simpa using hwi k (fun h => hj (by rw [h]))
        obtain ⟨c, hc⟩ := hlim _ (cons_mem_ball_one hx1 hw) i.succ hne
        refine ⟨c, ?_⟩
        simp only [Fin.cons_update]
        exact hc
      have ih := cauchy_torus_off_axes n (fun y => G (Fin.cons x y)) hd' hlim' r hr0 hr1 (Fin.tail z) hz' hzW'
      have e0 : ((0 : Fin (n + 1) → ℂ) ∘ Fin.succ) = 0 := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    obtain ⟨c, hc⟩ := hlim z hz1 0 (fun j _ => hzW j)
    have hupd : ∀ x : ℂ, Function.update z 0 x = Fin.cons x (Fin.tail z) := fun x => by
      rw [← Fin.update_cons_zero (x := z 0) (p := Fin.tail z) (z := x), Fin.cons_self_tail]
    have hg : Tendsto (fun x => G (Fin.cons x (Fin.tail z))) (𝓝[≠] 0) (𝓝 c) := by
      simpa only [hupd] using hc
    have hgd : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 → DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x :=
      fun x hx0 hx1 => (hd _ (cons_mem_ball_one hx1 hz'1) (cons_ne_zero hx0 hzW')).comp x
        (differentiable_cons_left (Fin.tail z) x)
    have heq : ∀ x : ℂ, x ≠ 0 → Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c =ᶠ[𝓝 x]
        (fun x => G (Fin.cons x (Fin.tail z))) := fun x hx =>
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun y hy => Function.update_of_ne hy _ _
    have hcont : ContinuousOn (Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c)
        (closedBall 0 r) := by
      intro x hx
      by_cases hx0 : x = 0
      · subst hx0
        exact (continuousAt_update_same.mpr hg).continuousWithinAt
      · have hx1 : ‖x‖ < 1 := lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) hr1
        exact ((hgd x hx0 hx1).continuousAt.congr (heq x hx0).symm).continuousWithinAt
    have hdiff : ∀ x ∈ ball (0 : ℂ) r \ {0},
        DifferentiableAt ℂ (Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c) x :=
      fun x hx => (hgd x hx.2 (lt_trans (mem_ball_zero_iff.mp hx.1) hr1)).congr_of_eventuallyEq
        (heq x hx.2)
    have hz0 : z 0 ∈ ball (0 : ℂ) r := by simpa using (mem_ball_pi_iff hr0).mp hz 0
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (countable_singleton 0)
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    have hcirc : (∮ x in C((0 : Fin (n + 1) → ℂ) 0, r), (x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))) =
        ∮ x in C(0, r), (x - z 0)⁻¹ *
          Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c x := by
      refine circleIntegral.integral_congr hr0.le fun x hx => ?_
      have hxn : ‖x‖ = r := by simpa using hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hxn
        exact hr0.ne hxn
      simp only [Function.update_of_ne hx0]
    rw [hcirc, h1, Function.update_of_ne (hzW 0), Fin.cons_self_tail, pow_succ]
    ring

def torusFunctional {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hf : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  have hint : ∀ g : C(Cube n, ℂ), IntegrableOn
      (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := fun g =>
    ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn
      (((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hf))
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (hint g) (hint g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hf).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctl_kern {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hz : z ∈ ball c r) :
    fctl c r f (kern c r z) = ∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ := by
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring

theorem kern_analyticAt_of_mem {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) {z : Fin n → ℂ}
    (hz : z ∈ ball c r) : AnalyticAt ℂ (kern c r) z := by
  refine Finset.analyticAt_fun_prod _ fun i _ => ?_
  set u := cubeCoord c r i - z i • (1 : C(Cube n, ℂ))
  have hu : IsUnit u := (ContinuousMap.isUnit_iff_forall_ne_zero u).mpr fun θ' => by
    simp only [u, cubeCoord, ContinuousMap.sub_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact torusMap_sub_ne hr hz θ'.1 i
  have hA : AnalyticAt ℂ (fun w : Fin n → ℂ => cubeCoord c r i - w i • (1 : C(Cube n, ℂ))) z := by
    have h := (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i) (1 : C(Cube n, ℂ))).analyticAt z
    exact analyticAt_const.sub h
  exact (analyticAt_inverse (𝕜 := ℂ) hu.unit).comp_of_eq hA (by simp [u])

theorem exists_analytic_on_ball {n : ℕ} {G : (Fin n → ℂ) → ℂ}
    (hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ)
    (hlim : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ Φ : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Φ (ball 0 r) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) → Φ z = G z := by
  set L := torusFunctional 0 r G (continuous_comp_torusMap_zero hd hr0 hr1)
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  refine ⟨fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern 0 r z), fun z hz =>
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem 0 hr0 hz)), fun z hz hzW => ?_⟩
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl 0 r G (kern 0 r z) = G z
  rw [fctl_kern hr0 G hz, cauchy_torus_off_axes n G hd hlim r hr0 hr1 z hz hzW, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

end RiemannExtensionSlices

open RiemannExtensionSlices in

theorem RiemannExtensionSlices.proof : RiemannExtensionSlices.Statement := by
  intro n G hG hlim
  obtain ⟨W, hW⟩ : ∃ W : Set (Fin n → ℂ), W = {w | ∀ i, w i ≠ 0} := ⟨_, rfl⟩
  rw [← hW] at hG
  have hWo : IsOpen W := by
    rw [hW, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const
  have hWd : Dense W := by
    have h := dense_pi (α := fun _ : Fin n => ℂ) (s := fun _ => ({0}ᶜ : Set ℂ)) univ
      (fun i _ => dense_compl_singleton 0)
    convert h using 1
    ext z
    simp [hW]
  have hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ := fun ζ h1 h2 =>
    hG.differentiableAt ((isOpen_ball.inter hWo).mem_nhds ⟨h1, by rw [hW]; exact h2⟩)
  have hlimUnder : ∀ r : ℝ, ∀ Φ : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Φ (ball 0 r) →
      (∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) → Φ z = G z) →
      ∀ w ∈ ball (0 : Fin n → ℂ) r, limUnder (𝓝[W] w) G = Φ w := by
    intro r Φ hΦa hΦG w hw
    have : (𝓝[W] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hWd w)
    have hev : Φ =ᶠ[𝓝[W] w] G := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hw)]
        with x hxW hxb
      rw [hW] at hxW
      exact hΦG x hxb hxW
    exact (Tendsto.congr' hev ((hΦa w hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).limUnder_eq
  have hrad : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∃ r : ℝ, 0 < r ∧ r < 1 ∧ z ∈ ball (0 : Fin n → ℂ) r := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith, mem_ball_zero_iff.mpr (by linarith)⟩
  refine ⟨fun z => limUnder (𝓝[W] z) G, fun z hz => ?_, fun z hz hzW => ?_⟩
  · obtain ⟨r, hr0, hr1, hzr⟩ := hrad z hz
    obtain ⟨Φ, hΦa, hΦG⟩ := exists_analytic_on_ball hd hlim hr0 hr1
    refine (hΦa z hzr).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hzr] with w hw
    exact (hlimUnder r Φ hΦa hΦG w hw).symm
  · obtain ⟨r, hr0, hr1, hzr⟩ := hrad z hz
    obtain ⟨Φ, hΦa, hΦG⟩ := exists_analytic_on_ball hd hlim hr0 hr1
    show limUnder (𝓝[W] z) G = G z
    rw [hlimUnder r Φ hΦa hΦG z hzr, hΦG z hzr hzW]

end

end GroundTheory.Heights₂.Heights.Regular
