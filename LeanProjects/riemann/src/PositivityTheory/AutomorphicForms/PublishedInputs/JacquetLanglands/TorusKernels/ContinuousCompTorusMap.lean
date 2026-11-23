import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

noncomputable section

namespace UpperTheory.Esk.OrbitalSingularIntegrals

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood

open scoped Real

def SepHol {n : ℕ} (f : (Fin n → ℂ) → ℂ) (S : Set (Fin n → ℂ)) : Prop :=
  ContinuousOn f S ∧ ∀ ζ ∈ S, ∀ i, DifferentiableAt ℂ (fun t => f (Function.update ζ i t)) (ζ i)

theorem continuous_comp_torusMap' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall c r)) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) :=
  hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_closedBall c hr)

theorem torusIntegrable_kernel' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  refine Continuous.mul ?_ (continuous_comp_torusMap' hr.le hf)
  refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr hz θ i
  exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const

theorem cauchy' : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    SepHol f (closedBall c r) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ (torusIntegrable_kernel' hr hf.1 hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have hS : SepHol (fun y => f (Fin.cons x y)) (closedBall (fun i => c (Fin.succ i)) r) := by
        refine ⟨?_, fun ζ hζ j => ?_⟩
        · exact hf.1.comp (differentiable_cons_right x).continuous.continuousOn
            (fun y hy => hcons x hxc y hy)
        · have h1 := hf.2 (Fin.cons x ζ) (hcons x hxc ζ hζ) j.succ
          have e : (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) =
              fun t => f (Function.update (Fin.cons x ζ : Fin (n + 1) → ℂ) j.succ t) := by
            funext t
            rw [Fin.cons_update]
          show DifferentiableAt ℂ (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) (ζ j)
          rw [e]
          simpa only [Fin.cons_succ] using h1
      have ih := cauchy' n (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr hS (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) := by
      intro x hx
      have h1 := hf.2 (Fin.cons x (Fin.tail z)) (hcons x hx _ (ball_subset_closedBall hz')) 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h1
      exact h1.differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

variable {n : ℕ}

theorem integrableOn_fctl' {c : Fin n → ℂ} {r : ℝ} {f : (Fin n → ℂ) → ℂ}
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  exact ((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hc

def fctlCLM' (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl' hc g) (integrableOn_fctl' hc g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hc).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM'_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : SepHol f (closedBall c r)) (hz : z ∈ ball c r) :
    fctlCLM' c r f (continuous_comp_torusMap' hr.le hf.1) (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy' n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring

theorem osgFin (U : Set (Fin n → ℂ)) (hU : IsOpen U) (f : (Fin n → ℂ) → ℂ) (hf : SepHol f U) :
    AnalyticOnNhd ℂ f U := by
  intro z0 hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : closedBall z0 (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hS : SepHol f (closedBall z0 (ε / 2)) :=
    ⟨hf.1.mono hsub, fun ζ hζ i => hf.2 ζ (hsub hζ) i⟩
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ *
      fctlCLM' z0 (ε / 2) f (continuous_comp_torusMap' hr.le hS.1) (kern z0 (ε / 2) z)) z0 :=
    analyticAt_const.mul (((fctlCLM' z0 (ε / 2) f _).analyticAt _).comp (kern_analyticAt z0 hr))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  rw [fctlCLM'_kern hr hS hz, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end UpperTheory.Esk.OrbitalSingularIntegrals

open UpperTheory.Esk.OrbitalSingularIntegrals in
theorem UpperTheory.Esk.pf_Osg : UpperTheory.Esk.Osg := by
  intro I _ _ U hU f hf hsep
  set n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let Φ : (Fin n → ℂ) → (I → ℂ) := fun w i => w (e i)
  have hΦ : Continuous Φ := continuous_pi fun i => continuous_apply (e i)
  let g : (Fin n → ℂ) → ℂ := fun w => f (Φ w)
  let V : Set (Fin n → ℂ) := Φ ⁻¹' U
  have hV : IsOpen V := hU.preimage hΦ
  have hupd : ∀ (w : Fin n → ℂ) (j : Fin n) (t : ℂ), Φ (Function.update w j t) = Function.update (Φ w) (e.symm j) t := by
    intro w j t
    funext i
    by_cases h : i = e.symm j
    · subst h
      simp [Φ]
    · have h' : e i ≠ j := fun h' => h (by rw [← h']; simp)
      simp [Φ, h, h']
  have hg : SepHol g V := by
    refine ⟨hf.comp hΦ.continuousOn (fun w hw => hw), fun w hw j => ?_⟩
    have h1 := hsep (Φ w) hw (e.symm j)
    have e1 : (fun t => g (Function.update w j t)) = fun t => f (Function.update (Φ w) (e.symm j) t) := by
      funext t
      simp only [g, hupd]
    rw [e1]
    simpa [Φ] using h1
  have hA := osgFin V hV g hg
  let Ψ : (I → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  have hΨ : ∀ z, Φ (Ψ z) = z := by
    intro z
    funext i
    simp [Φ, Ψ]
  intro z hz
  have hmem : Ψ z ∈ V := by
    show Φ (Ψ z) ∈ U
    rw [hΨ]
    exact hz
  have h2 := (hA (Ψ z) hmem).comp (Ψ.analyticAt z)
  have hfe : g ∘ Ψ = f := by
    funext w
    simp only [Function.comp, g, hΨ]
  rwa [hfe] at h2
