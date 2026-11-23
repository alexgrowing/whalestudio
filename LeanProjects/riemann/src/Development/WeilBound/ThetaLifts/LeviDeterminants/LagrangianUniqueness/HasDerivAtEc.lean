import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.RealTest
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DenseHasCompactSupport

open Complex MeasureTheory
open scoped Real ContDiff RealInnerProductSpace FourierTransform

noncomputable section

namespace PositivityTheory.ThKF0.RealL

def ec (t : ℝ) : ℂ := cexp (2 * π * I * (t : ℂ))

theorem ec_add (s t : ℝ) : ec (s + t) = ec s * ec t := by
  simp only [ec, ofReal_add, mul_add, Complex.exp_add]

theorem ec_zero : ec 0 = 1 := by simp [ec]

theorem norm_ec (t : ℝ) : ‖ec t‖ = 1 := by
  rw [ec, show 2 * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

theorem hasDerivAt_ec (c : ℂ) (t : ℝ) : HasDerivAt (fun s => c * ec s) (c * (2 * π * I) * ec t) t := by
  have h : HasDerivAt (fun s : ℝ => 2 * π * I * (s : ℂ)) (2 * π * I) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * π * I)
  have := h.cexp.const_mul c
  exact this.congr_deriv (by simp only [ec]; ring)

theorem ec_temp : ec.HasTemperateGrowth := by
  refine ⟨(contDiff_const.mul Complex.ofRealCLM.contDiff).cexp, fun n => ⟨0, ‖(2 * π * I : ℂ) ^ n‖, fun x => ?_⟩⟩
  have h : iteratedDeriv n ec = fun s => (2 * π * I : ℂ) ^ n * ec s := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(hasDerivAt_ec _ s).deriv, pow_succ]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, h, norm_mul, norm_ec]
  simp

section Phase

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ph (q : V → ℝ) : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ := SchwartzMap.smulLeftCLM ℂ (fun x => ec (q x))

theorem ph_apply {q : V → ℝ} (hq : q.HasTemperateGrowth) (f : SchwartzMap V ℂ) (x : V) : ph q f x = ec (q x) * f x :=
  SchwartzMap.smulLeftCLM_apply_apply (ec_temp.comp hq) f x

theorem ph_surj {q : V → ℝ} (hq : q.HasTemperateGrowth) : Function.Surjective (ph q) := fun f =>
  ⟨ph (fun x => -q x) f, by
    ext x
    rw [ph_apply hq, ph_apply hq.fun_neg, ← mul_assoc, ← ec_add, add_neg_cancel, ec_zero, one_mul]⟩

end Phase

theorem delta_pi (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hT : ∀ (i : Fin n) (c : ℝ) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = ec (c * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : HasCompactSupport (f : (Fin n → ℝ) → ℂ)) (h0 : f 0 = 0) : T f = 0 := by
  obtain ⟨R, hR0, hR⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) R hR0.ne').toContinuousLinearEquiv
  have he : ∀ x, e x = R • x := fun x => rfl
  have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => by
    rw [ContinuousLinearEquiv.symm_apply_eq, he, smul_inv_smul₀ hR0.ne']
  let f₁ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hs : tsupport (f₁ : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 := by
    intro x hx
    have h1 : e x ∈ tsupport (f : (Fin n → ℝ) → ℂ) :=
      tsupport_comp_subset_preimage (f : (Fin n → ℝ) → ℂ) e.continuous hx
    have h2 := mem_ball_zero_iff.1 (hR h1)
    rw [he, norm_smul, Real.norm_of_nonneg hR0.le] at h2
    exact mem_ball_zero_iff.2 (by nlinarith)
  obtain ⟨g, -, hg⟩ := GlobalTheory.CompanionTheory.DiracComb.exists_div n f₁ hs (by
    show f (e 0) = 0
    rw [map_zero, h0])
  let G := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm (g i)
  have ht : ∀ i : Fin n, (fun x : Fin n → ℝ => R⁻¹ * x i).HasTemperateGrowth := fun i =>
    (R⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasTemperateGrowth
  have e1 : f = ∑ i, (ph (fun x => R⁻¹ * x i) (G i) - G i) := by
    ext x
    have := hg (e.symm x)
    change f (e (e.symm x)) = _ at this
    rw [e.apply_symm_apply] at this
    rw [this, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_apply, ph_apply (ht i), sub_mul, one_mul, he']
    rfl
  rw [e1, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_sub, hT i R⁻¹ (G i) _ (ph_apply (ht i) _), sub_self]

theorem test_pi (n : ℕ) : ∃ f₀ : SchwartzMap (Fin n → ℝ) ℂ, ∀ T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ,
    (∀ (i : Fin n) (c : ℝ) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = ec (c * x i) * f x) → T g = T f) →
    T f₀ = 0 → T = 0 := by
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) := b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ := h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ0 : ψ 0 = 1 := by
    show ((b 0 : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨ψ, fun T hT h0 => ?_⟩
  have hψ : HasCompactSupport (ψ : (Fin n → ℝ) → ℂ) := h₁
  have key : Set.EqOn T (0 : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
      {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := by
    intro f hf
    have hc : HasCompactSupport ((f - f 0 • ψ : SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) := by
      have : ((f - f 0 • ψ : SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) =
          (f : (Fin n → ℝ) → ℂ) + (fun _ => -f 0) * (ψ : (Fin n → ℝ) → ℂ) := by
        funext x
        show f x - f 0 * ψ x = f x + -f 0 * ψ x
        ring
      rw [this]
      exact HasCompactSupport.add hf hψ.mul_left
    have := delta_pi n T hT _ hc (by
      show f 0 - f 0 * ψ 0 = 0
      rw [hψ0, mul_one, sub_self])
    rwa [map_sub, map_smul, h0, smul_zero, sub_zero] at this
  exact ContinuousLinearMap.ext (congrFun
    (Continuous.ext_on (GlobalTheory.CompanionTheory.DiracComb.dense_hasCompactSupport n) T.continuous (0 : _ →L[ℂ] ℂ).continuous key))

section Inner

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def Rel (w : E × E) (f g : SchwartzMap E ℂ) : Prop := ∀ z, g z = ec (⟪z, w.2⟫ + ⟪w.1, w.2⟫ / 2) * f (z + w.1)

def Test (S : Set (E × E)) : Prop := ∃ f₀ : SchwartzMap E ℂ, ∀ T : SchwartzMap E ℂ →L[ℂ] ℂ,
  (∀ w ∈ S, ∀ f g, Rel w f g → T g = T f) → T f₀ = 0 → T = 0

omit [FiniteDimensional ℝ E] in
theorem Test.map {S S' : Set (E × E)} (h : Test S) (U : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ) (hU : Function.Surjective U)
    (φ : E × E → E × E) (hφ : ∀ w f g, Rel w f g → Rel (φ w) (U f) (U g)) (hS : ∀ w ∈ S, φ w ∈ S') : Test S' := by
  obtain ⟨f₀, h⟩ := h
  refine ⟨U f₀, fun T hT h0 => ?_⟩
  have := h (T.comp U) (fun w hw f g hr => hT _ (hS w hw) _ _ (hφ w f g hr)) h0
  ext f
  obtain ⟨f, rfl⟩ := hU f
  exact DFunLike.congr_fun this f

theorem test_Y : Test {w : E × E | w.1 = 0} := by
  let B := stdOrthonormalBasis ℝ E
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := B.toBasis.equivFun.toContinuousLinearEquiv
  have he : ∀ x i, e x i = ⟪x, B i⟫ := fun x i => by
    rw [real_inner_comm, ← B.repr_apply_apply]; rfl
  obtain ⟨f₀, h⟩ := test_pi (Module.finrank ℝ E)
  let U := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
  refine ⟨U f₀, fun T hT h0 => ?_⟩
  have := h (T.comp U) (fun i c f g hr => hT (0, c • B i) rfl _ _ fun z => by
    show g (e z) = _ * f (e (z + 0))
    rw [hr, he, add_zero, inner_zero_left, zero_div, add_zero, inner_smul_right]) h0
  ext f
  have hf : U (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f) = f := by
    ext x
    show f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  rw [← hf]
  exact DFunLike.congr_fun this _

theorem Test.fourier {S S' : Set (E × E)} (h : Test S) (hS : ∀ w ∈ S, (-w.2, w.1) ∈ S') : Test S' := by
  borelize E
  refine h.map (SchwartzMap.fourierTransformCLM ℂ) (fun f => ⟨𝓕⁻ f,
    (SchwartzMap.fourierTransformCLM_apply ℂ _).trans (FourierTransform.fourier_fourierInv_eq f)⟩)
    (fun w => (-w.2, w.1)) (fun w f g hr ξ => ?_) hS
  obtain ⟨x, y⟩ := w
  change 𝓕 (g : E → ℂ) ξ = ec (⟪ξ, x⟫ + ⟪-y, x⟫ / 2) * 𝓕 (f : E → ℂ) (ξ + -y)
  have hec : ∀ t : ℝ, cexp (((-2 * π * t : ℝ) : ℂ) * I) = ec (-t) := fun t => by
    rw [ec]; congr 1; push_cast; ring
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul,
    ← integral_add_right_eq_self (fun v => ec (⟪ξ, x⟫ + ⟪-y, x⟫ / 2) * (cexp (((-2 * π * ⟪v, ξ + -y⟫ : ℝ) : ℂ) * I) • f v)) x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [hec, hr v, smul_eq_mul, ← mul_assoc, ← ec_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_comm x]
  ring

theorem Test.shear {S S' : Set (E × E)} (h : Test S) (b : E →ₗ[ℝ] E) (hb : ∀ x y, ⟪x, b y⟫ = ⟪y, b x⟫)
    (hS : ∀ w ∈ S, (w.1, w.2 + b w.1) ∈ S') : Test S' := by
  have ht : (fun z : E => -(⟪z, b z⟫ / 2)).HasTemperateGrowth := by
    have h1 := (innerSL ℝ (E := E)).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id'
      (LinearMap.toContinuousLinearMap b).hasTemperateGrowth
    have h2 := (Function.HasTemperateGrowth.const (E := E) (-(1 / 2) : ℝ)).mul h1
    have h3 : (fun z : E => -(⟪z, b z⟫ / 2)) = (fun _ => -(1 / 2)) * fun z : E => ⟪z, b z⟫ := by
      funext z
      simp only [Pi.mul_apply]
      ring
    rw [h3]
    exact h2
  refine h.map (ph _) (ph_surj ht) (fun w => (w.1, w.2 + b w.1)) (fun w f g hr z => ?_) hS
  simp only [ph_apply ht, hr z, ← mul_assoc, ← ec_add]
  congr 2
  simp only [map_add, inner_add_left, inner_add_right, hb w.1 z]
  ring

theorem test_lag (P : Submodule ℝ E) (b : E →ₗ[ℝ] E) (hb : ∀ x y, ⟪x, b y⟫ = ⟪y, b x⟫) :
    Test {w : E × E | ∃ p ∈ P, ∃ q ∈ Pᗮ, w = (p, b p + q)} := by
  let pr : E →ₗ[ℝ] E := P.starProjection.toLinearMap
  have hpr : ∀ x y, ⟪x, pr y⟫ = ⟪y, pr x⟫ := fun x y => by
    show ⟪x, P.starProjection y⟫ = ⟪y, P.starProjection x⟫
    rw [← P.inner_starProjection_left_eq_right, real_inner_comm]
  have h1 : Test {w : E × E | w.2 = 0} := test_Y.fourier fun w hw => hw
  have h2 : Test {w : E × E | w.2 = -pr w.1} := h1.shear (-pr) (fun x y => by simp [inner_neg_right, hpr x y])
    fun w hw => by simp [show w.2 = 0 from hw]
  have h3 : Test {w : E × E | w.1 = pr w.2} := h2.fourier fun w hw => by simp [show w.2 = _ from hw]
  refine h3.shear (b - pr) (fun x y => by simp [inner_sub_right, hpr x y, hb x y]) fun w hw => ?_
  have hw : w.1 = pr w.2 := hw
  have hp : w.1 ∈ P := hw ▸ P.starProjection_apply_mem _
  have hpp : pr w.1 = w.1 := P.starProjection_eq_self_iff.2 hp
  refine ⟨w.1, hp, w.2 - pr w.2, P.sub_starProjection_mem_orthogonal _, ?_⟩
  rw [LinearMap.sub_apply, hpp, ← hw]
  congr 1
  abel

end Inner

end PositivityTheory.ThKF0.RealL

namespace PositivityTheory.ThKF0

open RealL

theorem realTest : RealTest := by
  intro V _ _ _ P b hb
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃L[ℝ] E := toEuclidean
  let β : E → E := fun u => (InnerProductSpace.toDual ℝ E).symm
    (LinearMap.toContinuousLinearMap (b (e.symm u) ∘ₗ e.symm.toLinearEquiv.toLinearMap))
  have hβ : ∀ u v, ⟪v, β u⟫ = b (e.symm v) (e.symm u) := fun u v => by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, hb]; rfl
  let B : E →ₗ[ℝ] E :=
    { toFun := β
      map_add' := fun u u' => ext_inner_left ℝ fun v => by simp only [hβ, inner_add_right, map_add]
      map_smul' := fun c u => ext_inner_left ℝ fun v => by
        simp only [hβ, inner_smul_right, map_smul, RingHom.id_apply, smul_eq_mul] }
  have hB : ∀ u v, ⟪v, B u⟫ = b (e.symm v) (e.symm u) := hβ
  obtain ⟨f₀, h⟩ := test_lag (P.map e.toLinearEquiv.toLinearMap) B fun x y => by rw [hB, hB, hb]
  let U := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
  have hU : ∀ f x, U f x = f (e x) := fun _ _ => rfl
  refine ⟨U f₀, fun T h1 h2 h0 => ?_⟩
  have := h (T.comp U) (by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, q, hq, rfl⟩ f g hr
    change T (U g) = T (U f)
    let l : V →L[ℝ] ℝ := (innerSL ℝ q).comp (e : V →L[ℝ] E)
    have hl : ∀ x, l x = ⟪q, e x⟫ := fun _ => rfl
    have hl0 : ∀ p ∈ P, l p = 0 := fun p hp => by
      rw [hl, real_inner_comm]
      exact hq _ ⟨p, hp, rfl⟩
    have ht : (fun x => -l x).HasTemperateGrowth := l.hasTemperateGrowth.fun_neg
    rw [h2 l.toLinearMap hl0 (ph (fun x => -l x) (U g)) (U g) fun x => by
      change _ = ec (l x) * _
      rw [ph_apply ht, ← mul_assoc, ← ec_add, add_neg_cancel, ec_zero, one_mul]]
    refine h1 p hp _ _ fun x => ?_
    change _ = ec _ * _
    have h3 := hr (e x)
    change g (e x) = ec (⟪e x, B (e p) + q⟫ + ⟪e p, B (e p) + q⟫ / 2) * f (e x + e p) at h3
    have h4 : ⟪e p, q⟫ = 0 := by rw [real_inner_comm, ← hl, hl0 p hp]
    rw [ph_apply ht, hU, hU, h3, map_add e, ← mul_assoc, ← ec_add, hl]
    congr 2
    simp only [inner_add_right, hB, e.symm_apply_apply, h4, real_inner_comm q]
    ring) h0
  ext f
  have hf : U (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f) = f := by
    ext x
    show f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  rw [← hf]
  exact DFunLike.congr_fun this _

end PositivityTheory.ThKF0
