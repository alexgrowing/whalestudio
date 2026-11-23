import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKF.E

theorem exists_exp {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (m : ℝ → A) (hc : Continuous m)
    (h0 : m 0 = 1) (hm : ∀ s t, m (s + t) = m s * m t) : ∃ X : A, ∀ t, m t = NormedSpace.exp (t • X) := by
  have hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, m s) (m t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  obtain ⟨ε, hε, hu⟩ : ∃ ε : ℝ, 0 < ε ∧ IsUnit (∫ s in (0 : ℝ)..ε, m s) := by
    have h1 := (hasDerivAt_iff_tendsto_slope_zero.1 (hI 0))
    simp only [zero_add, intervalIntegral.integral_same, sub_zero, h0] at h1
    have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, IsUnit (t⁻¹ • ∫ s in (0 : ℝ)..t, m s) :=
      h1.eventually (Units.isOpen.mem_nhds isUnit_one)
    have h3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), IsUnit (t⁻¹ • ∫ s in (0 : ℝ)..t, m s) :=
      h2.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    obtain ⟨t, ht, ht0⟩ := (h3.and self_mem_nhdsWithin).exists
    refine ⟨t, ht0, ?_⟩
    have : (∫ s in (0 : ℝ)..t, m s) = algebraMap ℝ A t * (t⁻¹ • ∫ s in (0 : ℝ)..t, m s) := by
      rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
    rw [this]
    exact ((IsUnit.mk0 t (ne_of_gt ht0)).map (algebraMap ℝ A)).mul ht
  obtain ⟨B, hB⟩ := hu
  have key : ∀ t, m t = ((∫ s in (0 : ℝ)..(t + ε), m s) - ∫ s in (0 : ℝ)..t, m s) * (B⁻¹ : Aˣ) := fun t => by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have e : (∫ s in t..(t + ε), m s) = m t * B := by
      have e0 := (ContinuousLinearMap.mul ℝ A (m t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 ε)
      rw [hB, ← ContinuousLinearMap.mul_apply' ℝ A, ← e0]
      have := intervalIntegral.integral_comp_add_left m (a := 0) (b := ε) t
      rw [add_zero] at this
      rw [← this]
      simp [hm]
    rw [e, mul_assoc, Units.mul_inv, mul_one]
  set X : A := (m ε - 1) * (B⁻¹ : Aˣ) with hX
  have hd : ∀ t, HasDerivAt m (m t * X) t := fun t => by
    have h1 := (((hI (t + ε)).comp_add_const t ε).sub (hI t)).mul_const ((B⁻¹ : Aˣ) : A)
    have h2 : (m (t + ε) - m t) * ((B⁻¹ : Aˣ) : A) = m t * X := by rw [hX, hm, ← mul_assoc, mul_sub, mul_one]
    rw [h2] at h1
    exact h1.congr_of_eventuallyEq (.of_forall key)
  refine ⟨X, fun t => ?_⟩
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hg : ∀ s, HasDerivAt (fun s => m s * NormedSpace.exp (s • (-X))) 0 s := fun s => by
    have := (hd s).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-X) s)
    exact this.congr_deriv (by simp [mul_assoc])
  have hk : m t * NormedSpace.exp (t • (-X)) = 1 := by
    have := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
    simpa [h0] using this
  have h2 : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (((Commute.refl X).neg_left.smul_left t).smul_right t)]
    simp
  calc m t = m t * (NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X)) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, hk, one_mul]

variable {l : Type} [Fintype l] [DecidableEq l]

structure Impl (s : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (S : Sch l →ₗ[ℂ] Sch l) : Prop where
  norm : ∀ f, ‖(S f).toLp 2 volume‖ = ‖f.toLp 2 volume‖
  impl : ∀ w (f g : Sch l), ⇑g = rhoFun w f → ⇑(S g) = rhoFun (s w) (S f)

theorem Impl.inner {s} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S) (f g : Sch l) :
    inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  have e : ∀ (u v : Sch l) (c : ℂ), u.toLp 2 volume + c • v.toLp 2 volume = (u + c • v).toLp 2 volume := fun u v c => by
    simp only [← schwartzToL2_apply, map_add, map_smul]
  have e' : ∀ (u v : Sch l) (c : ℂ), u.toLp 2 volume - c • v.toLp 2 volume = (u - c • v).toLp 2 volume := fun u v c => by
    simp only [← schwartzToL2_apply, map_sub, map_smul]
  have e1 := e (S f) (S g) 1
  have e2 := e' (S f) (S g) 1
  have e3 := e f g 1
  have e4 := e' f g 1
  simp only [one_smul] at e1 e2 e3 e4
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4, e, e, e', e', ← map_add, ← map_sub,
    ← map_smul, ← map_add, ← map_sub, h.norm, h.norm, h.norm, h.norm]

theorem exists_rho (w : l ⊕ l → ℝ) (f : Sch l) : ∃ g : Sch l, ⇑g = rhoFun w f := by
  have ht : Function.HasTemperateGrowth (phase w) := by
    have h2 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2 :=
      (innerSL ℝ (qPart w)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    have h3 := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2
    convert h3 using 1
    funext x
    simp only [phase, Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  refine ⟨smulLeftCLM ℂ (phase w) (compSubConstCLM ℂ (-pPart w) f), ?_⟩
  funext x
  rw [smulLeftCLM_apply_apply ht]
  simp [rhoFun]

theorem toLp_rho {w : l ⊕ l → ℝ} {f g : Sch l} (h : ⇑g = rhoFun w f) : g.toLp 2 volume = rho w (f.toLp 2 volume) := by
  refine Lp.ext ((g.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho w _).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))).symm

theorem eq_of_inner {u v : Sch l} (h : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by
  apply injective_toLp 2 volume
  have := h (u - v)
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem Impl.dRho {s : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) (w : l ⊕ l → ℝ) (f : Sch l) : S (dRho w f) = dRho (s w) (S f) := by
  refine eq_of_inner fun φ => ?_
  obtain ⟨φ', rfl⟩ := hs φ
  have d1 := hasDerivAt_inner_rho w φ' f
  have d2 := hasDerivAt_inner_rho (s w) (S φ') (S f)
  rw [h.inner]
  refine d1.unique (d2.congr_of_eventuallyEq (.of_forall fun t => ?_))
  obtain ⟨g, hg⟩ := exists_rho (t • w) f
  simp only
  rw [← toLp_rho hg, ← map_smul, ← toLp_rho (h.impl _ _ _ hg), h.inner]

theorem Impl.continuous {s : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) : Continuous S := by
  have hA : ∀ A ∈ weylAlg l, ∃ A' : Sch l →L[ℂ] Sch l, ∀ f, A (S f) = S (A' f) := fun A hA => by
    refine weylAlg_induction (P := fun A => ∃ A' : Sch l →L[ℂ] Sch l, ∀ f, A (S f) = S (A' f)) ⟨1, fun _ => rfl⟩ ?_
      ⟨0, fun f => by simp⟩ ?_ ?_ hA
    · rintro A w ⟨A', h'⟩
      refine ⟨A' * GlobalTheory.RealWeil.dRho (s.symm w), fun f => ?_⟩
      have := Impl.dRho (s := s.toLinearMap) h hs (s.symm w) f
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← this, h']
    · rintro A B ⟨A', h1⟩ ⟨B', h2⟩
      exact ⟨A' + B', fun f => by simp [h1, h2]⟩
    · rintro c A ⟨A', h1⟩
      exact ⟨c • A', fun f => by simp [h1]⟩
  refine (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_of_continuous_comp S fun kn => ?_
  obtain ⟨A, hAm, hb⟩ := exists_seminorm_le (l := l) kn.1 kn.2
  choose A' hA' using fun r => hA _ (hAm r)
  refine Seminorm.continuous_of_continuousAt_zero (𝕝 := ℂ) ?_
  have hc : Continuous fun f : Sch l => ∑ r, ‖schwartzToL2 l (A' r f)‖ := by fun_prop
  have h0 := hc.tendsto 0
  simp only [map_zero, norm_zero, Finset.sum_const_zero] at h0
  rw [ContinuousAt, map_zero]
  refine squeeze_zero (fun f => apply_nonneg _ _) (fun f => ?_) h0
  have := hb (S f)
  simp only [hA', h.norm] at this
  exact this

theorem exists_ne_zero (x : EuclideanSpace ℝ l) : ∃ φ : Sch l, φ x ≠ 0 := by
  obtain ⟨f, h1, h2, h3, -, h4⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := Set.univ) (x := x) Filter.univ_mem
  refine ⟨(h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).toSchwartzMap (ofRealCLM.contDiff.comp h3), ?_⟩
  show ((f x : ℝ) : ℂ) ≠ 0
  simp [h4]

theorem Impl.scalar {S : Sch l →ₗ[ℂ] Sch l} (h : Impl id S) (hs : Function.Surjective S) : ∃ c : ℂ, ∀ f, S f = c • f := by
  have h1 : ∀ (φ f : Sch l) x, (starRingEnd ℂ) (S φ x) * S f x = (starRingEnd ℂ) (φ x) * f x := fun φ f x => by
    have key : ∀ (a b : Sch l) (q : EuclideanSpace ℝ l) (g : Sch l), ⇑g = rhoFun (Sum.elim 0 fun i => -q i) b →
        Inner.inner ℂ (a.toLp 2 volume) (g.toLp 2 volume) = 𝓕 (fun x => (starRingEnd ℂ) (a x) * b x) q := fun a b q g hg => by
      rw [toLp_rho hg, inner_toLp_rho, Real.fourier_eq']
      refine integral_congr_ae (.of_forall fun y => ?_)
      have e1 : pPart (l := l) (Sum.elim 0 fun i => -q i) = 0 := rfl
      have e2 : qPart (l := l) (Sum.elim 0 fun i => -q i) = -q := rfl
      simp only [rhoFun, phase, e1, e2, inner_zero_left, mul_zero, add_zero, inner_neg_left, smul_eq_mul, RCLike.inner_apply,
        real_inner_comm y q]
      push_cast
      ring_nf
    have hi : ∀ a b : Sch l, Integrable (fun x => (starRingEnd ℂ) (a x) * b x) ∧
        Continuous (fun x => (starRingEnd ℂ) (a x) * b x) := fun a b =>
      ⟨b.integrable.bdd_mul (c := SchwartzMap.seminorm ℂ 0 0 a) (continuous_conj.comp a.continuous).aestronglyMeasurable
        (.of_forall fun x => by simpa using a.norm_le_seminorm ℂ x), (continuous_conj.comp a.continuous).mul b.continuous⟩
    set u := fun x => (starRingEnd ℂ) (S φ x) * S f x - (starRingEnd ℂ) (φ x) * f x with hu
    have hz : 𝓕 u = 0 := by
      funext q
      obtain ⟨g, hg⟩ := exists_rho (Sum.elim 0 fun i => -q i) f
      have := h.inner φ g
      rw [key _ _ q _ (h.impl _ _ _ hg), key _ _ q _ hg, Real.fourier_eq', Real.fourier_eq'] at this
      rw [Real.fourier_eq', hu]
      simp only [smul_sub]
      have hb : ∀ a b : Sch l, Integrable fun v => cexp (((-2 * π * ⟪v, q⟫ : ℝ) : ℂ) * I) • ((starRingEnd ℂ) (a v) * b v) :=
        fun a b => (hi a b).1.bdd_mul (c := 1) (by fun_prop) (.of_forall fun v => (norm_exp_ofReal_mul_I _).le)
      rw [integral_sub (hb _ _) (hb _ _), this, sub_self]
      rfl
    have := Continuous.fourierInv_fourier_eq (f := u) ((hi _ _).2.sub (hi _ _).2) ((hi _ _).1.sub (hi _ _).1)
      (by rw [hz]; exact integrable_zero _ _ _)
    rw [hz] at this
    have h3 := congrFun this x
    rw [Real.fourierInv_eq] at h3
    simp only [Pi.zero_apply, smul_zero, integral_zero] at h3
    exact sub_eq_zero.1 h3.symm
  have h2 : ∀ x, ∃ m : ℂ, ∀ f : Sch l, S f x = m * f x := fun x => by
    obtain ⟨φ, hφ⟩ := exists_ne_zero x
    obtain ⟨φ', rfl⟩ := hs φ
    have hn : (starRingEnd ℂ) (S φ' x) ≠ 0 := by simpa using hφ
    refine ⟨(starRingEnd ℂ) (φ' x) / (starRingEnd ℂ) (S φ' x), fun f => ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hn, mul_comm, h1]
  obtain ⟨m, hm⟩ := h2 0
  refine ⟨m, fun f => SchwartzMap.ext fun x => ?_⟩
  obtain ⟨g, hg⟩ := exists_rho (Sum.elim (fun i => x i) 0) f
  have e1 : pPart (l := l) (Sum.elim (fun i => x i) 0) = x := rfl
  have e2 : qPart (l := l) (Sum.elim (fun i => x i) 0) = 0 := rfl
  have := hm g
  rw [h.impl _ _ _ hg, hg] at this
  simpa [rhoFun, phase, e1, e2] using this

theorem quad_mem (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : quad X ∈ weylAlg l :=
  Subalgebra.smul_mem _ (sum_mem fun _ _ => sum_mem fun _ _ => Subalgebra.smul_mem _
    (add_mem (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _))) _) _

theorem sympl_eq (w u : l ⊕ l → ℝ) : sympl w u = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ u) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Matrix.one_apply, Fintype.sum_sum_type,
    mul_comm, sub_eq_add_neg, add_comm]

theorem exists_lift (hP : GlobalTheory.Published.RealMetaplecticRepresentation) {X : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) : ∃ (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l →L[ℂ] Sch l), Q ∈ weylAlg l ∧
      (∀ f, U 0 f = f) ∧ (∀ s t f, U (s + t) f = U s (U t f)) ∧
      (∀ t, Impl (fun w => NormedSpace.exp (t • X) *ᵥ w) (U t).toLinearMap) ∧
      (∀ f, Continuous fun t => (U t f).toLp 2 volume) ∧
      ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (U t f)) (lam (Q f)) 0 := by
  rcases isEmpty_or_nonempty l with hl | hl
  · refine ⟨fun _ => 1, 0, zero_mem _, fun _ => rfl, fun _ _ _ => rfl, fun t => ⟨fun _ => rfl, fun w f g hg => ?_⟩,
      fun _ => continuous_const, fun f lam => by simpa using hasDerivAt_const _ _⟩
    rw [Subsingleton.elim (NormedSpace.exp (t • X) *ᵥ w) w]
    exact hg
  obtain ⟨G, _, _, _, pr, om, omS, -, h2, h3, h4, h5, h6⟩ := hP l
  obtain ⟨γ, hc, h0, hm, hγ, hd⟩ := h6 X hX
  refine ⟨fun t => omS (γ t), quad X, quad_mem X, fun f => by simp [h0], fun s t f => by simp [hm], fun t => ⟨fun f => ?_,
    fun w f g hg => ?_⟩, fun f => ?_, fun f lam => (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hγ hd f⟩
  · show ‖(omS (γ t) f).toLp 2 volume‖ = _
    rw [← h4, LinearIsometryEquiv.norm_map]
  · obtain ⟨g', hg'⟩ := exists_rho (NormedSpace.exp (t • X) *ᵥ w) (omS (γ t) f)
    have : omS (γ t) g = g' := by
      apply injective_toLp 2 volume
      show (omS (γ t) g).toLp 2 volume = g'.toLp 2 volume
      rw [← h4, toLp_rho hg, toLp_rho hg', h3, hγ, h4]
    exact this ▸ hg'
  · simp only [← h4]
    exact (h2 _).comp hc

theorem lie (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by
  have hm : ∃ X : Matrix (l ⊕ l) (l ⊕ l) ℝ, ∀ t, LinearMap.toMatrix' (s t) = NormedSpace.exp (t • X) := by
    letI := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
    haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
    refine exists_exp (fun t => LinearMap.toMatrix' (s t)) ?_ ?_ fun t u => ?_
    · refine continuous_matrix fun a b => ?_
      simp only [LinearMap.toMatrix'_apply]
      exact (continuous_apply a).comp (sc _)
    · rw [show s 0 = LinearMap.id from LinearMap.ext s0, LinearMap.toMatrix'_id]
    · rw [show s (t + u) = s t ∘ₗ s u from LinearMap.ext (sm t u), LinearMap.toMatrix'_comp]
  obtain ⟨X, hX⟩ := hm
  have hs : ∀ t w, s t w = NormedSpace.exp (t • X) *ᵥ w := fun t w => by rw [← hX, LinearMap.toMatrix'_mulVec]
  have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
    refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
    show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X)
    ext a b
    have h1 : ∀ t : ℝ, ∑ i, ∑ j, NormedSpace.exp (t • X) i a * (Matrix.J l ℝ i j * NormedSpace.exp (t • X) j b) =
        Matrix.J l ℝ a b := fun t => by
      have := ss t (Pi.single a 1) (Pi.single b 1)
      rw [sympl_eq, sympl_eq, neg_inj, hs, hs] at this
      simpa [dotProduct, mulVec, Finset.mul_sum, Pi.single_apply, mul_add] using this
    have h2 : HasDerivAt (fun t : ℝ => ∑ i, ∑ j, NormedSpace.exp (t • X) i a *
        (Matrix.J l ℝ i j * NormedSpace.exp (t • X) j b)) _ 0 :=
      HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
        (hasDerivAt_exp_apply X i a).fun_mul ((hasDerivAt_exp_apply X j b).const_mul _)
    simp only [h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    simp only [zero_smul, NormedSpace.exp_zero, Finset.sum_add_distrib, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at h3
    simp only [Matrix.mul_apply, transpose_apply, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    linarith
  obtain ⟨U, Q, hQ, U0, Um, Ui, Uc, Ud⟩ := exists_lift hP hsp
  have hc : ∀ t, ∃ c : ℂ, ∀ f, S t f = c • U t f := fun t => by
    have hi : Impl id (S t ∘ₗ (U (-t)).toLinearMap) := ⟨fun f => ((hS t).norm _).trans ((Ui (-t)).norm f), fun w f g hg => by
      have := (hS t).impl _ _ _ ((Ui (-t)).impl w f g hg)
      rw [← hs, ← sm, add_neg_cancel, s0] at this
      exact this⟩
    obtain ⟨c, hc⟩ := hi.scalar fun f => ⟨U t (S (-t) f), by
      show S t (U (-t) (U t _)) = f
      rw [← Um, neg_add_cancel, U0, ← Sm, add_neg_cancel, S0]⟩
    refine ⟨c, fun f => ?_⟩
    rw [← hc]
    show _ = S t (U (-t) (U t f))
    rw [← Um, neg_add_cancel, U0]
  choose c hc using hc
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have hφ0 : φ ≠ 0 := fun h => hφ (by simp [h])
  have hU : ∀ t, U t φ ≠ 0 := fun t h => hφ0 (by rw [← U0 φ, ← neg_add_cancel t, Um, h, map_zero])
  have c0 : c 0 = 1 := by
    have := hc 0 φ
    rw [S0, U0] at this
    exact (smul_left_injective ℂ hφ0 (this.symm.trans (one_smul _ _).symm))
  have cm : ∀ t u, c (t + u) = c t * c u := fun t u => by
    have := Sm t u φ
    rw [hc, hc, hc, map_smul, smul_smul, ← Um] at this
    exact smul_left_injective ℂ (hU _) this
  have cc : Continuous c := continuous_iff_continuousAt.2 fun t₀ => by
    let lam : Sch l →L[ℂ] ℂ := (innerSL ℂ ((U t₀ φ).toLp 2 volume)).comp (schwartzToL2 l)
    have h1 : Continuous fun t => lam (U t φ) := (innerSL ℂ ((U t₀ φ).toLp 2 volume)).continuous.comp (Uc φ)
    have h2 : lam (U t₀ φ) ≠ 0 := fun h => hU t₀ (by
      apply injective_toLp 2 volume
      have : (U t₀ φ).toLp 2 volume = 0 := inner_self_eq_zero.1 h
      exact this.trans (map_zero (schwartzToL2 l)).symm)
    refine ((Sc φ lam).continuousAt.div h1.continuousAt h2).congr ?_
    filter_upwards [h1.continuousAt.eventually_ne h2] with t ht
    simp only [Pi.div_apply, hc, map_smul, smul_eq_mul]
    rw [mul_div_cancel_right₀ _ ht]
  obtain ⟨z, hz⟩ := exists_exp c cc c0 cm
  have hd : HasDerivAt c z 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) z (0 : ℝ)
    simp only [← hz, c0, one_mul] at this
    exact this
  refine ⟨z • 1 + Q, add_mem (Subalgebra.smul_mem _ (one_mem _) _) hQ, fun f lam => ?_⟩
  simp only [hc, map_smul, smul_eq_mul]
  refine (hd.fun_mul (Ud f lam)).congr_deriv ?_
  simp [c0, U0]

end CompanionTheory.ThKF.E
