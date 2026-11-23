import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHasDerivAtZeroOfMapAddMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoSlopeMetaplecticLiftSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalarStatement

open scoped Matrix

noncomputable section

namespace GlobalTheory.MetaplecticScalarDeriv

open MeasureTheory Filter Topology GlobalTheory.RealWeil

theorem exists_schwartz_one (l : Type) [Fintype l] : ∃ f : Sch l, f 0 = 1 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ l) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem lintegral_sq_eq (l : Type) [Fintype l] (f : Sch l) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = eLpNorm (⇑(f.toLp 2 : L2 l)) 2 volume ^ 2 := by
  rw [eLpNorm_congr_ae (f.coeFn_toLp 2 volume), eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
  have := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := ⇑f) (μ := volume) (q := 2) two_pos
  simpa [ENNReal.toReal_ofNat] using this

theorem continuous_eval (l : Type) [Fintype l] (x : EuclideanSpace ℝ l) : Continuous fun f : Sch l => f x :=
  ((BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).continuous

theorem continuous_rhoFun (l : Type) [Fintype l] (w : l ⊕ l → ℝ) {f : EuclideanSpace ℝ l → ℂ} (hf : Continuous f) :
    Continuous (rhoFun w f) :=
  (continuous_phase w).mul (hf.comp (continuous_add_right _))

theorem intertwine_fun (l : Type) [Fintype l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (U : L2 l ≃ₗᵢ[ℂ] L2 l)
    (S : Sch l →L[ℂ] Sch l) (h3 : ∀ (w : l ⊕ l → ℝ) (f : L2 l), U (rho w f) = rho (M *ᵥ w) (U f))
    (h4 : ∀ f : Sch l, U (f.toLp 2) = (S f).toLp 2) (w : l ⊕ l → ℝ) (h h₁ : Sch l) (hh : ⇑h₁ = rhoFun w ⇑h) :
    ⇑(S h₁) = rhoFun (M *ᵥ w) ⇑(S h) := by
  have e1 : (h₁.toLp 2 : L2 l) = rho w (h.toLp 2) := by
    refine Lp.ext ((h₁.coeFn_toLp 2 volume).trans ?_)
    rw [hh]
    exact (rhoFun_congr w (h.coeFn_toLp 2 volume).symm).trans (coeFn_rho w _).symm
  have e2 : ((S h₁).toLp 2 : L2 l) = rho (M *ᵥ w) ((S h).toLp 2) := by
    rw [← h4, e1, h3, h4]
  have e3 : ⇑(S h₁) =ᵐ[volume] rhoFun (M *ᵥ w) ⇑(S h) := by
    refine ((S h₁).coeFn_toLp 2 volume).symm.trans ?_
    rw [e2]
    exact (coeFn_rho _ _).trans (rhoFun_congr _ ((S h).coeFn_toLp 2 volume))
  exact (Continuous.ae_eq_iff_eq volume (S h₁).continuous (continuous_rhoFun l _ (S h).continuous)).1 e3

theorem lintegral_iso (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l) (S : Sch l →L[ℂ] Sch l)
    (h4 : ∀ f : Sch l, U (f.toLp 2) = (S f).toLp 2) (h : Sch l) :
    ∫⁻ x, ‖S h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
  rw [lintegral_sq_eq, lintegral_sq_eq]
  congr 1
  have hn : ‖((S h).toLp 2 : L2 l)‖ = ‖(h.toLp 2 : L2 l)‖ := by rw [← h4, U.norm_map]
  rw [Lp.norm_def, Lp.norm_def] at hn
  exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).1 hn

theorem main_nonempty (hP : GlobalTheory.FunPr.Hypotheses₂) (l : Type) [Fintype l] [DecidableEq l] [Nonempty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hZ : Z ∈ LieAlgebra.Symplectic.sp l ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTrho : ∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h →
      ⇑(T t h₁) = rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h))
    (hTiso : ∀ (t : ℝ) (h : Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩ := hP.realMetaplecticRepresentation l
  obtain ⟨γ, -, hγ0, hγadd, hγpr, hγd⟩ := h6 Z hZ
  have hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f := by
    intro s t f
    rw [hγadd, map_mul]
    rfl
  have hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f := by
    intro t f
    rw [hmul, neg_add_cancel, hγ0, map_one]
    rfl
  have hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f := by
    intro t f
    rw [hmul, add_neg_cancel, hγ0, map_one]
    rfl
  have hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
    intro t w
    have e : pr (γ t) * pr (γ (-t)) = 1 := by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]
    have e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
      congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
    rw [← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
  have hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h := by
    intro t
    refine GlobalTheory.T.schwartz_unitary_intertwiner_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]
  choose ν _hνn hν using hU
  have hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f := by
    intro t f
    have := hν t (omS (γ t) f)
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1] using this
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hν0 : ν 0 = 1 := by
    have e := congrArg (fun g : Sch l => g 0) (hTν 0 f0)
    simp only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e
    change 1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e
    rw [ContinuousLinearMap.one_apply, hf0, mul_one] at e
    exact e.symm
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    set f := omS (γ (-(s + t))) f0
    have e1 : T (s + t) f = ν (s + t) • f0 := by rw [hTν, hS2]
    have e2 : T (s + t) f = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]
    have e := congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)
    simpa [hf0] using e
  have hcontS : ContinuousAt (fun t => omS (γ t) f0) 0 := by
    have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0) := by
      have h1' := h1.add_const f0
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]
    exact h2
  have hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0 := (continuous_eval l 0).continuousAt.comp hcontS
  have hS00 : omS (γ 0) f0 0 ≠ 0 := by
    rw [hγ0, map_one, ContinuousLinearMap.one_apply, hf0]
    exact one_ne_zero
  have hνc : ContinuousAt ν 0 := by
    have hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0 :=
      (hTcont f0 0).continuousAt.div hcontS0 hS00
    refine hq.congr ?_
    filter_upwards [hcontS0.eventually_ne hS00] with t ht
    rw [hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul hνc
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    rw [← hν0]
    exact hνc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hν1.smul hd).add (hslope.smul_const f)
  rw [one_smul, add_comm] at hlim
  refine hlim.congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem main_empty (l : Type) [Fintype l] [DecidableEq l] [IsEmpty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hsub : ∀ x : EuclideanSpace ℝ l, x = 0 := fun x => by
    ext i
    exact isEmptyElim i
  have hdec : ∀ f : Sch l, f = f 0 • f0 := by
    intro f
    ext x
    rw [hsub x, SchwartzMap.smul_apply, hf0, smul_eq_mul, mul_one]
  set ν : ℝ → ℂ := fun t => T t f0 0 with hνdef
  have hTν : ∀ t (f : Sch l), T t f = ν t • f := by
    intro t f
    have e : T t f = f 0 • T t f0 := by
      conv_lhs => rw [hdec f]
      exact map_smul _ _ _
    rw [e]
    ext x
    rw [hsub x]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hνdef]
    ring
  have hν0 : ν 0 = 1 := by
    simp only [hνdef, hT0, LinearMap.id_apply, hf0]
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    have e : T (s + t) f0 = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, smul_smul, mul_comm]
    have e' := congrArg (fun g : Sch l => g 0) e
    simpa [hf0, hνdef] using e'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul (hTcont f0 0).continuousAt
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hq : quad Z f = 0 := by simp [quad]
  rw [hq, add_zero]
  refine (hslope.smul_const f).congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  intro hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont
  rcases isEmpty_or_nonempty l with hl | hl
  · exact main_empty l Z T hT0 hTadd hTcont
  · exact main_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont

end GlobalTheory.MetaplecticScalarDeriv
