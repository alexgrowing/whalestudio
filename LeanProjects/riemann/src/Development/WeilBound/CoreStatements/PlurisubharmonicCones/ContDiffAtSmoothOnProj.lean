import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivializationStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (analyticAt_comp_symm_of_holoOn contDiffAt_comp_symm_of_smoothOn)

namespace LevelTowerAlt

theorem exists_local_inverse {m : ℕ} {f : (Fin m → ℂ) → Fin m → ℂ} {x : Fin m → ℂ} (hf : AnalyticAt ℂ f x)
    {U : Set (Fin m → ℂ)} (hU : U ∈ 𝓝 x) (hinj : Set.InjOn f U) :
    ∃ g : (Fin m → ℂ) → Fin m → ℂ, AnalyticAt ℂ g (f x) ∧ g (f x) = x ∧ (∀ᶠ y in 𝓝 (f x), f (g y) = y) ∧
      (∀ᶠ y in 𝓝 x, g (f y) = y) ∧ Function.Bijective (fderiv ℂ g (f x)) := by
  have hV : x ∈ interior (U ∩ {y | AnalyticAt ℂ f y}) :=
    mem_interior_iff_mem_nhds.2 (inter_mem hU hf.eventually_analyticAt)
  have hi : Function.Injective (fderiv ℂ f x) :=
    HoloInjDerivInj.proof m f _ isOpen_interior (fun y hy => (interior_subset hy).2)
      (hinj.mono fun y hy => (interior_subset hy).1) x hV
  let e : (Fin m → ℂ) ≃L[ℂ] (Fin m → ℂ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ f x : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) hi).toContinuousLinearEquiv
  have he : (e : (Fin m → ℂ) →L[ℂ] Fin m → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  have hs : HasStrictFDerivAt f (e : (Fin m → ℂ) →L[ℂ] Fin m → ℂ) x := by
    rw [he]
    exact hf.hasStrictFDerivAt
  refine ⟨hs.localInverse f e x, ?_, hs.localInverse_apply_image, hs.eventually_right_inverse,
    hs.eventually_left_inverse, ?_⟩
  · exact (hs.toOpenPartialHomeomorph f).analyticAt_symm' (i := e) hs.mem_toOpenPartialHomeomorph_source hf he.symm
  · rw [hs.to_localInverse.hasFDerivAt.fderiv]
    exact e.symm.bijective

theorem exists_log_re {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : E → ℂ} {u : E}
    (hT : AnalyticAt ℂ T u) (h0 : T u ≠ 0) :
    ∃ G : E → ℂ, AnalyticAt ℂ G u ∧ ∀ᶠ v in 𝓝 u, Real.log ‖T v‖ = (G v).re := by
  refine ⟨fun v => Complex.log (T v / T u) + (Real.log ‖T u‖ : ℝ),
    (AnalyticAt.clog (hT.div analyticAt_const h0) (by simp [div_self h0])).add analyticAt_const, ?_⟩
  filter_upwards [hT.continuousAt.eventually_ne h0] with v hv
  rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 h0)]
  ring

theorem compat_atlas {d : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas d X) (a : Fin A.n) :
    IsCompatChart A (A.chart a) := fun j => ⟨A.holo j a, A.holo a j⟩

section Model

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}

theorem analyticAt_torusSmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : E → K → ℂ}
    {g : E → (Σ k, J k) → ℂ} {u : E} (hc : ∀ k, AnalyticAt ℂ (fun v => c v k) u) (hg : AnalyticAt ℂ g u) :
    AnalyticAt ℂ (fun v => torusSmul (c v) (g v)) u :=
  analyticAt_pi_iff.2 fun p => (hc p.1).mul (analyticAt_pi_iff.1 hg p)

theorem proj_torusSmul (hP : IsMultiHomogIdeal P) (M : CxModel P n) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : M.proj (torusSmul c z) = M.proj z :=
  ((M.fibre z hz _ (VertFactorSmooth.torusSmul_mem_mcPts hP hz hc)).2 ⟨c, hc, rfl⟩).symm

theorem continuousAt_proj (M : CxModel P n) {E : Type*} [TopologicalSpace E] {g : E → (Σ k, J k) → ℂ} {u : E}
    (hg : ContinuousAt g u) (hm : ∀ᶠ v in 𝓝 u, g v ∈ mcPts P) : ContinuousAt (fun v => M.proj (g v)) u :=
  (M.cont (g u) hm.self_of_nhds).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hg, hm⟩)

theorem chart_local_gen (hP : IsMultiHomogIdeal P) (M : CxModel P n) {Bd : Set ((Σ k, J k) → ℂ)}
    (χ : SncChart P n Bd) {e : OpenPartialHomeomorph M.Xc (Fin n → ℂ)} (he : IsCompatChart M.atlas e)
    {t : Fin n → ℂ} (ht : t ∈ ball (0 : Fin n → ℂ) 1) (hsrc : M.proj (χ.γ t) ∈ e.source)
    (hT : ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ), IsOpen V ∧ χ.γ t ∈ V ∧
      AnalyticOnNhd ℂ T V ∧ T (χ.γ t) = t ∧ ∀ z ∈ V ∩ mcPts P, T z ∈ Metric.ball 0 1 ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (χ.γ (T z))) :
    AnalyticAt ℂ (fun t' => e (M.proj (χ.γ t'))) t ∧
      Function.Bijective (fderiv ℂ (fun t' => e (M.proj (χ.γ t'))) t) := by
  obtain ⟨V, T, hV, htV, hTa, hTt, hTV⟩ := hT
  obtain ⟨U, hU, hxU, s, hs, hsh⟩ := M.sections (M.proj (χ.γ t))
  obtain ⟨c₀, hc₀, hγ⟩ := (M.fibre _ (hs _ hxU).1 _ (χ.mem t ht)).1 (hs _ hxU).2
  set x₀ := M.proj (χ.γ t) with hx₀
  let σ : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun y => torusSmul c₀ (s (e.symm y))
  have hσa : AnalyticAt ℂ σ (e x₀) :=
    analyticAt_torusSmul (fun _ => analyticAt_const)
      (analyticAt_pi_iff.2 fun p => analyticAt_comp_symm_of_holoOn he (hsh p) hxU hsrc)
  have hσ0 : σ (e x₀) = χ.γ t := by
    show torusSmul c₀ (s (e.symm (e x₀))) = _
    rw [e.left_inv hsrc, ← hγ]
  have hΦa : AnalyticAt ℂ (fun y => T (σ y)) (e x₀) :=
    AnalyticAt.comp (g := T) (f := σ) (by rw [hσ0]; exact hTa _ htV) hσa
  have hΦ0 : T (σ (e x₀)) = t := by rw [hσ0, hTt]
  have hFΦ : ∀ᶠ y in 𝓝 (e x₀), e (M.proj (χ.γ (T (σ y)))) = y := by
    have h1 : ∀ᶠ y in 𝓝 (e x₀), y ∈ e.target := e.open_target.mem_nhds (e.map_source hsrc)
    have h2 : ∀ᶠ y in 𝓝 (e x₀), e.symm y ∈ U :=
      (e.continuousAt_symm (e.map_source hsrc)).eventually (hU.mem_nhds (by rw [e.left_inv hsrc]; exact hxU))
    have h3 : ∀ᶠ y in 𝓝 (e x₀), σ y ∈ V := hσa.continuousAt.eventually (hV.mem_nhds (by rw [hσ0]; exact htV))
    filter_upwards [h1, h2, h3] with y h1 h2 h3
    have hm : σ y ∈ mcPts P := VertFactorSmooth.torusSmul_mem_mcPts hP (hs _ h2).1 hc₀
    obtain ⟨hb, c, hc, hz⟩ := hTV _ ⟨h3, hm⟩
    have h4 : M.proj (χ.γ (T (σ y))) = M.proj (σ y) := (M.fibre _ (χ.mem _ hb) _ hm).2 ⟨c, hc, hz⟩
    have h5 : M.proj (σ y) = e.symm y := (proj_torusSmul hP M (hs _ h2).1 hc₀).trans (hs _ h2).2
    rw [h4, h5, e.right_inv h1]
  obtain ⟨g, hga, hg0, hgr, -, hgb⟩ := exists_local_inverse hΦa hFΦ fun y hy y' hy' h => by
    have h' : T (σ y) = T (σ y') := h
    have hy1 : e (M.proj (χ.γ (T (σ y)))) = y := hy
    have hy2 : e (M.proj (χ.γ (T (σ y')))) = y' := hy'
    rw [← hy1, ← hy2, h']
  simp only [hΦ0] at hga hg0 hgr hgb
  have heq : (fun t' => e (M.proj (χ.γ t'))) =ᶠ[𝓝 t] g := by
    have h1 : Tendsto g (𝓝 t) (𝓝 (e x₀)) := hg0 ▸ hga.continuousAt.tendsto
    filter_upwards [hgr, h1.eventually hFΦ] with t' h2 h3
    rw [h2] at h3
    exact h3
  exact ⟨hga.congr heq.symm, by rw [heq.fderiv_eq]; exact hgb⟩

end Model

section Component

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W) (M : XModel D)

theorem analyticAt_proj_gen {P : Ideal (MRing J)} {n : ℕ} (hP : IsMultiHomogIdeal P) (M : CxModel P n)
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {e : OpenPartialHomeomorph M.Xc (Fin n → ℂ)}
    (he : IsCompatChart M.atlas e) {t : Fin n → ℂ} (ht : t ∈ ball (0 : Fin n → ℂ) 1)
    (hT : ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ), IsOpen V ∧ χ.γ t ∈ V ∧
      AnalyticOnNhd ℂ T V ∧ T (χ.γ t) = t ∧ ∀ z ∈ V ∩ mcPts P, T z ∈ Metric.ball 0 1 ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (χ.γ (T z)))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → (Σ k, J k) → ℂ} {u : E} (hg : AnalyticAt ℂ g u)
    (hm : ∀ᶠ v in 𝓝 u, g v ∈ mcPts P) (hsrc : M.proj (g u) ∈ e.source)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (hgu : g u = torusSmul c (χ.γ t)) :
    AnalyticAt ℂ (fun v => e (M.proj (g v))) u := by
  have hF := (chart_local_gen hP M χ he ht
    (by rw [← proj_torusSmul hP M (χ.mem t ht) hc, ← hgu]; exact hsrc) hT).1
  obtain ⟨V, T, hV, htV, hTa, hTt, hTV⟩ := hT
  have hc' : ∀ k, c⁻¹ k ≠ 0 := fun k => inv_ne_zero (hc k)
  let g' : E → (Σ k, J k) → ℂ := fun v => torusSmul c⁻¹ (g v)
  have hg' : AnalyticAt ℂ g' u := analyticAt_torusSmul (fun _ => analyticAt_const) hg
  have hg0 : g' u = χ.γ t := by
    funext p
    show c⁻¹ p.1 * g u p = _
    rw [hgu]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  have h1 : AnalyticAt ℂ (fun v => T (g' v)) u :=
    AnalyticAt.comp (g := T) (f := g') (by rw [hg0]; exact hTa _ htV) hg'
  have h2 : AnalyticAt ℂ (fun v => e (M.proj (χ.γ (T (g' v))))) u :=
    AnalyticAt.comp (g := fun t' => e (M.proj (χ.γ t'))) (f := fun v => T (g' v)) (by rw [hg0, hTt]; exact hF) h1
  refine h2.congr ?_
  filter_upwards [hm, hg'.continuousAt.eventually (hV.mem_nhds (by rw [hg0]; exact htV))] with v hv hvV
  have hm' : g' v ∈ mcPts P := VertFactorSmooth.torusSmul_mem_mcPts hP hv hc'
  obtain ⟨hb, d, hd, hz⟩ := hTV _ ⟨hvV, hm'⟩
  rw [(M.fibre _ (χ.mem _ hb) _ hm').2 ⟨d, hd, hz⟩, proj_torusSmul hP M hv hc']

theorem analyticAt_proj {e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)} (he : IsCompatChart M.atlas e)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → (Σ k, J k) → ℂ} {u : E} (hg : AnalyticAt ℂ g u)
    (hm : ∀ᶠ v in 𝓝 u, g v ∈ mcPts (mCoordIdeal D.y)) (hsrc : M.proj (g u) ∈ e.source) :
    AnalyticAt ℂ (fun v => e (M.proj (g v))) u := by
  obtain ⟨a, t, ht, c, hc, hgu⟩ := D.chart_cover _ hm.self_of_nhds
  have ht' : t ∈ ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
    mem_ball_zero_iff.2 (ht.trans_lt (by norm_num))
  exact analyticAt_proj_gen (n := D.n) D.arith.2.1.2.1 M (D.chart a) he ht' (GlobalTheory.T.chart_local_analytic_trivialization K J II Ψ Ω W D a t ht')
    hg hm hsrc hc hgu

theorem comp_proj_eventuallyEq {β : Type*} (G : M.Xc → β) (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ))
    {E : Type*} [TopologicalSpace E] {g : E → (Σ k, J k) → ℂ} {u : E} (hg : ContinuousAt g u)
    (hm : ∀ᶠ v in 𝓝 u, g v ∈ mcPts (mCoordIdeal D.y)) (hsrc : M.proj (g u) ∈ e.source) :
    (G ∘ e.symm) ∘ (fun v => e (M.proj (g v))) =ᶠ[𝓝 u] fun v => G (M.proj (g v)) := by
  filter_upwards [(continuousAt_proj M hg hm).eventually (e.open_source.mem_nhds hsrc)] with v hv
  simp only [Function.comp_apply, e.left_inv hv]

theorem analyticAt_holoOn_proj {U : Set M.Xc} {G : M.Xc → ℂ} (hG : M.atlas.HoloOn U G)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → (Σ k, J k) → ℂ} {u : E} (hg : AnalyticAt ℂ g u)
    (hm : ∀ᶠ v in 𝓝 u, g v ∈ mcPts (mCoordIdeal D.y)) (hU : M.proj (g u) ∈ U) :
    AnalyticAt ℂ (fun v => G (M.proj (g v))) u := by
  obtain ⟨j, hj⟩ := M.atlas.cover (M.proj (g u))
  exact (AnalyticAt.comp (f := fun v => M.atlas.chart j (M.proj (g v)))
    (analyticAt_comp_symm_of_holoOn (compat_atlas _ j) hG hU hj)
    (analyticAt_proj D M (compat_atlas _ j) hg hm hj)).congr
    (comp_proj_eventuallyEq D M G _ hg.continuousAt hm hj)

theorem contDiffAt_smoothOn_proj {U : Set M.Xc} (hUo : IsOpen U) {G : M.Xc → ℝ} (hG : M.atlas.SmoothOn U G)
    {m : ℕ} {g : (Fin m → ℂ) → (Σ k, J k) → ℂ} {u : Fin m → ℂ} (hg : AnalyticAt ℂ g u)
    (hm : ∀ᶠ v in 𝓝 u, g v ∈ mcPts (mCoordIdeal D.y)) (hU : M.proj (g u) ∈ U) :
    ContDiffAt ℝ ∞ (fun v => G (M.proj (g v))) u := by
  obtain ⟨j, hj⟩ := M.atlas.cover (M.proj (g u))
  have h : AnalyticAt ℝ (fun v => M.atlas.chart j (M.proj (g v))) u :=
    (analyticAt_proj D M (compat_atlas _ j) hg hm hj).restrictScalars
  exact (ContDiffAt.comp (f := fun v => M.atlas.chart j (M.proj (g v))) u
    (contDiffAt_comp_symm_of_smoothOn (compat_atlas _ j) hUo hG hU hj) h.contDiffAt).congr_of_eventuallyEq
    (comp_proj_eventuallyEq D M G _ hg.continuousAt hm hj).symm

end Component

end LevelTowerAlt
