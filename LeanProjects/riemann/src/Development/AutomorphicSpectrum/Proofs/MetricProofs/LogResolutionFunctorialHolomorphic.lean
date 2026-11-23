import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Proj

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem orbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem orbit_trans {a b d : (Σ k, ι k) → ℂ} (h : SameOrbit a b) (h' : SameOrbit b d) :
    SameOrbit a d := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem orbit_cross {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) (k : K) (i i' : ι k) :
    z ⟨k, i⟩ * w ⟨k, i'⟩ = z ⟨k, i'⟩ * w ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  simp only
  ring

theorem orbit_of_cross {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : ∀ k (i i' : ι k), z ⟨k, i⟩ * w ⟨k, i'⟩ = z ⟨k, i'⟩ * w ⟨k, i⟩) : SameOrbit z w := by
  choose p hp using hw
  refine ⟨fun k => z ⟨k, p k⟩ / w ⟨k, p k⟩, fun k => ?_, ?_⟩
  · refine div_ne_zero (fun h0 => ?_) (hp k)
    obtain ⟨i, hi⟩ := hz k
    have := h k i (p k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hp k)) this
  · funext ⟨k, i⟩
    have := h k i (p k)
    have hk := hp k
    simp only
    field_simp
    linear_combination this

theorem affCoord_eq {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (p : (k : K) → ι k) :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem not_mem_mcPts_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have := h.2 1 Submodule.mem_top
  simp at this

end Orbit

section Analysis

theorem continuousAt_of_holoOn {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : AnalyticAt ℂ (g ∘ (A.chart j).symm) (A.chart j x) :=
    hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp (f := A.chart j) h1.continuousAt ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem exists_analytic_retraction {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {a : (Fin D → ℂ) → E} {w₀ : Fin D → ℂ} (ha : AnalyticAt ℂ a w₀)
    (hker : (fderiv ℂ a w₀).ker = ⊥) :
    ∃ G : E → Fin D → ℂ, AnalyticAt ℂ G (a w₀) ∧ ∀ᶠ w in 𝓝 w₀, G (a w) = w := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    ((fderiv ℂ a w₀ : (Fin D → ℂ) →L[ℂ] E) : (Fin D → ℂ) →ₗ[ℂ] E) (by simpa using hker)
  let L : E →L[ℂ] Fin D → ℂ := LinearMap.toContinuousLinearMap g
  have hf : AnalyticAt ℂ (L ∘ a) w₀ := L.analyticAt _ |>.comp ha
  have hcd : ContDiffAt ℂ ⊤ (L ∘ a) w₀ := hf.contDiffAt
  have hd : HasFDerivAt (L ∘ a)
      ((ContinuousLinearEquiv.refl ℂ (Fin D → ℂ) : (Fin D → ℂ) ≃L[ℂ] (Fin D → ℂ)) :
        (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) w₀ := by
    have h1 := L.hasFDerivAt.comp w₀ ha.differentiableAt.hasFDerivAt
    refine h1.congr_fderiv ?_
    ext1 v
    have := congrArg (fun T : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ) => T v) hg
    simpa [L] using this
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hcd.localInverse hd hn ∘ L, ?_, ?_⟩
  · have h1 := (hcd.to_localInverse hd hn).analyticAt
    exact AnalyticAt.comp (g := hcd.localInverse hd hn) (f := L) h1 (L.analyticAt _)
  · exact (hcd.hasStrictFDerivAt' hd hn).eventually_left_inverse

end Analysis

section Factor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem orbit_ne {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) {q : Σ k, ι k} (hq : z q ≠ 0) :
    w q ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := h
  exact right_ne_zero_of_mul hq

theorem analyticAt_affCoord {e : ℕ} {Z : Type*} [TopologicalSpace Z] (A : FinHolAtlas e Z)
    {U : Set Z} {f : Z → (Σ k, ι k) → ℂ} (hf : ∀ q, A.HoloOn U fun z => f z q) (j : Fin A.n)
    {w : Fin e → ℂ} (hw : w ∈ (A.chart j).target) (hU : (A.chart j).symm w ∈ U)
    (p : (k : K) → ι k) (hp : ∀ k, f ((A.chart j).symm w) ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun w' => affCoord p (f ((A.chart j).symm w'))) w := by
  refine AnalyticAt.pi fun q => ?_
  exact AnalyticAt.div (hf q j w ⟨hw, hU⟩) (hf ⟨q.1, p q.1⟩ j w ⟨hw, hU⟩) (hp q.1)

variable {P : Ideal (MRing ι)} {D e : ℕ} (R : AnLogRes P ⊤ D) {Y : Type*} [TopologicalSpace Y]
  (B : FinHolAtlas e Y) {V : Y → Set Y} {μ : Y → Y → (Σ k, ι k) → ℂ} {h : Y → R.X}

include R in

theorem local_orbit (hVm : ∀ y, y ∈ V y)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) {x : R.X} {y y' : Y}
    (h1 : h y' ∈ R.U x) (h2 : y' ∈ V y) : SameOrbit (R.lift x (h y')) (μ y y') :=
  orbit_trans (R.compat x (h y') (h y') ⟨h1, R.mem_U _⟩)
    (orbit_trans (hh y') (hc y' y y' ⟨hVm y', h2⟩))

theorem continuous_of_orbit (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hmem : ∀ y, ∀ u ∈ V y, μ y u ∈ mcPts P)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro F hF
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (F.map h) (by simp)
  have hth : Tendsto h F (𝓝 x) := hx
  have hUx : ∀ᶠ y' in (F : Filter Y), h y' ∈ R.U x := hth ((R.isOpen_U x).mem_nhds (R.mem_U x))
  have hVy : ∀ᶠ y' in (F : Filter Y), y' ∈ V y := hF ((hVo y).mem_nhds (hVm y))
  have hcr : ∀ k (i i' : ι k), R.lift x x ⟨k, i⟩ * μ y y ⟨k, i'⟩ =
      R.lift x x ⟨k, i'⟩ * μ y y ⟨k, i⟩ := by
    intro k i i'
    have t1 : ∀ q, Tendsto (fun y' => R.lift x (h y') q) F (𝓝 (R.lift x x q)) := fun q =>
      (continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hth
    have t2 : ∀ q, Tendsto (fun y' => μ y y' q) F (𝓝 (μ y y q)) := fun q =>
      (continuousAt_of_holoOn B (hμ y q) (hVm y)).tendsto.mono_left hF
    refine tendsto_nhds_unique ((t1 ⟨k, i⟩).mul (t2 ⟨k, i'⟩))
      (((t1 ⟨k, i'⟩).mul (t2 ⟨k, i⟩)).congr' ?_)
    filter_upwards [hUx, hVy] with y' h1 h2
    exact orbit_cross (local_orbit R hVm hc hh h1 h2) k i' i
  have hxy : SameOrbit (R.lift x x) (μ y y) :=
    orbit_of_cross (R.mem x x (R.mem_U x)).1 (hmem y y (hVm y)).1 hcr
  have hxe : x = h y := R.inj x (h y) (not_mem_mcPts_top _) (orbit_trans hxy (orbit_symm (hh y)))
  rw [← hxe]
  exact hx

theorem analytic_of_orbit (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) (hcont : Continuous h) (j : Fin B.n)
    (k : Fin R.A.n) : AnalyticOnNhd ℂ (R.A.chart k ∘ h ∘ (B.chart j).symm)
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (R.A.chart k).source)) := by
  rintro u ⟨hu, hsrc⟩
  have hsrc' : h ((B.chart j).symm u) ∈ (R.A.chart k).source := hsrc
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = (B.chart j).symm u := ⟨_, rfl⟩
  rw [← hy₀] at hsrc'
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = h y₀ := ⟨_, rfl⟩
  rw [← hx₀] at hsrc'
  have hz₀ := R.mem x₀ x₀ (R.mem_U x₀)
  choose p hp using hz₀.1
  have hlw : (R.A.chart k).symm (R.A.chart k x₀) = x₀ := (R.A.chart k).left_inv hsrc'
  have hA : AnalyticAt ℂ (fun w => affCoord p (R.lift x₀ ((R.A.chart k).symm w)))
      (R.A.chart k x₀) :=
    analyticAt_affCoord R.A (R.holo x₀) k ((R.A.chart k).map_source hsrc')
      (by rw [hlw]; exact R.mem_U x₀) p (by rw [hlw]; exact hp)
  obtain ⟨G, hG, hGl⟩ := exists_analytic_retraction hA
    (R.immersion x₀ (not_mem_mcPts_top _) p hp k hsrc')
  have horb : SameOrbit (R.lift x₀ x₀) (μ y₀ y₀) := by rw [hx₀]; exact hh y₀
  have hB : AnalyticAt ℂ (fun u' => affCoord p (μ y₀ ((B.chart j).symm u'))) u :=
    analyticAt_affCoord B (hμ y₀) j hu (by rw [← hy₀]; exact hVm y₀) p
      (by rw [← hy₀]; exact fun k' => orbit_ne horb (hp k'))
  have hbu : affCoord p (μ y₀ ((B.chart j).symm u)) =
      affCoord p (R.lift x₀ ((R.A.chart k).symm (R.A.chart k x₀))) := by
    rw [hlw, ← hy₀]
    exact (affCoord_eq horb p).symm
  have hGb : AnalyticAt ℂ (G ∘ fun u' => affCoord p (μ y₀ ((B.chart j).symm u'))) u := by
    refine AnalyticAt.comp ?_ hB
    simp only [hbu]
    exact hG
  refine hGb.congr ?_
  have c1 : ContinuousAt (B.chart j).symm u := (B.chart j).continuousAt_symm hu
  have e1 : ∀ᶠ u' in 𝓝 u, (B.chart j).symm u' ∈ V y₀ :=
    c1.eventually_mem ((hVo y₀).mem_nhds (by rw [← hy₀]; exact hVm y₀))
  have c2 : ContinuousAt (fun u' => h ((B.chart j).symm u')) u := hcont.continuousAt.comp c1
  have e2 : ∀ᶠ u' in 𝓝 u, h ((B.chart j).symm u') ∈ R.U x₀ ∩ (R.A.chart k).source :=
    c2.eventually_mem (((R.isOpen_U x₀).inter (R.A.chart k).open_source).mem_nhds
      (by rw [← hy₀, ← hx₀]; exact ⟨R.mem_U _, hsrc'⟩))
  have c3 : Tendsto (fun u' => R.A.chart k (h ((B.chart j).symm u'))) (𝓝 u)
      (𝓝 (R.A.chart k x₀)) := by
    have := ((R.A.chart k).continuousAt hsrc').tendsto
    refine this.comp ?_
    have t := c2.tendsto
    rwa [← hy₀, ← hx₀] at t
  have e3 := c3.eventually hGl
  filter_upwards [e1, e2, e3] with u' h1 h2 h3
  simp only [Function.comp]
  rw [← h3, (R.A.chart k).left_inv h2.2]
  exact congrArg G (affCoord_eq (local_orbit R hVm hc hh h2.1 h1) p).symm

theorem exists_holoMap_of_local_lifts (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hmem : ∀ y, ∀ u ∈ V y, μ y u ∈ mcPts P)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u)) :
    ∃ h : Y → R.X, HoloMap B R.A h ∧ ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y) := by
  have hex : ∀ y, ∃ x, SameOrbit (R.lift x x) (μ y y) := fun y =>
    R.surj _ (hmem y y (hVm y)) (not_mem_mcPts_top _)
  choose h hh using hex
  have hcont := continuous_of_orbit R B hVo hVm hμ hmem hc hh
  exact ⟨h, ⟨hcont, analytic_of_orbit R B hVo hVm hμ hc hh hcont⟩, hh⟩

end Factor

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} {P : Ideal (MRing ι)}
    {P' : Ideal (MRing ι')} (hb : IsBlockMap κ v) (hP : P ≤ imageZ v P')
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts P') : z ∘ v ∈ mcPts P := by
  obtain ⟨hκ, -, hblk, hsurj⟩ := hb
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨q, hq⟩ := hsurj ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : q.1 = k := hκ (by rw [← hblk q, hq])
    subst hk
    refine ⟨q.2, ?_⟩
    change z (v q) ≠ 0
    rw [hq]
    exact hi'
  · have h1 : rename v f ∈ P' := hP hf
    have h2 := hz.2 _ h1
    rwa [map_rename, eval_rename] at h2

end Block

theorem holoMap_of_blockProj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → (Σ k, ι' k)) (P : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P ⊤ D) (R' : AnLogRes P' J' D'), IsBlockMap κ v → P ≤ imageZ v P' → ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x ∘ v) := by
  intro K _ ι _ K' _ ι' _ κ v P P' J' D D' R R' hb hP
  refine exists_holoMap_of_local_lifts R R'.A (V := R'.U) (μ := fun y u => R'.lift y u ∘ v)
    R'.isOpen_U R'.mem_U (fun y q => R'.holo y (v q))
    (fun y u hu => comp_mem_mcPts hb hP (R'.mem y u hu)) ?_
  intro y y' u hu
  obtain ⟨c, hc, e⟩ := R'.compat y y' u hu
  refine ⟨c ∘ κ, fun k => hc _, ?_⟩
  funext p
  have := congrFun e (v p)
  simpa [hb.2.2.1 p] using this

end GlobalTheory.CompanionTheory.Ar.PB.Proj
