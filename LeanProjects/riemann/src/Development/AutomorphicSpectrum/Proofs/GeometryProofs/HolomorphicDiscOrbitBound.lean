import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug.Disc

open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.FinHolAtlas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem orbit_symm {u w : (Σ k, ι k) → ℂ} (h : SameOrbit u w) : SameOrbit w u := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem orbit_trans {u v w : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (h' : SameOrbit v w) :
    SameOrbit u w := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

theorem orbit_cross {u w : (Σ k, ι k) → ℂ} (h : SameOrbit u w) (k : K) (a b : ι k) :
    u ⟨k, a⟩ * w ⟨k, b⟩ = u ⟨k, b⟩ * w ⟨k, a⟩ := by
  obtain ⟨c, hc, rfl⟩ := h
  simp only []
  ring

theorem orbit_of_cross {u w : (Σ k, ι k) → ℂ} (hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : ∀ k (a b : ι k), u ⟨k, a⟩ * w ⟨k, b⟩ = u ⟨k, b⟩ * w ⟨k, a⟩) : SameOrbit u w := by
  choose l hl using hw
  refine ⟨fun k => u ⟨k, l k⟩ / w ⟨k, l k⟩, fun k => ?_, ?_⟩
  · refine div_ne_zero (fun h0 => ?_) (hl k)
    obtain ⟨i, hi⟩ := hu k
    have := h k i (l k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hl k)) this
  · funext ⟨k, a⟩
    have := h k a (l k)
    simp only []
    field_simp [hl k]
    linear_combination this

theorem affCoord_orbit {u w : (Σ k, ι k) → ℂ} (h : SameOrbit u w) (p : (k : K) → ι k) :
    affCoord p u = affCoord p w := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

section Atlas

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {F : Type} [TopologicalSpace F] (A : FinHolAtlas e X) {g : X → F}
    {x : X} (j : Fin A.n) (hj : x ∈ (A.chart j).source)
    (h : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x)) : ContinuousAt g x := by
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp h ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem chart_mem (A : FinHolAtlas e X) {U : Set X} {x : X} (hx : x ∈ U) (j : Fin A.n)
    (hj : x ∈ (A.chart j).source) :
    A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
  ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩

theorem analyticAt_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y}
    {A : FinHolAtlas e X} {h : Y → X} (hh : HoloMap B A h) {V : Set X} {G : X → ℂ}
    (hG : A.HoloOn V G) {y₀ : Y} (hy : h y₀ ∈ V) (j : Fin B.n)
    (hj : y₀ ∈ (B.chart j).source) :
    AnalyticAt ℂ (G ∘ h ∘ (B.chart j).symm) (B.chart j y₀) := by
  obtain ⟨k, hk⟩ := A.cover (h y₀)
  have hv := (B.chart j).map_source hj
  have hl := (B.chart j).left_inv hj
  have h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) (B.chart j y₀) :=
    hh.2 j k _ ⟨hv, by simpa [hl] using hk⟩
  have h2 : AnalyticAt ℂ (G ∘ (A.chart k).symm) (A.chart k (h y₀)) :=
    hG k _ (chart_mem A hy k hk)
  have h2' : AnalyticAt ℂ (G ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (B.chart j).symm) (B.chart j y₀)) := by
    simpa [hl] using h2
  have h3 := h2'.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (h ∘ (B.chart j).symm) (B.chart j y₀) :=
    hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hv)
  have hs : (A.chart k).source ∈ 𝓝 ((h ∘ (B.chart j).symm) (B.chart j y₀)) := by
    simpa [hl] using (A.chart k).open_source.mem_nhds hk
  filter_upwards [hc.tendsto hs] with v hv'
  exact congrArg G ((A.chart k).left_inv hv')

end Atlas

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem lift_continuousAt (R : AnLogRes P J e) (x : R.X) {y : R.X} (hy : y ∈ R.U x) :
    ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  refine continuousAt_pi.2 fun p => ?_
  refine continuousAt_of_chart R.A j hj ?_
  exact (R.holo x p j _ (chart_mem R.A hy j hj)).continuousAt

theorem tendsto_center (R : AnLogRes P J e) (hJ : ∀ z, z ∉ mcPts J)
    {Zf : ℂ → (Σ k, ι k) → ℂ} (hZ : ContinuousAt Zf 0) (hZ0 : ∀ k, ∃ i, Zf 0 ⟨k, i⟩ ≠ 0)
    {x : ℂ → R.X} (hx : ∀ᶠ z in 𝓝 (0 : ℂ), SameOrbit (R.lift (x z) (x z)) (Zf z))
    {x₀ : R.X} (h0 : SameOrbit (R.lift x₀ x₀) (Zf 0)) : Tendsto x (𝓝 0) (𝓝 x₀) := by
  rw [tendsto_iff_ultrafilter]
  intro F hF
  have hxs : Tendsto x F (𝓝 (F.map x).lim) := (F.map x).le_nhds_lim
  set xs := (F.map x).lim with hxsdef
  have hU : ∀ᶠ z in (F : Filter ℂ), x z ∈ R.U xs :=
    hxs.eventually ((R.isOpen_U xs).mem_nhds (R.mem_U xs))
  have hl : Tendsto (fun z => R.lift xs (x z)) F (𝓝 (R.lift xs xs)) :=
    (lift_continuousAt R xs (R.mem_U xs)).tendsto.comp hxs
  have hZF : Tendsto Zf F (𝓝 (Zf 0)) := hZ.tendsto.mono_left hF
  have horb : ∀ᶠ z in (F : Filter ℂ), SameOrbit (R.lift xs (x z)) (Zf z) := by
    filter_upwards [hU, hF hx] with z h1 h2
    exact orbit_trans (R.compat xs (x z) (x z) ⟨h1, R.mem_U _⟩) h2
  have hcross : ∀ k (a b : ι k), R.lift xs xs ⟨k, a⟩ * Zf 0 ⟨k, b⟩ =
      R.lift xs xs ⟨k, b⟩ * Zf 0 ⟨k, a⟩ := by
    intro k a b
    have t1 : Tendsto (fun z => R.lift xs (x z) ⟨k, a⟩ * Zf z ⟨k, b⟩) F
        (𝓝 (R.lift xs xs ⟨k, a⟩ * Zf 0 ⟨k, b⟩)) :=
      ((tendsto_pi_nhds.1 hl) _).mul ((tendsto_pi_nhds.1 hZF) _)
    have t2 : Tendsto (fun z => R.lift xs (x z) ⟨k, b⟩ * Zf z ⟨k, a⟩) F
        (𝓝 (R.lift xs xs ⟨k, b⟩ * Zf 0 ⟨k, a⟩)) :=
      ((tendsto_pi_nhds.1 hl) _).mul ((tendsto_pi_nhds.1 hZF) _)
    refine tendsto_nhds_unique_of_eventuallyEq t1 t2 ?_
    filter_upwards [horb] with z hz
    exact orbit_cross hz k a b
  have hfin : SameOrbit (R.lift xs xs) (Zf 0) :=
    orbit_of_cross (R.mem xs xs (R.mem_U xs)).1 hZ0 hcross
  have : xs = x₀ := R.inj xs x₀ (hJ _) (orbit_trans hfin (orbit_symm h0))
  rw [← this]
  exact hxs

theorem chart_differentiable (R : AnLogRes P J e) (hJ : ∀ z, z ∉ mcPts J)
    {Zf : ℂ → (Σ k, ι k) → ℂ}
    (hZ : ∀ q, ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => Zf w q) z)
    {x : ℂ → R.X} {x₀ : R.X} (hx : ∀ᶠ z in 𝓝 (0 : ℂ), SameOrbit (R.lift (x z) (x z)) (Zf z))
    (h0 : SameOrbit (R.lift x₀ x₀) (Zf 0)) (ht : Tendsto x (𝓝 0) (𝓝 x₀)) (j : Fin R.A.n)
    (hj : x₀ ∈ (R.A.chart j).source) :
    ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => R.A.chart j (x w)) z := by
  classical
  choose p hp using (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hv₀ := chart_mem R.A (R.mem_U x₀) j hj
  have hl := (R.A.chart j).left_inv hj
  let a : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun v => affCoord p (R.lift x₀ ((R.A.chart j).symm v))
  have hcoord : ∀ q, AnalyticAt ℂ (fun v => R.lift x₀ ((R.A.chart j).symm v) q) (R.A.chart j x₀) :=
    fun q => R.holo x₀ q j _ hv₀
  have hden : ∀ k, R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    rw [hl]
    exact hp k
  have ha : AnalyticAt ℂ a (R.A.chart j x₀) := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (hcoord q).div (hcoord _) (hden q.1)
  have hker : ((fderiv ℂ a (R.A.chart j x₀) : (Fin e → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ)) :
      (Fin e → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ)).ker = ⊥ :=
    R.immersion x₀ (hJ _) p hp j hj
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let ρc : ((Σ k, ι k) → ℂ) →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap ρ
  let b : (Fin e → ℂ) → (Fin e → ℂ) := fun v => ρc (a v)
  have hb : ContDiffAt ℂ 1 b (R.A.chart j x₀) :=
    ρc.contDiff.contDiffAt.comp _ ha.contDiffAt
  have hb' : HasFDerivAt b
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (R.A.chart j x₀) := by
    have h1 := ρc.hasFDerivAt.comp (R.A.chart j x₀) ha.differentiableAt.hasFDerivAt
    refine HasFDerivAt.congr_fderiv h1 (ContinuousLinearMap.ext fun v => ?_)
    exact LinearMap.congr_fun hρ v
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  let Inv := hb.localInverse hb' hn
  have hInv : ContDiffAt ℂ 1 Inv (b (R.A.chart j x₀)) := hb.to_localInverse hb' hn
  have hleft : ∀ᶠ v in 𝓝 (R.A.chart j x₀), Inv (b v) = v :=
    (hb.hasStrictFDerivAt' hb' hn).eventually_left_inverse
  let c : ℂ → Fin e → ℂ := fun z => ρc (affCoord p (Zf z))
  have hZp : ∀ k, Zf 0 ⟨k, p k⟩ ≠ 0 := by
    obtain ⟨d, -, hd⟩ := h0
    intro k h
    exact hp k (by rw [hd]; simp [h])
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ q, DifferentiableAt ℂ (fun w => Zf w q) z :=
    eventually_all.2 hZ
  have hDen : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ k, Zf z ⟨k, p k⟩ ≠ 0 := by
    refine eventually_all.2 fun k => ?_
    exact (hZ ⟨k, p k⟩).self_of_nhds.continuousAt.eventually_ne (hZp k)
  have hcd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ c z := by
    filter_upwards [hall, hDen] with z h1 h2
    refine ρc.differentiableAt.comp z (differentiableAt_pi.2 fun q => ?_)
    exact (h1 q).div (h1 _) (h2 q.1)
  have hc0 : c 0 = b (R.A.chart j x₀) := by
    show ρc (affCoord p (Zf 0)) = ρc (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀))))
    rw [hl, affCoord_orbit h0]
  have hcc : ContinuousAt c 0 := hcd.self_of_nhds.continuousAt
  have hInvd : ∀ᶠ y in 𝓝 (c 0), DifferentiableAt ℂ Inv y := by
    rw [hc0]
    exact (hInv.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hdiff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => Inv (c w)) z := by
    filter_upwards [hcc.tendsto.eventually hInvd, hcd] with z h1 h2
    exact h1.comp z h2
  have hchart : Tendsto (fun z => R.A.chart j (x z)) (𝓝 0) (𝓝 (R.A.chart j x₀)) :=
    ((R.A.chart j).continuousAt hj).tendsto.comp ht
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), R.A.chart j (x z) = Inv (c z) := by
    filter_upwards [hchart.eventually hleft, ht.eventually ((R.A.chart j).open_source.mem_nhds hj),
      ht.eventually ((R.isOpen_U x₀).mem_nhds (R.mem_U x₀)), hx] with z h1 h2 h3 h4
    have hbz : b (R.A.chart j (x z)) = c z := by
      show ρc (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j (x z))))) =
        ρc (affCoord p (Zf z))
      rw [(R.A.chart j).left_inv h2,
        affCoord_orbit (orbit_trans (R.compat x₀ (x z) (x z) ⟨h3, R.mem_U _⟩) h4)]
    rw [← hbz, h1]
  filter_upwards [hdiff, heq.eventually_nhds] with z h1 h2
  exact h1.congr_of_eventuallyEq h2

theorem exists_lower_bound {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z ≠ 0) :
    ∃ (c : ℝ) (m : ℕ), 0 < c ∧ ∀ᶠ z in 𝓝 (0 : ℂ), c * ‖z‖ ^ m ≤ ‖g z‖ := by
  have hnot : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), g z = 0 := by
    intro h
    have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = 0 := h.filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz1, hz2⟩ := (hne.and h1).exists
    exact hz1 hz2
  obtain ⟨m, f, hf, hf0, hgf⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot
  refine ⟨‖f 0‖ / 2, m, by positivity, ?_⟩
  have hlt : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f 0‖ / 2 < ‖f z‖ :=
    hf.continuousAt.norm.eventually (lt_mem_nhds (by
      have : 0 < ‖f 0‖ := norm_pos_iff.2 hf0
      linarith))
  filter_upwards [hgf, hlt] with z h1 h2
  rw [h1, norm_smul, norm_pow, sub_zero, mul_comm]
  exact mul_le_mul_of_nonneg_left h2.le (by positivity)

end GlobalTheory.CompanionTheory.Ar.Plug.Disc

namespace GlobalTheory.CompanionTheory.Ar.Plug

open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.FinHolAtlas GlobalTheory.CompanionTheory.Ar.Plug.Disc

theorem rW_le_log_disc : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : PB.AnSys D σ) (P : Ideal (MRing ι)) (Re : PB.Realis S P), Re.J = ⊤ → ∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts P) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → Re.π x ∈ S.open') → ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → ReciprocityTheory.AnForm.P.rW S.L S.s (Re.π x) ≤ C * (1 + |Real.log ‖z‖|) := by
  intro K _ ι _ D σ S P Re hJ Zf hZ hmem hopen
  have hJ' : ∀ z, z ∉ mcPts Re.J := by
    intro z hz
    have := hz.2 1 (by rw [hJ]; trivial)
    simp at this
  have h0b : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  obtain ⟨x₀, h0⟩ := Re.R.surj (Zf 0) (hmem 0 h0b) (hJ' _)
  have hex : ∀ z, ∃ x : Re.R.X, z ∈ Metric.ball (0 : ℂ) 1 → SameOrbit (Re.R.lift x x) (Zf z) := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : ℂ) 1
    · obtain ⟨x, hx⟩ := Re.R.surj (Zf z) (hmem z hz) (hJ' _)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨x₀, fun h => absurd h hz⟩
  choose x hxs using hex
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_mem_nhds _ one_pos
  have hx : ∀ᶠ z in 𝓝 (0 : ℂ), SameOrbit (Re.R.lift (x z) (x z)) (Zf z) := hball.mono hxs
  have hZd : ∀ q, ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => Zf w q) z := fun q => by
    filter_upwards [hball] with z hz
    exact (hZ q).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hZc : ContinuousAt Zf 0 := continuousAt_pi.2 fun q => (hZd q).self_of_nhds.continuousAt
  have ht : Tendsto x (𝓝 0) (𝓝 x₀) := tendsto_center Re.R hJ' hZc (hmem 0 h0b).1 hx h0
  obtain ⟨j, hj⟩ := Re.R.A.cover x₀
  have hv := chart_differentiable Re.R hJ' hZd hx h0 ht j hj
  have hH : AnalyticAt ℂ (S.s (Re.π x₀) ∘ Re.π ∘ (Re.R.A.chart j).symm) (Re.R.A.chart j x₀) :=
    analyticAt_comp Re.holo (S.sec.1 (Re.π x₀)) (S.L.mem_U _) j hj
  have hvt : Tendsto (fun z => Re.R.A.chart j (x z)) (𝓝 0) (𝓝 (Re.R.A.chart j x₀)) :=
    ((Re.R.A.chart j).continuousAt hj).tendsto.comp ht
  have hsrc : ∀ᶠ z in 𝓝 (0 : ℂ), x z ∈ (Re.R.A.chart j).source :=
    ht.eventually ((Re.R.A.chart j).open_source.mem_nhds hj)
  have hg : AnalyticAt ℂ (fun z => S.s (Re.π x₀) (Re.π (x z))) 0 := by
    refine Complex.analyticAt_iff_eventually_differentiableAt.2 ?_
    filter_upwards [hv, hvt.eventually hH.eventually_analyticAt, hsrc.eventually_nhds] with z h1 h2 h3
    have h4 := (h2.differentiableAt.comp z h1)
    refine h4.congr_of_eventuallyEq ?_
    filter_upwards [h3] with w hw
    simp [(Re.R.A.chart j).left_inv hw]
  have hyt : Tendsto (fun z => Re.π (x z)) (𝓝 0) (𝓝 (Re.π x₀)) :=
    (Re.holo.1.tendsto x₀).comp ht
  have hLU : ∀ᶠ z in 𝓝 (0 : ℂ), Re.π (x z) ∈ S.L.U (Re.π x₀) :=
    hyt.eventually ((S.L.isOpen_U _).mem_nhds (S.L.mem_U _))
  have hkey : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → S.s (Re.π x₀) (Re.π (x z)) ≠ 0 ∧
      logNormSec S.L S.s (Re.π (x z)) = Real.log ‖S.s (Re.π x₀) (Re.π (x z))‖ -
        S.L.φ (Re.π x₀) (Re.π (x z)) := by
    filter_upwards [hball, hLU] with z hz hU hz0
    have hop : S.s (Re.π (x z)) (Re.π (x z)) ≠ 0 := hopen z hz hz0 (x z) (hxs z hz)
    have hsec := S.sec.2 (Re.π x₀) (Re.π (x z)) (Re.π (x z)) ⟨hU, S.L.mem_U _⟩
    have hne : S.s (Re.π x₀) (Re.π (x z)) ≠ 0 := by
      intro h
      rw [h, norm_zero, zero_mul] at hsec
      exact (mul_pos (norm_pos_iff.2 hop) (Real.exp_pos _)).ne hsec
    refine ⟨hne, ?_⟩
    rw [logNormSec, ← hsec, Real.log_mul (norm_ne_zero_iff.2 hne) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), S.s (Re.π x₀) (Re.π (x z)) ≠ 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hkey] with z hz hz0
    exact (hz hz0).1
  obtain ⟨c, m, hc, hlow⟩ := exists_lower_bound hg hne
  have hφ : ContinuousAt (S.L.φ (Re.π x₀)) (Re.π x₀) := by
    obtain ⟨k, hk⟩ := S.A.cover (Re.π x₀)
    refine continuousAt_of_chart S.A k hk ?_
    have h1 := S.potL.1 (Re.π x₀) k
    refine h1.continuousOn.continuousAt ?_
    exact ((S.A.chart k).isOpen_inter_preimage_symm (S.L.isOpen_U _)).mem_nhds
      (chart_mem S.A (S.L.mem_U _) k hk)
  have hbd : ∀ᶠ z in 𝓝 (0 : ℂ), S.L.φ (Re.π x₀) (Re.π (x z)) < S.L.φ (Re.π x₀) (Re.π x₀) + 1 :=
    (hφ.tendsto.comp hyt).eventually_lt_const (lt_add_one _)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.1 (hkey.and (hlow.and (hbd.and hball)))
  set A : ℝ := Real.exp 1 + 2 * |Real.log c| + 2 * (|S.L.φ (Re.π x₀) (Re.π x₀)| + 1) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + 2 * m, min ε 1, lt_min hε one_pos, ?_⟩
  intro z hz0 hzε y hy
  have hz1 : ‖z‖ < 1 := hzε.trans_le (min_le_right _ _)
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz1
  have hne0 : z ≠ 0 := norm_pos_iff.1 hz0
  obtain ⟨h1, h2, h3, -⟩ := hall (y := z) (by simpa using hzε.trans_le (min_le_left _ _))
  obtain ⟨h1a, h1b⟩ := h1 hne0
  have hyx : y = x z := Re.R.inj y (x z) (hJ' _) (orbit_trans hy (orbit_symm (hxs z hzb)))
  subst hyx
  rw [ReciprocityTheory.AnForm.P.rW, h1b]
  have hlog : Real.log c + m * Real.log ‖z‖ ≤ Real.log ‖S.s (Re.π x₀) (Re.π (x z))‖ := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_mul hc.ne' (by positivity), Real.log_pow] at this
  have hlz : Real.log ‖z‖ = -|Real.log ‖z‖| := by
    rw [abs_of_nonpos (Real.log_nonpos hz0.le hz1.le), neg_neg]
  have hL : 0 ≤ |Real.log ‖z‖| := abs_nonneg _
  have hc1 := neg_abs_le (Real.log c)
  have hc2 := le_abs_self (S.L.φ (Re.π x₀) (Re.π x₀))
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hlz] at hlog
  nlinarith [mul_nonneg hA0 hL, mul_nonneg hm hL]

end GlobalTheory.CompanionTheory.Ar.Plug
