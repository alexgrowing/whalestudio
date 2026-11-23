import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.an_conj

open scoped ContDiff

variable {e : ℕ} {X : Type} [TopologicalSpace X]

noncomputable def cj (e : ℕ) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj i)

theorem cj_apply (z : Fin e → ℂ) : cj e z = star z := by
  ext i; simp [cj]

theorem levi_cj {g : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (hg : ContDiffAt ℝ 2 g (cj e z)) (w : Fin e → ℂ) :
    levi (g ∘ cj e) z w = levi g (cj e z) (cj e w) := by
  have hev : fderiv ℝ (g ∘ cj e) =ᶠ[𝓝 z] fun y => (fderiv ℝ g (cj e y)).comp (cj e) := by
    have h1 : ∀ᶠ y in 𝓝 (cj e z), ContDiffAt ℝ 2 g y := hg.eventually (by simp)
    filter_upwards [(cj e).continuous.continuousAt.eventually h1] with y hy
    rw [fderiv_comp y (hy.differentiableAt (by norm_num)) (cj e).differentiableAt, (cj e).fderiv]
  have hH : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (cj e z)) (cj e z) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 := ((hH.comp z (cj e).hasFDerivAt).clm_comp (hasFDerivAt_const (cj e) z)).fderiv
  have h3 : ∀ a b, fderiv ℝ (fderiv ℝ (g ∘ cj e)) z a b = fderiv ℝ (fderiv ℝ g) (cj e z) (cj e a) (cj e b) := by
    intro a b
    rw [hev.fderiv_eq]
    erw [h2]
    simp
  have h4 : cj e (Complex.I • w) = -(Complex.I • cj e w) := by
    ext i; simp [cj]
  unfold levi
  rw [h3, h3, h4]
  simp

def Anti (A : FinHolAtlas e X) (c : X → X) : Prop :=
  ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z))))
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))

theorem ev_eq {A : FinHolAtlas e X} {c : X → X} (hc : Continuous c) (g : X → ℝ) (j k : Fin A.n)
    {t : Fin e → ℂ} (ht : t ∈ (A.chart j).target) (hk : c ((A.chart j).symm t) ∈ (A.chart k).source) :
    (g ∘ c ∘ (A.chart j).symm) =ᶠ[𝓝 t]
      ((g ∘ (A.chart k).symm) ∘ cj e) ∘ fun z => star (A.chart k (c ((A.chart j).symm z))) := by
  have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source) ∈ 𝓝 t :=
    ((A.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hc)).mem_nhds ⟨ht, hk⟩
  filter_upwards [hm] with t' ht'
  simp only [Function.comp_apply, cj_apply, star_star, (A.chart k).left_inv ht'.2]

theorem smoothOn_pull {A : FinHolAtlas e X} {c : X → X} (hc : Continuous c) (ha : Anti A c)
    {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) : A.SmoothOn (c ⁻¹' U) (f ∘ c) := by
  intro j t ht
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨k, hk⟩ := A.cover (c ((A.chart j).symm t))
  have h1 := GlobalTheory.CompanionTheory.Ar.Giv.contDiffAt_of_smoothOn hU hf k ((A.chart k).map_source hk)
    (by rw [(A.chart k).left_inv hk]; exact ht.2)
  have h2 : ContDiffAt ℝ ∞ (fun z => star (A.chart k (c ((A.chart j).symm z)))) t :=
    ((ha j k t ⟨ht.1, hk⟩).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h3 : ContDiffAt ℝ ∞ ((f ∘ (A.chart k).symm) ∘ cj e) (star (A.chart k (c ((A.chart j).symm t)))) :=
    ContDiffAt.comp _ (by rw [cj_apply, star_star]; exact h1) (cj e).contDiff.contDiffAt
  exact (ContDiffAt.comp t h3 h2).congr_of_eventuallyEq (ev_eq hc f j k ht.1 hk)

theorem isPotential_pull {A : FinHolAtlas e X} {c : X → X} (hc : Continuous c) (ha : Anti A c)
    {P : LocPot X} (hP : IsPotential A P) : IsPotential A (P.pullback c hc) := by
  refine ⟨fun x => smoothOn_pull hc ha (P.isOpen_U _) (hP.1 (c x)), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 (c x) (c x') (c y) hy
  refine ⟨c ⁻¹' W, hW.preimage hc, hyW, _, Cj.holoOn_conj_comp c hc ha hG, fun z hz => ?_⟩
  rw [Complex.conj_re]
  exact hGe (c z) hz

theorem isPsh_pull {A : FinHolAtlas e X} {c : X → X} (hc : Continuous c) (ha : Anti A c)
    {P : LocPot X} (hP : IsPotential A P) (hpsh : IsPsh A P) : IsPsh A (P.pullback c hc) := by
  intro x j t ht w
  obtain ⟨k, hk⟩ := A.cover (c ((A.chart j).symm t))
  have hz := (A.chart k).map_source hk
  have hzU : (A.chart k).symm (A.chart k (c ((A.chart j).symm t))) ∈ P.U (c x) := by
    rw [(A.chart k).left_inv hk]; exact ht.2
  have h1 := potential_contDiffAt_chart hP (c x) k hz hzU
  have h1' : ContDiffAt ℝ 2 (P.φ (c x) ∘ (A.chart k).symm)
      (cj e (star (A.chart k (c ((A.chart j).symm t))))) := by rw [cj_apply, star_star]; exact h1
  have h3 : ContDiffAt ℝ 2 ((P.φ (c x) ∘ (A.chart k).symm) ∘ cj e) (star (A.chart k (c ((A.chart j).symm t)))) :=
    ContDiffAt.comp _ h1' (cj e).contDiff.contDiffAt
  show 0 ≤ levi (P.φ (c x) ∘ c ∘ (A.chart j).symm) t w
  rw [levi_congr (ev_eq hc _ j k ht.1 hk) w, levi_comp w (ha j k t ⟨ht.1, hk⟩) h3, levi_cj h1',
    cj_apply, star_star]
  exact hpsh (c x) k _ ⟨hz, hzU⟩ _

theorem isPsh_of_same {A : FinHolAtlas e X} {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q)
    (h : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
      ∀ y ∈ V, Q.φ x y = P.φ x y + (-1 / 2) * (G y).re) (hp : IsPsh A P) : IsPsh A Q := by
  choose V hV hxV G hG hGe using h
  let Q2 : LocPot X := ⟨fun x => V x ∩ P.U x, fun x => (hV x).inter (P.isOpen_U x),
    fun x => ⟨hxV x, P.mem_U x⟩, Q.φ⟩
  refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_of_phi_eq (P := Q2) hQ rfl ?_
  intro x j y hy w
  have hGa : AnalyticAt ℂ (G x ∘ (A.chart j).symm) y := hG x j y ⟨hy.1, hy.2.1⟩
  have hev : (Q.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (P.φ x ∘ (A.chart j).symm) v + (-1 / 2) * ((G x ∘ (A.chart j).symm) v).re := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm (hV x)).mem_nhds ⟨hy.1, hy.2.1⟩] with v hv
    exact hGe x _ hv.2
  have hRe : ContDiffAt ℝ 2 (fun v => ((G x ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  show 0 ≤ levi (Q.φ x ∘ (A.chart j).symm) y w
  rw [levi_congr hev, levi_add_smul _ (potential_contDiffAt_chart hP x j hy.1 hy.2.2) hRe,
    levi_re_analytic hGa, mul_zero, add_zero]
  exact hp x j y ⟨hy.1, hy.2.2⟩ w

theorem hasFDerivAt_lim {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : ℝ → E → F} {g : E → F} {g' : E → E →L[ℝ] F}
    (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, DifferentiableAt ℝ (f t) z)
    (h0 : TendstoLocallyUniformlyOn f g (𝓝[>] 0) U)
    (h1 : TendstoLocallyUniformlyOn (fun t => fderiv ℝ (f t)) g' (𝓝[>] 0) U) {z : E} (hz : z ∈ U) :
    HasFDerivAt g (g' z) z := by
  refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[>] (0 : ℝ)) (f := f)
    (f' := fun t => fderiv ℝ (f t)) ?_ ?_ ?_
  · have := tendstoLocallyUniformlyOn_iff_filter.1 h1 z hz
    rwa [hU.nhdsWithin_eq hz] at this
  · filter_upwards [hf.prod_mk (hU.mem_nhds hz)] with p hp
    exact (hp.1 p.2 hp.2).hasFDerivAt
  · filter_upwards [hU.mem_nhds hz] with y hy using h0.tendsto_at hy

theorem contDiffAt_lim {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U)
    {f : ℝ → E → ℝ} {g : E → ℝ} (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, ContDiffAt ℝ ∞ (f t) z)
    (h0 : TendstoLocallyUniformlyOn f g (𝓝[>] 0) U)
    (h1 : TendstoLocallyUniformlyOn (fun t => fderiv ℝ (f t)) (fderiv ℝ g) (𝓝[>] 0) U)
    (h2 : TendstoLocallyUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t))) (fderiv ℝ (fderiv ℝ g)) (𝓝[>] 0) U)
    {z : E} (hz : z ∈ U) : ContDiffAt ℝ 2 g z := by
  have d0 : ∀ y ∈ U, DifferentiableAt ℝ g y := fun y hy =>
    (hasFDerivAt_lim hU (hf.mono fun t ht z hz => (ht z hz).differentiableAt (by simp)) h0 h1 hy).differentiableAt
  have d1 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ g) y := fun y hy =>
    (hasFDerivAt_lim hU (hf.mono fun t ht z hz =>
      ((ht z hz).fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)) h1 h2 hy).differentiableAt
  have c2 : ContinuousOn (fderiv ℝ (fderiv ℝ g)) U := by
    refine h2.continuousOn (hf.mono fun t ht z hz => ?_).frequently
    exact ((((ht z hz).fderiv_right (m := 1) (by norm_cast)).fderiv_right (m := 0)
      (by norm_num)).continuousAt).continuousWithinAt
  have e1 : ContDiffOn ℝ 1 (fderiv ℝ g) U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨fun y hy => (d1 y hy).differentiableWithinAt, by simp, contDiffOn_zero.2 c2⟩
  have e2 : ContDiffOn ℝ 2 g U := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨fun y hy => (d0 y hy).differentiableWithinAt, by simp, e1⟩
  exact e2.contDiffAt (hU.mem_nhds hz)

theorem regular_family_pullback_involution {A : FinHolAtlas e X} {c : X → X} (hc : Continuous c) (ha : Anti A c) {s : X → X → ℂ}
    (hV : IsOpen (bdry s)ᶜ) (hb : ∀ y, c y ∈ bdry s ↔ y ∈ bdry s) {ph : X → ℝ} {phT : ℝ → X → ℝ}
    (hph : ∀ y ∉ bdry s, ph (c y) = ph y) (hT : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) : IsRegFamilyC2 A s ph fun t => phT t ∘ c := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast
  have hG : ∀ k, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (bdry s)ᶜ,
      ContDiffAt ℝ ∞ (phT t ∘ (A.chart k).symm) z := fun k => hT.mono fun t ht z hz =>
    GlobalTheory.CompanionTheory.Ar.Giv.contDiffAt_of_smoothOn isOpen_univ ht k hz.1 trivial
  have hΦ : ∀ k, ∀ z ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (bdry s)ᶜ,
      ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) z := by
    intro k z hz
    have hO := (A.chart k).isOpen_inter_preimage_symm hV
    exact contDiffAt_lim hO (hG k)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hO).2 fun K h1 h2 => (hC k K h1 h2).1)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hO).2 fun K h1 h2 => (hC k K h1 h2).2.1)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hO).2 fun K h1 h2 => (hC k K h1 h2).2.2) hz
  intro j K hKs hK
  have hOo := (A.chart j).isOpen_inter_preimage_symm hV
  have hloc : ∀ y0 ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, ∃ N ∈ 𝓝 y0,
      TendstoUniformlyOn (fun t => (phT t ∘ c) ∘ (A.chart j).symm) (ph ∘ (A.chart j).symm) (𝓝[>] 0) N ∧
      TendstoUniformlyOn (fun t => fderiv ℝ ((phT t ∘ c) ∘ (A.chart j).symm))
        (fderiv ℝ (ph ∘ (A.chart j).symm)) (𝓝[>] 0) N ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((phT t ∘ c) ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (A.chart j).symm))) (𝓝[>] 0) N := by
    intro y0 hy0
    obtain ⟨k, hk⟩ := A.cover (c ((A.chart j).symm y0))
    set W := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' ((A.chart k).source ∩ (bdry s)ᶜ)) with hWdef
    have hWo : IsOpen W :=
      (A.chart j).isOpen_inter_preimage_symm (((A.chart k).open_source.inter hV).preimage hc)
    have hy0W : y0 ∈ W := ⟨hy0.1, hk, fun h => hy0.2 ((hb _).1 h)⟩
    obtain ⟨N, hN0, hNW, hN⟩ := local_compact_nhds (hWo.mem_nhds hy0W)
    set τ := A.chart k ∘ c ∘ (A.chart j).symm with hτdef
    have hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y := by
      intro y hy
      have hR : ContDiffAt ℝ 2 (fun z => star (A.chart k (c ((A.chart j).symm z)))) y :=
        ((ha j k y ⟨hy.1, hy.2.1⟩).contDiffAt (n := 2)).restrict_scalars ℝ
      have := ((cj e).contDiff (n := 2)).contDiffAt.comp y hR
      convert this using 1
      funext z
      simp [hτdef, cj_apply]
    have hWU : Set.MapsTo τ W ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (bdry s)ᶜ) := by
      intro y hy
      refine ⟨(A.chart k).map_source hy.2.1, ?_⟩
      show (A.chart k).symm ((A.chart k) (c ((A.chart j).symm y))) ∈ (bdry s)ᶜ
      rw [(A.chart k).left_inv hy.2.1]
      exact hy.2.2
    have hτN : IsCompact (τ '' N) :=
      hN.image_of_continuousOn fun y hy => (hτ y (hNW hy)).continuousAt.continuousWithinAt
    obtain ⟨c0, c1, c2⟩ := hC k _ ((hWU.mono_left hNW).image_subset) hτN
    refine ⟨N, hN0, ?_⟩
    refine AnalyticLimit.C2ConvergencePullback.local_c2_convergence_pullback (G := fun t => phT t ∘ (A.chart k).symm)
      (Φ := ph ∘ (A.chart k).symm) hWo hτ hWU ((hG k).mono fun t ht z hz => (ht z hz).of_le h2) (hΦ k)
      ?_ ?_ hN hNW c0 c1 c2
    · intro t y hy
      show phT t (c ((A.chart j).symm y)) =
        phT t ((A.chart k).symm ((A.chart k) (c ((A.chart j).symm y))))
      rw [(A.chart k).left_inv hy.2.1]
    · intro y hy
      show ph ((A.chart j).symm y) = ph ((A.chart k).symm ((A.chart k) (c ((A.chart j).symm y))))
      rw [(A.chart k).left_inv hy.2.1]
      exact (hph _ fun h => hy.2.2 ((hb _).2 h)).symm
  refine ⟨?_, ?_, ?_⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, h, -, -⟩ := hloc y hy
    exact ⟨N, hN, h⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, -, h, -⟩ := hloc y hy
    exact ⟨N, hN, h⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, -, -, h⟩ := hloc y hy
    exact ⟨N, hN, h⟩

theorem tu_avg {α F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g h : ℝ → α → F} {l : α → F} {K : Set α}
    (hf : TendstoUniformlyOn f l (𝓝[>] 0) K) (hg : TendstoUniformlyOn g l (𝓝[>] 0) K)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ K, h t y = (1 / 2 : ℝ) • (f t y + g t y)) :
    TendstoUniformlyOn h l (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε, he] with t h1 h2 h3 y hy
  have e1 := h1 y hy
  have e2 := h2 y hy
  rw [dist_eq_norm] at e1 e2 ⊢
  have : l y - h t y = (1 / 2 : ℝ) • ((l y - f t y) + (l y - g t y)) := by
    rw [h3 y hy]; module
  rw [this, norm_smul]
  have := norm_add_le (l y - f t y) (l y - g t y)
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
  linarith

theorem fderiv_avg {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f g h : E → F} (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (hg : ∀ y ∈ U, DifferentiableAt ℝ g y) (he : ∀ y ∈ U, h y = (1 / 2 : ℝ) • (f y + g y)) :
    ∀ y ∈ U, fderiv ℝ h y = (1 / 2 : ℝ) • (fderiv ℝ f y + fderiv ℝ g y) := by
  intro y hy
  have hev : h =ᶠ[𝓝 y] fun z => (1 / 2 : ℝ) • (f z + g z) := Filter.mem_of_superset (hU.mem_nhds hy) he
  rw [hev.fderiv_eq]
  exact (((hf y hy).hasFDerivAt.add (hg y hy).hasFDerivAt).const_smul (1 / 2 : ℝ)).fderiv

theorem regular_family_average {A : FinHolAtlas e X} {s : X → X → ℂ} {ph : X → ℝ} {f g : ℝ → X → ℝ}
    (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (f t)) (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t))
    (h1 : IsRegFamilyC2 A s ph f) (h2 : IsRegFamilyC2 A s ph g) :
    IsRegFamilyC2 A s ph fun t y => (f t y + g t y) / 2 := by
  intro j K hKs hK
  obtain ⟨a0, a1, a2⟩ := h1 j K hKs hK
  obtain ⟨b0, b1, b2⟩ := h2 j K hKs hK
  have hO := (A.chart j).open_target
  have e0 : ∀ t, ∀ y ∈ (A.chart j).target, ((fun y => (f t y + g t y) / 2) ∘ (A.chart j).symm) y =
      (1 / 2 : ℝ) • ((f t ∘ (A.chart j).symm) y + (g t ∘ (A.chart j).symm) y) := by
    intro t y _
    simp only [Function.comp_apply, smul_eq_mul]; ring
  have sm : ∀ u : X → ℝ, A.Smooth u → ∀ y ∈ (A.chart j).target, ContDiffAt ℝ ∞ (u ∘ (A.chart j).symm) y :=
    fun u hu y hy => GlobalTheory.CompanionTheory.Ar.Giv.contDiffAt_of_smoothOn isOpen_univ hu j hy trivial
  have e1 := fun t (hf : A.Smooth (f t)) (hg : A.Smooth (g t)) => fderiv_avg hO
    (fun y hy => (sm _ hf y hy).differentiableAt (by simp))
    (fun y hy => (sm _ hg y hy).differentiableAt (by simp)) (e0 t)
  have e2 := fun t (hf : A.Smooth (f t)) (hg : A.Smooth (g t)) => fderiv_avg hO
    (fun y hy => ((sm _ hf y hy).fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp))
    (fun y hy => ((sm _ hg y hy).fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)) (e1 t hf hg)
  refine ⟨tu_avg a0 b0 (Eventually.of_forall fun t y hy => e0 t y (hKs hy).1), tu_avg a1 b1 ?_, tu_avg a2 b2 ?_⟩
  · filter_upwards [hf, hg] with t hf hg y hy using e1 t hf hg y (hKs hy).1
  · filter_upwards [hf, hg] with t hf hg y hy using e2 t hf hg y (hKs hy).1

end PositivityTheory.Xgp.an_conj

theorem PositivityTheory.Xgp.t_an_conj : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 := by
  intro e X _ _ _ A Θ L s nb m W hL hs hsnc hs0 hΘ hΘp c hc hcc ha hb hr th ph phT C t₀ hth hG hph hF hC2
  have hΘpsh : IsPsh A Θ := TailBoundAlt.isPsh_of_isPosPot A Θ hΘp
  have hΘpb : IsPotential A (Θ.pullback c hc) := PositivityTheory.Xgp.an_conj.isPotential_pull hc ha hΘ
  obtain ⟨K, hK0, -, hKpsh⟩ := TailBoundAlt.exists_psh_chern_bound A Θ (Θ.pullback c hc) hΘ hΘp hΘpb
  have ht₀ : 0 < t₀ := hF.1
  have hU : IsOpen (bdry s)ᶜ := GlobalTheory.CompanionTheory.Ar.Giv.isOpen_compl_bdry hs
  set M : ℝ := max 1 K with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : K ≤ M := le_max_right _ _
  set C' : ℝ := |C| * M with hC'
  set t₁ : ℝ := min t₀ (Real.exp (-Real.exp 1)) with ht₁
  have ht₁0 : 0 < t₁ := lt_min ht₀ (Real.exp_pos _)
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  have ht₁e : t₁ ≤ Real.exp (-Real.exp 1) := min_le_right _ _
  have hCC' : |C| ≤ C' := le_mul_of_one_le_right (abs_nonneg C) hM1
  have F1 := GlobalTheory.CompanionTheory.Ar.Giv.isRegFamily_mono A Θ L s th ph phT C t₀ |C| t₁ hΘ hΘpsh hth hs0 hF le_rfl ht₁0 ht₁t₀ ht₁e
  have F2 := GlobalTheory.CompanionTheory.Ar.Giv.isRegFamily_mono A Θ L s th ph phT C t₀ C' t₁ hΘ hΘpsh hth hs0 hF hCC' ht₁0 ht₁t₀ ht₁e
  have hsmc : ∀ u : X → ℝ, A.Smooth u → A.Smooth (u ∘ c) := fun u hu => by
    have := PositivityTheory.Xgp.an_conj.smoothOn_pull hc ha isOpen_univ hu
    rwa [Set.preimage_univ] at this
  have hnb : ∀ y ∉ bdry s, c y ∉ bdry s := fun y hy h => hy ((hb y).1 h)
  refine ⟨C', t₁, ?_, ?_⟩
  · obtain ⟨-, -, F1⟩ := F1
    obtain ⟨h1, h2, F2⟩ := F2
    refine ⟨h1, h2, fun t ht htt => ?_⟩
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8⟩ := F2 t ht htt
    obtain ⟨b1, -, -, -, b5, -⟩ := F1 t ht htt
    have hsm : A.Smooth fun y => (phT t y + phT t (c y)) / 2 := fun j =>
      ((a1 j).add (hsmc _ a1 j)).div_const 2
    refine ⟨hsm, fun y => ?_, fun y hy => ?_, fun y => ?_, ?_, fun y hy hyr => ?_, fun y hy => ?_,
      fun t' h1 h2 y => ?_⟩
    · linarith [a2 y, a2 (c y)]
    · linarith [a3 y hy, a3 (c y) (hnb y hy), hph y hy]
    · linarith [a4 y, a4 (c y)]
    · set ε : ℝ := epsT |C| t with hε
      have hq := GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg ht (htt.trans ht₁e)
      have hε0 : 0 ≤ ε := by
        rw [hε, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]; exact mul_nonneg (abs_nonneg C) hq
      have hε' : epsT C' t = M * ε := by
        rw [hε, epsT, epsT, hC']; ring
      have hεK : 0 ≤ M * ε - (K + 1) * ε / 2 := by nlinarith
      have hP0 : IsPotential A (th + LocPot.ofFun (phT t) + Θ.rsmul ε) :=
        isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ b1))
          (isPotentialRsmul A ε Θ hΘ)
      have hD : IsPotential A (Θ.rsmul K + (Θ.pullback c hc).rsmul (-1)) :=
        isPotentialAdd A _ _ (isPotentialRsmul A K Θ hΘ) (isPotentialRsmul A (-1) _ hΘpb)
      have hS0 := PositivityTheory.Xgp.an_conj.isPotential_pull hc ha hP0
      have hS0p := PositivityTheory.Xgp.an_conj.isPsh_pull hc ha hP0 b5
      have hS00 := isPotentialAdd A _ _ hP0 hS0
      have hS1 := isPotentialRsmul A (1 / 2) _ hS00
      have hS1p := isPshRsmul A (1 / 2) _ (by norm_num) hS00 (isPshAdd A _ _ hP0 hS0 b5 hS0p)
      have hS2 := isPotentialRsmul A (ε / 2) _ hD
      have hS2p := isPshRsmul A (ε / 2) _ (by positivity) hD hKpsh
      have hS3 := isPotentialRsmul A (M * ε - (K + 1) * ε / 2) Θ hΘ
      have hS3p := isPshRsmul A (M * ε - (K + 1) * ε / 2) Θ hεK hΘ hΘpsh
      have hS := isPshAdd A _ _ (isPotentialAdd A _ _ hS1 hS2) hS3
        (isPshAdd A _ _ hS1 hS2 hS1p hS2p) hS3p
      have hT : IsPotential A (th + LocPot.ofFun (fun y => (phT t y + phT t (c y)) / 2) + Θ.rsmul (epsT C' t)) :=
        isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ hsm)) (isPotentialRsmul A _ Θ hΘ)
      refine PositivityTheory.Xgp.an_conj.isPsh_of_same (isPotentialAdd A _ _ (isPotentialAdd A _ _ hS1 hS2) hS3) hT
        (fun x => ?_) hS
      obtain ⟨V, hV, hxV, G, hGh, hGe⟩ := hG x
      refine ⟨V, hV, hxV, G, hGh, fun y hy => ?_⟩
      show th.φ x y + (phT t y + phT t (c y)) / 2 + epsT C' t * Θ.φ x y =
        1 / 2 * ((th.φ x y + phT t y + ε * Θ.φ x y) + (th.φ (c x) (c y) + phT t (c y) + ε * Θ.φ (c x) (c y))) +
        ε / 2 * (K * Θ.φ x y + -1 * Θ.φ (c x) (c y)) + (M * ε - (K + 1) * ε / 2) * Θ.φ x y + -1 / 2 * (G y).re
      rw [hε', ← hGe y hy]
      ring
    · have := a6 (c y) (hnb y hy) (by rw [hr]; exact hyr)
      linarith [a6 y hy hyr, hph y hy]
    · have := a7 (c y) (hnb y hy)
      rw [hr] at this
      linarith [a7 y hy, hph y hy]
    · linarith [a8 t' h1 h2 y, a8 t' h1 h2 (c y)]
  · have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT ht₀) fun t ht => (hF.2.2 t ht.1 ht.2).1
    exact PositivityTheory.Xgp.an_conj.regular_family_average (g := fun t => phT t ∘ c) hev (hev.mono fun t => hsmc _) hC2
      (PositivityTheory.Xgp.an_conj.regular_family_pullback_involution hc ha hU hb hph hev hC2)
