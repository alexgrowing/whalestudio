import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeSheets
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

noncomputable section

namespace RootFieldNumerics

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace Desc

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) :
    ContinuousAt f x := by
  obtain ⟨k, hk⟩ := A.cover x
  have h1 := (hf k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ U
    rwa [(A.chart k).left_inv hk]⟩).continuousAt
  have h2 := h1.comp ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with x' hx'
  simp [(A.chart k).left_inv hx']

theorem analytic_off {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S U : Set X} {f : Y → ℂ}
    (hh : HoloMap B A h) (hd : IsDegreeOff A B h 1 S) (hf : B.HoloOn (h ⁻¹' U) f) (σ : X → Y)
    (hσ : ∀ x ∉ S, h (σ x) = x) (hσ' : ∀ y, h y ∉ S → σ (h y) = y) (k : Fin A.n) {q : Fin e → ℂ}
    (hq : q ∈ (A.chart k).target) (hU : (A.chart k).symm q ∈ U) (hS : (A.chart k).symm q ∉ S) :
    AnalyticAt ℂ (fun t => f (σ ((A.chart k).symm t))) q := by
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  set x := (A.chart k).symm q with hx
  obtain ⟨j, hj⟩ := B.cover (σ x)
  set p := B.chart j (σ x) with hp
  have hpt : p ∈ (B.chart j).target := (B.chart j).map_source hj
  have hsp : (B.chart j).symm p = σ x := (B.chart j).left_inv hj
  have hxs : x ∈ (A.chart k).source := (A.chart k).map_target hq
  have hhs : h ((B.chart j).symm p) ∈ (A.chart k).source := by rw [hsp, hσ x hS]; exact hxs
  let φ : (Fin e → ℂ) → Fin e → ℂ := A.chart k ∘ h ∘ (B.chart j).symm
  have hφ : AnalyticAt ℂ φ p := hh.2 j k p ⟨hpt, hhs⟩
  have hφp : φ p = q := by
    show A.chart k (h ((B.chart j).symm p)) = q
    rw [hsp, hσ x hS, hx, (A.chart k).right_inv hq]
  have hdet := hd.2.2.2.2.2 j k p hpt (by
    show h ((B.chart j).symm p) ∉ S
    rwa [hsp, hσ x hS]) hhs
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) := (fderiv ℂ φ p).toContinuousLinearEquivOfDetNeZero hdet
  have hL : HasFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) p := by
    have := hφ.differentiableAt.hasFDerivAt
    simpa [L] using this
  have hc : ContDiffAt ℂ ⊤ φ p := hφ.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hc.localInverse hL hn
  have hψ : AnalyticAt ℂ ψ q := by
    have := (hc.to_localInverse hL hn).analyticAt
    rwa [hφp] at this
  have hψq : ψ q = p := by
    rw [← hφp]
    exact hc.localInverse_apply_image hL hn
  have hri : ∀ᶠ t in 𝓝 q, φ (ψ t) = t := by
    have := (hc.hasStrictFDerivAt' hL hn).eventually_right_inverse
    rw [hφp] at this
    exact this
  have hfa : AnalyticAt ℂ (f ∘ (B.chart j).symm) (ψ q) := by
    rw [hψq]
    refine hf j p ⟨hpt, ?_⟩
    show h ((B.chart j).symm p) ∈ U
    rwa [hsp, hσ x hS]
  refine (hfa.comp hψ).congr ?_
  have c1 : ContinuousAt (fun t => h ((B.chart j).symm (ψ t))) q :=
    hh.1.continuousAt.comp (ContinuousAt.comp (by rw [hψq]; exact (B.chart j).continuousAt_symm hpt) hψ.continuousAt)
  have e1 : ∀ᶠ t in 𝓝 q, h ((B.chart j).symm (ψ t)) ∈ (A.chart k).source ∩ Sᶜ :=
    c1.eventually_mem (((A.chart k).open_source.inter hSc.isOpen_compl).mem_nhds (by
      show h ((B.chart j).symm (ψ q)) ∈ _
      rw [hψq, hsp, hσ x hS]
      exact ⟨hxs, hS⟩))
  filter_upwards [hri, e1] with t h1 h2
  have h3 : (A.chart k).symm t = h ((B.chart j).symm (ψ t)) := by
    rw [← (A.chart k).left_inv h2.1]
    exact congrArg _ h1.symm
  show f ((B.chart j).symm (ψ t)) = f (σ ((A.chart k).symm t))
  rw [h3, hσ' _ h2.2]

theorem local_ext {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U) (k : Fin A.n)
    (ha : ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) {q : Fin e → ℂ} (hq : q ∈ (A.chart k).target)
    (hqU : (A.chart k).symm q ∈ U) :
    ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧ ∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t) := by
  by_cases hqS : (A.chart k).symm q ∈ S
  swap
  · exact ⟨_, ha q hq hqU hqS, Eventually.of_forall fun _ _ => rfl⟩
  obtain ⟨W, hW, hqW, hWc, φ, hφ, ⟨w₀, hw₀, hw₀'⟩, hz⟩ := analyticSubset_chart_local A hS hi k (z := q)
    ⟨_, ⟨hqS, (A.chart k).map_target hq⟩, (A.chart k).right_inv hq⟩
  let U' := W ∩ ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U)
  have hU' : IsOpen U' := hW.inter ((A.chart k).isOpen_inter_preimage_symm hU)
  have hns : ∀ b ∈ U', φ b ≠ 0 → (A.chart k).symm b ∉ S := fun b hb h0 hs =>
    h0 (hz b ⟨⟨_, ⟨hs, (A.chart k).map_target hb.2.1⟩, (A.chart k).right_inv hb.2.1⟩, hb.1⟩)
  have hden : U' ⊆ closure {b ∈ U' | φ b ≠ 0} := fun b hb => by
    by_contra hn
    have h1 : ∀ᶠ b' in 𝓝 b, b' ∉ {b ∈ U' | φ b ≠ 0} := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with b' hb' h using hb' (subset_closure h)
    have h2 : φ =ᶠ[𝓝 b] 0 := by
      filter_upwards [h1, hU'.mem_nhds hb] with b' h h'
      by_contra h0
      exact h ⟨h', h0⟩
    exact hw₀' (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc hb.1 h2 hw₀)
  obtain ⟨u', hu', he⟩ := GlobalTheory.LogExt.riemann_extension_log _ U' φ (fun t => u ((A.chart k).symm t)) hU'
    (hφ.differentiableOn.mono Set.inter_subset_left)
    (fun b hb => (ha b hb.1.2.1 hb.1.2.2 (hns b hb.1 hb.2)).differentiableAt.differentiableWithinAt) hden
    (fun b hb' => by
      obtain ⟨C, hC⟩ := hb _ hb'.2.2
      refine ⟨C, 0, ?_⟩
      filter_upwards [((A.chart k).continuousAt_symm hb'.2.1).eventually hC, hU'.mem_nhds hb'] with t h1 h2 h0
      simpa using h1 (hns t h2 h0))
  have hq' : q ∈ U' := ⟨hqW, hq, hqU⟩
  refine ⟨u', GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU' hu' q hq', ?_⟩
  filter_upwards [hU'.mem_nhds hq'] with t ht hts
  have : (𝓝[{b ∈ U' | φ b ≠ 0}] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden ht)
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[{b ∈ U' | φ b ≠ 0}] t)
    ((hu'.continuousOn.continuousAt (hU'.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds)
    ((ha t ht.2.1 ht.2.2 hts).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with b hb using he hb

theorem ext_manifold {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U)
    (ha : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) :
    ∃ F : X → ℂ, A.HoloOn U F ∧ ∀ x ∈ U, x ∉ S → F x = u x := by
  have hden : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hi
  let F : X → ℂ := fun x => limUnder (𝓝[Sᶜ] x) u
  have key : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧
      (∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t)) ∧
      ∀ᶠ t in 𝓝 q, w t = F ((A.chart k).symm t) := fun k q hq hqU => by
    obtain ⟨w, hw, he⟩ := local_ext hS hi hU k (ha k) hb hq hqU
    refine ⟨w, hw, he, ?_⟩
    filter_upwards [he.eventually_nhds, hw.eventually_analyticAt, (A.chart k).open_target.mem_nhds hq] with t h1 h2 h3
    have hs := (A.chart k).map_target h3
    have hr := (A.chart k).right_inv h3
    have : (𝓝[Sᶜ] ((A.chart k).symm t)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden _)
    have hc : Tendsto (A.chart k) (𝓝 ((A.chart k).symm t)) (𝓝 t) := by
      have := ((A.chart k).continuousAt hs).tendsto
      rwa [hr] at this
    refine (Tendsto.limUnder_eq ?_).symm
    refine ((h2.continuousAt.tendsto.comp hc).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (hc.eventually h1), nhdsWithin_le_nhds ((A.chart k).open_source.mem_nhds hs),
      self_mem_nhdsWithin] with x h4 h5 h6
    have h7 : (A.chart k).symm (A.chart k x) ∉ S → w (A.chart k x) = u ((A.chart k).symm (A.chart k x)) := h4
    rw [(A.chart k).left_inv h5] at h7
    exact h7 h6
  refine ⟨F, fun k q hq => ?_, fun x hx hxS => ?_⟩
  · obtain ⟨w, hw, -, he⟩ := key k q hq.1 hq.2
    exact hw.congr he
  · obtain ⟨k, hk⟩ := A.cover x
    have hl := (A.chart k).left_inv hk
    obtain ⟨w, -, h1, h2⟩ := key k _ ((A.chart k).map_source hk) (by rwa [hl])
    have h3 := h1.self_of_nhds
    have h4 := h2.self_of_nhds
    rw [hl] at h3 h4
    rw [← h4, h3 hxS]

end Desc

open Desc in
theorem descend : Descend := by
  intro e X Y _ _ _ _ _ _ A B h S U f hh hd hU hf
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · refine ⟨0, fun k => ?_, fun y => isEmptyElim y⟩
    exact analyticOnNhd_const
  have hex : ∀ x, ∃ y, x ∉ S → h ⁻¹' {x} = {y} := fun x => by
    by_cases hx : x ∈ S
    · exact ⟨hY.some, fun h' => (h' hx).elim⟩
    · obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 x hx)
      exact ⟨y, fun _ => hy⟩
  choose σ hσ₀ using hex
  have hσ : ∀ x ∉ S, h (σ x) = x := fun x hx => by
    have : σ x ∈ h ⁻¹' {x} := by rw [hσ₀ x hx]; rfl
    exact this
  have hσ' : ∀ y, h y ∉ S → σ (h y) = y := fun y hy => by
    have : y ∈ h ⁻¹' {h y} := rfl
    rw [hσ₀ _ hy] at this
    exact this.symm
  have hfc : ContinuousOn f (h ⁻¹' U) := fun y hy => (contAt_of_holoOn B hf hy).continuousWithinAt
  obtain ⟨F, hF, he⟩ := ext_manifold (u := fun x => f (σ x)) hd.1 hd.2.1 hU
    (fun k q hq h1 h2 => analytic_off hh hd hf σ hσ hσ' k hq h1 h2) (fun x hx => by
      obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hx)
      have hc : IsCompact (h ⁻¹' K) := (hKc.isClosed.preimage hh.1).isCompact
      obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hfc.mono (Set.preimage_mono hKU))
      refine ⟨C, ?_⟩
      filter_upwards [hK] with x' h1 h2
      exact hC _ (by show h (σ x') ∈ K; rwa [hσ x' h2]))
  refine ⟨F, hF, fun y hy => ?_⟩
  have hden : Dense (h ⁻¹' S)ᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.2.2.1
  have ho : IsOpen (h ⁻¹' U) := hU.preimage hh.1
  refine Set.EqOn.of_subset_closure (f := fun y => F (h y)) (g := f) (s := h ⁻¹' U ∩ (h ⁻¹' S)ᶜ) (t := h ⁻¹' U)
    (fun y' hy' => ?_) (fun y' hy' => ?_) hfc Set.inter_subset_left (hden.open_subset_closure_inter ho) hy
  · show F (h y') = f y'
    rw [he _ hy'.1 hy'.2, hσ' _ hy'.2]
  · exact ((contAt_of_holoOn A hF hy').comp hh.1.continuousAt).continuousWithinAt

end RootFieldNumerics
