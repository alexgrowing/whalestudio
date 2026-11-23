import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRefAlongSheet
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_holoOn_comp_chartSymm {e m : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : ReciprocityTheory.AnForm.M.IsCompatChart A ψ) {V : Set X}
    {F : X → ℂ} (hF : A.HoloOn V F) {g : (Fin m → ℂ) → Fin e → ℂ} {y : Fin m → ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y ∈ ψ.target) (hV : ψ.symm (g y) ∈ V) :
    AnalyticAt ℂ (fun y' => F (ψ.symm (g y'))) y := by
  obtain ⟨i, hi⟩ := A.cover (ψ.symm (g y))
  have hτ : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (g y) := (hψ i).2 (g y) ⟨hgy, hi⟩
  have hFi : AnalyticAt ℂ (F ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (g y)) := by
    refine hF i _ ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i (ψ.symm (g y))) ∈ V
    rw [(A.chart i).left_inv hi]
    exact hV
  refine ((hFi.comp hτ).comp hg).congr ?_
  have hc : ContinuousAt (fun y' => ψ.symm (g y')) y := (ψ.continuousAt_symm hgy).comp hg.continuousAt
  filter_upwards [hc.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)] with y' hy'
  simp only [Function.comp_apply, (A.chart i).left_inv hy']

theorem RefAlongSheet.proof : RefAlongSheet.Statement := by
  intro K _ ι _ P n M Xo A S γ y j hγ hsrc hev
  classical
  obtain ⟨g, hg'⟩ : ∃ g : (Fin n → ℂ) → Fin n → ℂ, g = fun y'' => S.R.chart j (M.proj (γ y'')) := ⟨_, rfl⟩
  have hg : AnalyticAt ℂ g y := by
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hev.mono fun _ h => h.2)
    refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => g w i) hVo (fun z hz => ?_) y hyV
    rw [hg']
    exact (differentiableAt_pi.mp (hV z hz) i).differentiableWithinAt
  have hγc : ∀ p, AnalyticAt ℂ (fun w => γ w p) y := by
    intro p
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hγ.mono fun _ h => h.1)
    exact ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => γ w p) hVo
      (fun z hz => (differentiableAt_pi.mp (hV z hz) p).differentiableWithinAt) y hyV
  have hgy : g y ∈ (S.R.chart j).target := by rw [hg']; exact (S.R.chart j).map_source hsrc
  have hxy : (S.R.chart j).symm (g y) = M.proj (γ y) := by rw [hg']; exact (S.R.chart j).left_inv hsrc
  obtain ⟨U, hUo, hx0U, hUth, s, hs, hsh, G1, hG1, hG1eq⟩ :=
    S.th_ref (M.proj (γ y)) (M.proj (γ y)) (S.R.th.mem_U _)
  obtain ⟨W, hWo, hx0W, G2, hG2, hG2eq⟩ := S.R.q_th j (M.proj (γ y)) (M.proj (γ y)) ⟨S.R.th.mem_U _, hsrc⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (Fin n → ℂ) → M.Xc, x' = fun y' => (S.R.chart j).symm (g y') := ⟨_, rfl⟩
  have hsxy : x' y = M.proj (γ y) := by rw [hx']; exact hxy
  have hx'c : ContinuousAt x' y := by
    rw [hx']; exact ((S.R.chart j).continuousAt_symm hgy).comp hg.continuousAt
  have hsc : ∀ p, AnalyticAt ℂ (fun y' => s (x' y') p) y := fun p => by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) (hsh p) hg hgy (by rw [hxy]; exact hx0U)
  have hG1x : AnalyticAt ℂ (fun y' => G1 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG1 hg hgy (by rw [hxy]; exact hx0U)
  have hG2x : AnalyticAt ℂ (fun y' => G2 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG2 hg hgy (by rw [hxy]; exact hx0W)
  have hs0 : s (M.proj (γ y)) ∈ mcPts P := (hs _ hx0U).1
  choose i hi using hs0.1
  obtain ⟨cf, hcf⟩ : ∃ cf : K → (Fin n → ℂ) → ℂ,
      cf = fun k y' => γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ := ⟨_, rfl⟩
  have hsi : ∀ k, s (x' y) ⟨k, i k⟩ ≠ 0 := fun k => by rw [hsxy]; exact hi k
  have hcfa : ∀ k, AnalyticAt ℂ (cf k) y := fun k => by
    rw [hcf]; exact (hγc _).div (hsc _) (hsi k)
  have hne : ∀ᶠ y' in 𝓝 y, ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hsc _).continuousAt.eventually_ne (hsi k)
  have hUWn : U ∩ W ∈ 𝓝 (x' y) := (hUo.inter hWo).mem_nhds (by rw [hsxy]; exact ⟨hx0U, hx0W⟩)
  have hgood : ∀ᶠ y' in 𝓝 y, (x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 := by
    filter_upwards [hx'c.preimage_mem_nhds hUWn, hev, hγ, hne] with y' h1 h2 h3 h4
    exact ⟨⟨h1, h2.1, h3.2⟩, h4⟩
  have key : ∀ y', ((x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0) →
      (∀ k, cf k y' ≠ 0) ∧ Real.log (S.ref.h (γ y')) = ∑ k, (S.ref.a k : ℝ) * Real.log ‖cf k y'‖ +
        (S.R.q j (S.R.chart j (M.proj (γ y'))) - (G2 (x' y')).re - (G1 (x' y')).re) := by
    rintro y' ⟨⟨⟨hU', hW'⟩, hsrc', hγ'⟩, hne'⟩
    have hxp : x' y' = M.proj (γ y') := by rw [hx', hg']; exact (S.R.chart j).left_inv hsrc'
    obtain ⟨hsm, hsp⟩ := hs _ hU'
    obtain ⟨c, hc, hγc'⟩ := (M.fibre _ hsm _ hγ').1 (by rw [hsp, hxp])
    have hck : ∀ k, cf k y' = c k := fun k => by
      have h := congrFun hγc' ⟨k, i k⟩
      rw [hcf]
      show γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ = c k
      rw [h]
      exact mul_div_cancel_right₀ (c k) (hne' k)
    have hh : S.ref.h (γ y') = (∏ k, ‖c k‖ ^ S.ref.a k) * S.ref.h (s (x' y')) := by
      rw [hγc']; exact S.ref.smul c _ hc
    have hpos : ∀ k, 0 < ‖c k‖ := fun k => norm_pos_iff.2 (hc k)
    have hlog : Real.log (S.ref.h (γ y')) =
        ∑ k, (S.ref.a k : ℝ) * Real.log ‖c k‖ + Real.log (S.ref.h (s (x' y'))) := by
      rw [hh, Real.log_mul (Finset.prod_pos fun k _ => zpow_pos (hpos k) _).ne' (S.ref.pos _ hsm.1).ne',
        Real.log_prod fun k _ => (zpow_pos (hpos k) _).ne']
      simp only [Real.log_zpow]
    have h1 := hG1eq _ hU'
    have hsrc'' : x' y' ∈ (S.R.chart j).source := by rw [hxp]; exact hsrc'
    have h2 := hG2eq _ ⟨⟨hW', hUth hU'⟩, hsrc''⟩
    refine ⟨fun k => by rw [hck]; exact hc k, ?_⟩
    rw [hlog, ← hxp]
    simp only [hck]
    linarith
  have hcy : ∀ k, cf k y ≠ 0 := (key y hgood.self_of_nhds).1
  refine ⟨fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) * (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ)) -
    (G1 (x' y') + G2 (x' y')), ?_, ?_⟩
  · have hterm : ∀ k, AnalyticAt ℂ (fun y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := fun k => by
      have hl : AnalyticAt ℂ (fun y' => Complex.log (cf k y' / cf k y)) y := by
        refine ((hcfa k).div analyticAt_const (hcy k)).clog ?_
        show cf k y / cf k y ∈ Complex.slitPlane
        rw [div_self (hcy k)]
        exact Complex.one_mem_slitPlane
      exact analyticAt_const.mul (hl.add analyticAt_const)
    have hsum : AnalyticAt ℂ (fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := by
      have h := Finset.analyticAt_sum (𝕜 := ℂ) (f := fun k y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) Finset.univ fun k _ => hterm k
      convert h using 1
      ext y'
      simp [Finset.sum_apply]
    have hG12 : AnalyticAt ℂ (fun y' => G1 (x' y') + G2 (x' y')) y := hG1x.add hG2x
    exact hsum.sub hG12
  · filter_upwards [hgood] with y' hy'
    obtain ⟨hnz, heq⟩ := key y' hy'
    rw [heq]
    have hl : ∀ k, Real.log ‖cf k y' / cf k y‖ = Real.log ‖cf k y'‖ - Real.log ‖cf k y‖ := fun k => by
      rw [norm_div, Real.log_div (norm_ne_zero_iff.2 (hnz k)) (norm_ne_zero_iff.2 (hcy k))]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re,
      Complex.ofReal_re, hl, sub_add_cancel]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
