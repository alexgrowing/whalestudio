import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)

noncomputable section

namespace RegChartData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)

open Classical in

theorem glue_eventually (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      R.regularised ρ K t ε η y =
        regMax ε (fun j : {j // x₀ ∈ R.mid j} => R.phReg ρ K t j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      (x₀ ∉ R.mid j → y ∉ L j ∧ y ∉ closure (R.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ R.mid j
    · filter_upwards [(R.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (R.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (R.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (R.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [RegChartData.regularised, PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ R.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ R.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := R.cover y
  have hk0 : x₀ ∈ R.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ R.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, R.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

theorem arg_contDiffAt (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin R.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ R.mid j) :
    ContDiffAt ℝ ∞ (fun y => R.phReg ρ K t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by
  have hxj : x ∈ (R.chart j).source := R.mid_subset_source j hj
  have hT : ContDiffAt ℝ ∞ (R.chart j ∘ ψ.symm) (ψ x) :=
    ((analyticAt_transition hψ (R.compat j) hx hxj).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hTx : (R.chart j ∘ ψ.symm) (ψ x) = R.chart j x := by simp [ψ.left_inv hx]
  have hS := (R.smoothed_local ρ K ht j (hball j x (subset_closure hj))).1
  have hq : ContDiffAt ℝ ∞ (R.q j) (R.chart j x) :=
    (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds ((R.chart j).map_source hxj))
  rw [← hTx] at hS hq
  have hη := contDiffAt_comp_symm_of_smoothOn hψ (R.isOpen_mid j) (hcut.smooth j) hj hx
  exact ((hS.comp (ψ x) hT).sub (hq.comp (ψ x) hT)).add (contDiffAt_const.mul hη)

end RegChartData

open Classical in

theorem GlueRegularised.proof : GlueRegularised.Statement := by
  intro X _ _ _ D A R ρ η Cη K t ε hcut ht hε hball hcmp
  refine ⟨fun i y hy => ?_, fun k x hx w => ?_⟩
  ·
    have hyt : y ∈ (A.chart i).target := hy.1
    have hx₀ : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hyt
    have hψ : IsCompatChart A (A.chart i) := fun l => ⟨A.holo l i, A.holo i l⟩
    have hyx : A.chart i ((A.chart i).symm y) = y := (A.chart i).right_inv hyt
    have hloc := R.glue_eventually ρ η hcut hε.le hcmp ((A.chart i).symm y)
    have hG : ContDiffAt ℝ ∞ (fun y' => regMax ε (fun j : {j // (A.chart i).symm y ∈ R.mid j} =>
        R.phReg ρ K t j ((A.chart i).symm y') + 4 * ε * η j ((A.chart i).symm y')) + ε / 2) y := by
      have hr := ((ReciprocityTheory.AnForm.A.regMax_thm {j // (A.chart i).symm y ∈ R.mid j}).1 ε hε).1
      refine (hr.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).add contDiffAt_const
      have := R.arg_contDiffAt ρ η (K := K) (ε := ε) hcut ht hball hψ hx₀ j.2
      rwa [hyx] at this
    refine (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (((A.chart i).continuousAt_symm hyt).tendsto.eventually hloc).mono fun y' hy' => hy'.2
  ·
    have hψ := R.compat k
    have hxk : x ∈ (R.chart k).source := R.mid_subset_source k hx
    have hzt : R.chart k x ∈ (R.chart k).target := (R.chart k).map_source hxk
    have hqk : ContDiffAt ℝ ∞ (R.q k) (R.chart k x) :=
      (R.q_smooth k).contDiffAt ((R.chart k).open_target.mem_nhds hzt)
    set b : {j // x ∈ R.mid j} → (Fin D → ℂ) → ℝ := fun j y =>
      R.phReg ρ K t j ((R.chart k).symm y) + 4 * ε * η j ((R.chart k).symm y) + R.q k y with hb_def
    have hb : ∀ j, ContDiffAt ℝ ∞ (b j) (R.chart k x) := fun j =>
      (R.arg_contDiffAt ρ η (K := K) (ε := ε) hcut ht hball hψ hxk j.2).add hqk
    have hadd := ((ReciprocityTheory.AnForm.A.regMax_thm {j // x ∈ R.mid j}).1 ε hε).2.2.2.2.2.2.1
    have hgerm : R.chartFun (R.regularised ρ K t ε η) k =ᶠ[𝓝 (R.chart k x)]
        fun y => regMax ε (fun j => b j y) + ε / 2 := by
      have hloc := R.glue_eventually ρ η hcut hε.le hcmp x
      have ht' : Tendsto (R.chart k).symm (𝓝 (R.chart k x)) (𝓝 x) := by
        have := ((R.chart k).continuousAt_symm hzt).tendsto
        rwa [(R.chart k).left_inv hxk] at this
      filter_upwards [ht'.eventually hloc] with y hy
      simp only [PotentialCharts.chartFun]
      rw [hy.2, hb_def, hadd]
      ring
    have hconst : levi (fun y => regMax ε (fun j => b j y) + ε / 2) (R.chart k x) w =
        levi (fun y => regMax ε (fun j => b j y)) (R.chart k x) w := by
      unfold levi
      have : fderiv ℝ (fun y => regMax ε (fun j => b j y) + ε / 2) =
          fderiv ℝ (fun y => regMax ε (fun j => b j y)) := funext fun _ => fderiv_add_const _
      rw [this]
    rw [levi_congr hgerm w, hconst]
    have hzV : R.chart k x ∈ interior {y | ∀ j, ContDiffAt ℝ 2 (b j) y} :=
      mem_interior_iff_mem_nhds.2 (Filter.eventually_all.2 fun j =>
        ((hb j).of_le (WithTop.coe_le_coe.mpr le_top)).eventually (by simp))
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm D {j // x ∈ R.mid j} ε _ b isOpen_interior hε
      (fun j y hy => (interior_subset hy j).contDiffWithinAt) _ hzV w _ fun ⟨j, hj⟩ => ?_
    have hxj : x ∈ (R.chart j).source := R.mid_subset_source j hj
    set T := R.chart j ∘ (R.chart k).symm with hT
    have hTa : AnalyticAt ℂ T (R.chart k x) := analyticAt_transition hψ (R.compat j) hxk hxj
    have hTR : ContDiffAt ℝ ∞ T (R.chart k x) := (hTa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have hTz : T (R.chart k x) = R.chart j x := by simp [hT, (R.chart k).left_inv hxk]
    obtain ⟨hS, hSl⟩ := R.smoothed_local ρ K ht j (hball j x (subset_closure hj))
    have hq : ContDiffAt ℝ ∞ (R.q j) (R.chart j x) :=
      (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds ((R.chart j).map_source hxj))
    rw [← hTz] at hS hSl hq
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hS2 : ContDiffAt ℝ 2 (R.smoothed ρ K t j ∘ T) (R.chart k x) := (hS.comp _ hTR).of_le h2
    have hQ2 : ContDiffAt ℝ 2 (fun y => R.q k y - R.q j (T y)) (R.chart k x) :=
      (hqk.sub (hq.comp _ hTR)).of_le h2
    have hE2 : ContDiffAt ℝ 2 (η j ∘ (R.chart k).symm) (R.chart k x) :=
      (contDiffAt_comp_symm_of_smoothOn hψ (R.isOpen_mid j) (hcut.smooth j) hj hxk).of_le h2
    have hF2 : ContDiffAt ℝ 2 (fun y => (R.smoothed ρ K t j ∘ T) y + 1 * (R.q k y - R.q j (T y)))
        (R.chart k x) := hS2.add (contDiffAt_const.mul hQ2)
    have hbe : b ⟨j, hj⟩ = fun y => ((R.smoothed ρ K t j ∘ T) y + 1 * (R.q k y - R.q j (T y))) +
        4 * ε * (η j ∘ (R.chart k).symm) y := by
      funext y
      simp only [hb_def, RegChartData.phReg, hT, Function.comp_apply]
      ring
    have e1 := levi_add_smul (4 * ε) hF2 hE2 w
    have e2 := levi_add_smul 1 hS2 hQ2 w
    have e3 := levi_comp (φ := R.smoothed ρ K t j) w hTa (hS.of_le h2)

    have e4 : levi (fun y => R.q k y - R.q j (T y)) (R.chart k x) w = 0 := by
      obtain ⟨W, hWo, hxW, G, hG, hGeq⟩ := R.q_th k x x ⟨R.th.mem_U x, hxk⟩
      obtain ⟨W', hWo', hxW', G', hG', hGeq'⟩ := R.q_th j x x ⟨R.th.mem_U x, hxj⟩
      have hO : IsOpen (W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source) :=
        (((hWo.inter hWo').inter (R.th.isOpen_U x)).inter (R.chart k).open_source).inter
          (R.chart j).open_source
      have hxO : x ∈ W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source :=
        ⟨⟨⟨⟨hxW, hxW'⟩, R.th.mem_U x⟩, hxk⟩, hxj⟩
      have hev1 : ∀ᶠ y in 𝓝 (R.chart k x),
          (R.chart k).symm y ∈ W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source :=
        ((R.chart k).continuousAt_symm hzt).preimage_mem_nhds
          (by rw [(R.chart k).left_inv hxk]; exact hO.mem_nhds hxO)
      have hev := hev1.and ((R.chart k).open_target.mem_nhds hzt)
      have hGa := analyticAt_comp_symm_of_holoOn hψ hG hxW hxk
      have hGa' := analyticAt_comp_symm_of_holoOn hψ hG' hxW' hxk
      have hgerm : (fun y => R.q k y - R.q j (T y)) =ᶠ[𝓝 (R.chart k x)]
          fun y => (((G ∘ (R.chart k).symm) - (G' ∘ (R.chart k).symm)) y).re := by
        filter_upwards [hev] with y hy
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hyt⟩ := hy
        have ek := hGeq _ ⟨⟨h1, h3⟩, h4⟩
        have ej := hGeq' _ ⟨⟨h2, h3⟩, h5⟩
        rw [(R.chart k).right_inv hyt] at ek
        simp only [hT, Function.comp_apply, Pi.sub_apply, Complex.sub_re]
        linarith
      rw [levi_congr hgerm w]
      exact levi_re_analytic (hGa.sub hGa') w
    have hl := hcut.levi_ge j k x ⟨hj, hx⟩ w
    have h4 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 4 * ε)
    have h0 := hSl (fderiv ℂ T (R.chart k x) w)
    rw [hbe, e1, e2, e3, e4]
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
