import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli regMax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)

noncomputable section

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

open Classical in

theorem glue_eventually_of_close (a : Fin P.N → X → ℝ) (η : Fin P.N → X → ℝ) {Cη ε : ℝ}
    (hcut : P.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ P.mid j ∩ P.mid k, |a j x - a k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      P.glue (fun j x => a j x + 4 * ε * η j x) ε y =
        regMax ε (fun j : {j // x₀ ∈ P.mid j} => a j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      (x₀ ∉ P.mid j → y ∉ L j ∧ y ∉ closure (P.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ P.mid j
    · filter_upwards [(P.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (P.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (P.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (P.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ P.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ P.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := P.cover y
  have hk0 : x₀ ∈ P.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ P.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, P.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

end PotentialCharts

namespace BoundedPshData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

theorem smoothed_local (ρ : Mollifier D) {t : ℝ} (ht : 0 < t) (j : Fin B.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (B.chart j).target) :
    ContDiffAt ℝ ∞ (B.smoothed ρ t j) z ∧ ∀ w, 0 ≤ levi (B.smoothed ρ t j) z w := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall z t).exists_cthickening_subset_open (B.chart j).open_target hz
  rw [cthickening_closedBall hδ.le ht.le] at hδsub
  have hU'sub : ball z (δ + t) ⊆ (B.chart j).target := ball_subset_closedBall.trans hδsub
  have hpsh : IsPsh (ball z (δ + t)) (B.u j) := isPsh_mono (B.u_psh j) hU'sub
  obtain ⟨hopen, hsm, hpm, -⟩ :=
    (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ (B.u j) isOpen_ball hpsh).1 t ht
  have hz' : z ∈ shrink (ball z (δ + t)) t := closedBall_subset_ball (lt_add_of_pos_left t hδ)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ hopen
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm
  exact ⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩

theorem arg_contDiffAt (ρ : Mollifier D) (η : Fin B.N → X → ℝ) {Cη t ε : ℝ}
    (hcut : B.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin B.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ B.mid j) :
    ContDiffAt ℝ ∞ (fun y => B.phReg ρ t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by
  have hxj : x ∈ (B.chart j).source := B.mid_subset_source j hj
  have hT : ContDiffAt ℝ ∞ (B.chart j ∘ ψ.symm) (ψ x) :=
    ((analyticAt_transition hψ (B.compat j) hx hxj).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hTx : (B.chart j ∘ ψ.symm) (ψ x) = B.chart j x := by simp [ψ.left_inv hx]
  have hS := (B.smoothed_local ρ ht j (hball j x (subset_closure hj))).1
  have hq : ContDiffAt ℝ ∞ (B.q j) (B.chart j x) :=
    (B.q_smooth j).contDiffAt ((B.chart j).open_target.mem_nhds ((B.chart j).map_source hxj))
  rw [← hTx] at hS hq
  have hη := contDiffAt_comp_symm_of_smoothOn hψ (B.isOpen_mid j) (hcut.smooth j) hj hx
  exact ((hS.comp (ψ x) hT).sub (hq.comp (ψ x) hT)).add (contDiffAt_const.mul hη)

end BoundedPshData

open Classical in

theorem BoundedGlue.proof : BoundedGlue.Statement := by
  intro X _ _ _ D A B ρ η Cη t ε hcut ht hε hball hcmp
  have hloc := B.glue_eventually_of_close (fun j x => B.phReg ρ t j x) η hcut hε.le hcmp
  refine ⟨fun i y hy => ?_, fun k x hx w => ?_⟩
  ·
    have hyt : y ∈ (A.chart i).target := hy.1
    have hx₀ : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hyt
    have hψ : IsCompatChart A (A.chart i) := fun l => ⟨A.holo l i, A.holo i l⟩
    have hyx : A.chart i ((A.chart i).symm y) = y := (A.chart i).right_inv hyt
    have hG : ContDiffAt ℝ ∞ (fun y' => regMax ε (fun j : {j // (A.chart i).symm y ∈ B.mid j} =>
        B.phReg ρ t j ((A.chart i).symm y') + 4 * ε * η j ((A.chart i).symm y')) + ε / 2) y := by
      have hr := ((ReciprocityTheory.AnForm.A.regMax_thm {j // (A.chart i).symm y ∈ B.mid j}).1 ε hε).1
      refine (hr.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).add contDiffAt_const
      have := B.arg_contDiffAt ρ η (ε := ε) hcut ht hball hψ hx₀ j.2
      rwa [hyx] at this
    refine (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (((A.chart i).continuousAt_symm hyt).tendsto.eventually (hloc ((A.chart i).symm y))).mono
      fun y' hy' => hy'.2
  ·
    have hψ := B.compat k
    have hxk : x ∈ (B.chart k).source := B.mid_subset_source k hx
    have hzt : B.chart k x ∈ (B.chart k).target := (B.chart k).map_source hxk
    have hqk : ContDiffAt ℝ ∞ (B.q k) (B.chart k x) :=
      (B.q_smooth k).contDiffAt ((B.chart k).open_target.mem_nhds hzt)
    set b : {j // x ∈ B.mid j} → (Fin D → ℂ) → ℝ := fun j y =>
      B.phReg ρ t j ((B.chart k).symm y) + 4 * ε * η j ((B.chart k).symm y) + B.q k y with hb_def
    have hb : ∀ j, ContDiffAt ℝ ∞ (b j) (B.chart k x) := fun j =>
      (B.arg_contDiffAt ρ η (ε := ε) hcut ht hball hψ hxk j.2).add hqk
    have hadd := ((ReciprocityTheory.AnForm.A.regMax_thm {j // x ∈ B.mid j}).1 ε hε).2.2.2.2.2.2.1
    have hgerm : B.chartFun (B.regularised ρ t ε η) k =ᶠ[𝓝 (B.chart k x)]
        fun y => regMax ε (fun j => b j y) + ε / 2 := by
      have ht' : Tendsto (B.chart k).symm (𝓝 (B.chart k x)) (𝓝 x) := by
        have := ((B.chart k).continuousAt_symm hzt).tendsto
        rwa [(B.chart k).left_inv hxk] at this
      filter_upwards [ht'.eventually (hloc x)] with y hy
      simp only [PotentialCharts.chartFun, BoundedPshData.regularised]
      rw [hy.2, hb_def, hadd]
      ring
    have hconst : levi (fun y => regMax ε (fun j => b j y) + ε / 2) (B.chart k x) w =
        levi (fun y => regMax ε (fun j => b j y)) (B.chart k x) w := by
      unfold levi
      have : fderiv ℝ (fun y => regMax ε (fun j => b j y) + ε / 2) =
          fderiv ℝ (fun y => regMax ε (fun j => b j y)) := funext fun _ => fderiv_add_const _
      rw [this]
    rw [levi_congr hgerm w, hconst]
    have hzV : B.chart k x ∈ interior {y | ∀ j, ContDiffAt ℝ 2 (b j) y} :=
      mem_interior_iff_mem_nhds.2 (Filter.eventually_all.2 fun j =>
        ((hb j).of_le (WithTop.coe_le_coe.mpr le_top)).eventually (by simp))
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm D {j // x ∈ B.mid j} ε _ b isOpen_interior hε
      (fun j y hy => (interior_subset hy j).contDiffWithinAt) _ hzV w _ fun ⟨j, hj⟩ => ?_
    have hxj : x ∈ (B.chart j).source := B.mid_subset_source j hj
    set T := B.chart j ∘ (B.chart k).symm with hT
    have hTa : AnalyticAt ℂ T (B.chart k x) := analyticAt_transition hψ (B.compat j) hxk hxj
    have hTR : ContDiffAt ℝ ∞ T (B.chart k x) := (hTa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have hTz : T (B.chart k x) = B.chart j x := by simp [hT, (B.chart k).left_inv hxk]
    obtain ⟨hS, hSl⟩ := B.smoothed_local ρ ht j (hball j x (subset_closure hj))
    have hq : ContDiffAt ℝ ∞ (B.q j) (B.chart j x) :=
      (B.q_smooth j).contDiffAt ((B.chart j).open_target.mem_nhds ((B.chart j).map_source hxj))
    rw [← hTz] at hS hSl hq
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hS2 : ContDiffAt ℝ 2 (B.smoothed ρ t j ∘ T) (B.chart k x) := (hS.comp _ hTR).of_le h2
    have hQ2 : ContDiffAt ℝ 2 (fun y => B.q k y - B.q j (T y)) (B.chart k x) :=
      (hqk.sub (hq.comp _ hTR)).of_le h2
    have hE2 : ContDiffAt ℝ 2 (η j ∘ (B.chart k).symm) (B.chart k x) :=
      (contDiffAt_comp_symm_of_smoothOn hψ (B.isOpen_mid j) (hcut.smooth j) hj hxk).of_le h2
    have hF2 : ContDiffAt ℝ 2 (fun y => (B.smoothed ρ t j ∘ T) y + 1 * (B.q k y - B.q j (T y)))
        (B.chart k x) := hS2.add (contDiffAt_const.mul hQ2)
    have hbe : b ⟨j, hj⟩ = fun y => ((B.smoothed ρ t j ∘ T) y + 1 * (B.q k y - B.q j (T y))) +
        4 * ε * (η j ∘ (B.chart k).symm) y := by
      funext y
      simp only [hb_def, BoundedPshData.phReg, hT, Function.comp_apply]
      ring
    have e1 := levi_add_smul (4 * ε) hF2 hE2 w
    have e2 := levi_add_smul 1 hS2 hQ2 w
    have e3 := levi_comp (φ := B.smoothed ρ t j) w hTa (hS.of_le h2)

    have e4 : levi (fun y => B.q k y - B.q j (T y)) (B.chart k x) w = 0 := by
      obtain ⟨W, hWo, hxW, G, hG, hGeq⟩ := B.q_th k x x ⟨B.th.mem_U x, hxk⟩
      obtain ⟨W', hWo', hxW', G', hG', hGeq'⟩ := B.q_th j x x ⟨B.th.mem_U x, hxj⟩
      have hO : IsOpen (W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source) :=
        (((hWo.inter hWo').inter (B.th.isOpen_U x)).inter (B.chart k).open_source).inter
          (B.chart j).open_source
      have hxO : x ∈ W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source :=
        ⟨⟨⟨⟨hxW, hxW'⟩, B.th.mem_U x⟩, hxk⟩, hxj⟩
      have hev1 : ∀ᶠ y in 𝓝 (B.chart k x),
          (B.chart k).symm y ∈ W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source :=
        ((B.chart k).continuousAt_symm hzt).preimage_mem_nhds
          (by rw [(B.chart k).left_inv hxk]; exact hO.mem_nhds hxO)
      have hev := hev1.and ((B.chart k).open_target.mem_nhds hzt)
      have hGa := analyticAt_comp_symm_of_holoOn hψ hG hxW hxk
      have hGa' := analyticAt_comp_symm_of_holoOn hψ hG' hxW' hxk
      have hgerm : (fun y => B.q k y - B.q j (T y)) =ᶠ[𝓝 (B.chart k x)]
          fun y => (((G ∘ (B.chart k).symm) - (G' ∘ (B.chart k).symm)) y).re := by
        filter_upwards [hev] with y hy
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hyt⟩ := hy
        have ek := hGeq _ ⟨⟨h1, h3⟩, h4⟩
        have ej := hGeq' _ ⟨⟨h2, h3⟩, h5⟩
        rw [(B.chart k).right_inv hyt] at ek
        simp only [hT, Function.comp_apply, Pi.sub_apply, Complex.sub_re]
        linarith
      rw [levi_congr hgerm w]
      exact levi_re_analytic (hGa.sub hGa') w
    have hl := hcut.levi_ge j k x ⟨hj, hx⟩ w
    have h4 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 4 * ε)
    have h0 := hSl (fderiv ℂ T (B.chart k x) w)
    rw [hbe, e1, e2, e3, e4]
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
