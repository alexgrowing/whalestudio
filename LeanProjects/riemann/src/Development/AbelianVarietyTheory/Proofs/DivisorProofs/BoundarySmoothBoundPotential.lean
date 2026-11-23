import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryLocalChartExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPotentialContinuousOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCompAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCongrOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimsupMaxAddTendstoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothContinuousLimsupExtEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComplementOpenDenseStatement

open Filter Topology Metric

namespace GlobalTheory.BdryChart

theorem psh_near_boundary : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W → ∀ (Θ : ReciprocityTheory.AnForm.M.LocPot Y) (u : Y → ℝ) (C₁ : ℝ), ReciprocityTheory.AnForm.M.IsPotential A Θ → A.SmoothOn (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) u → GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.SumNonnegOn A Θ u (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) → (∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s, u y ≤ C₁ * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y)) → ∀ (x : Y) (j : Fin A.n) (z₀ : Fin D → ℂ), z₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.chartPart A j (Θ.U x) → (A.chart j).symm z₀ ∉ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → ∃ V : Set (Fin D → ℂ), IsOpen V ∧ z₀ ∈ V ∧ (∃ M : ℝ, ∀ z ∈ V, (A.chart j).symm z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → u ((A.chart j).symm z) ≤ M) ∧ ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh V (fun z => (max (((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal) + GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) u ((A.chart j).symm z)) ((-κ : ℝ) : EReal)).toReal) := by
  intro D Y _ _ _ A L s m W hB Θ u C₁ hΘ hsm hnn hgr x j z₀ hz₀ hy₀
  obtain ⟨hopen, hdense⟩ := GlobalTheory.T.boundary_complement_open_dense D Y A L s m W hB
  have hz₀t : z₀ ∈ (A.chart j).target := hz₀.1
  have hy₀U : (A.chart j).symm z₀ ∈ Θ.U x := hz₀.2
  obtain ⟨Φ, S, K, a, hΦc, hy₀s, hΦ0, hΦt, hK, hsK, hKN, hiff, ha, hlog⟩ :=
    GlobalTheory.T.boundary_local_chart_exists D Y A L s m W hB ((A.chart j).symm z₀) (Θ.U x) (Θ.isOpen_U x) hy₀U
  have hcΘ : ContinuousOn (Θ.φ x) (Θ.U x) :=
    (GlobalTheory.T.smooth_continuous_limsup_ext_eq D Y A (Θ.U x) (Θ.φ x) (Θ.isOpen_U x) (hΘ.1 x)).1
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn (hcΘ.mono hKN)
  have hBy : ∀ y ∈ Φ.source, |Θ.φ x y| ≤ |B| := fun y hy =>
    le_trans (by simpa [Real.norm_eq_abs] using hBd y (hsK hy)) (le_abs_self B)
  have hset : Metric.ball (0 : Fin D → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S =
      Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) := by
    ext w; constructor
    · rintro ⟨hw, hwc⟩
      rw [← hΦt] at hw
      have hs := Φ.map_target hw
      refine ⟨hw, hKN (hsK hs), ?_⟩
      rw [hiff _ hs, Φ.right_inv hw]; exact hwc
    · rintro ⟨hw, -, hwo⟩
      have hs := Φ.map_target hw
      refine ⟨hΦt ▸ hw, ?_⟩
      have := (hiff _ hs).1 hwo
      rwa [Φ.right_inv hw] at this
  obtain ⟨-, hGc, hGp, -⟩ :=
    GlobalTheory.T.chart_potential_continuous_on D Y A Θ u (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) x Φ hopen hΘ hsm hnn hΦc
  rw [← hset] at hGc hGp
  have hgrowth : ∀ w ∈ Metric.ball (0 : Fin D → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S,
      2 * Θ.φ x (Φ.symm w) + u (Φ.symm w) ≤ (2 * |B| + max C₁ 0 * a) *
        Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖w i‖⁻¹) := by
    intro w hw
    have hw' : w ∈ Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) := hset ▸ hw
    have hys : Φ.symm w ∈ Φ.source := Φ.map_target hw'.1
    have hΦy : Φ (Φ.symm w) = w := Φ.right_inv hw'.1
    have hsum : 0 ≤ ∑ i ∈ S, Real.log ‖w i‖⁻¹ := Finset.sum_nonneg fun i hi => by
      have hwi : w i ≠ 0 := fun h => hw.2 ⟨i, hi, h⟩
      have h1 : ‖w i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm w i) (by simpa using hw.1)
      have h0 : 0 < ‖w i‖ := norm_pos_iff.2 hwi
      exact Real.log_nonneg (one_le_inv₀ h0 |>.2 h1.le)
    have hℓ : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖w i‖⁻¹) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (by linarith)
    have hr : 1 ≤ Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s (Φ.symm w)) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.exp_one_le_rad hB _)
    have h1 := hgr _ hw'.2.2
    have h2 := hlog _ hys hw'.2.2
    rw [hΦy] at h2
    have h3 := hBy _ hys
    have h4 : C₁ * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s (Φ.symm w)) ≤
        max C₁ 0 * (a * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖w i‖⁻¹)) :=
      calc C₁ * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s (Φ.symm w))
          ≤ max C₁ 0 * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s (Φ.symm w)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    have h5 : |B| ≤ |B| * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖w i‖⁻¹) :=
      le_mul_of_one_le_right (abs_nonneg B) hℓ
    have h6 := le_abs_self (Θ.φ x (Φ.symm w))
    nlinarith
  obtain ⟨hbdd, hpsh⟩ := ReciprocityTheory.AnForm.A.pshExtension_thm D S (Metric.ball 0 1)
    (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) (2 * |B| + max C₁ 0 * a)
    Metric.isOpen_ball subset_rfl hGc hGp hgrowth
  obtain ⟨M', hM'⟩ := hbdd (Metric.closedBall 0 (1 / 2)) (isCompact_closedBall 0 _)
    (Metric.closedBall_subset_ball (by norm_num))
  have hub : ∀ y ∈ Φ.source, Φ y ∈ Metric.ball (0 : Fin D → ℂ) (1 / 2) →
      y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → u y ≤ M' + 2 * |B| := by
    intro y hys hyb hyo
    have hwc : Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S := (hiff y hys).1 hyo
    have := hM' ⟨Φ y, ⟨Metric.ball_subset_closedBall hyb, hwc⟩, rfl⟩
    simp only [Φ.left_inv hys] at this
    have h3 := hBy y hys
    linarith [neg_abs_le (Θ.φ x y)]
  have hVo : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Φ.source ∩ Φ ⁻¹' Metric.ball 0 (1 / 2))) :=
    (A.chart j).isOpen_inter_preimage_symm (Φ.isOpen_inter_preimage Metric.isOpen_ball)
  refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' (Φ.source ∩ Φ ⁻¹' Metric.ball 0 (1 / 2)),
    hVo, ⟨hz₀t, hy₀s, by simp [hΦ0]⟩, ⟨M' + 2 * |B|, fun z hz hzo => hub _ hz.2.1 hz.2.2 hzo⟩, ?_⟩
  intro κ
  have han : AnalyticOnNhd ℂ (Φ ∘ (A.chart j).symm) ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Φ.source ∩ Φ ⁻¹' Metric.ball 0 (1 / 2))) :=
    (hΦc j).1.mono fun z hz => ⟨hz.1, hz.2.1⟩
  have hmaps : Set.MapsTo (Φ ∘ (A.chart j).symm) ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Φ.source ∩ Φ ⁻¹' Metric.ball 0 (1 / 2))) (Metric.ball 0 1) :=
    fun z hz => hΦt ▸ Φ.map_source hz.2.1
  have hcomp := GlobalTheory.T.isPsh_comp_analytic D D (Metric.ball 0 1) _ _ _ Metric.isOpen_ball hVo (hpsh κ) han hmaps
  refine GlobalTheory.T.isPsh_congr_divisor D _ _ _ hcomp ?_
  intro z hz
  have hys : (A.chart j).symm z ∈ Φ.source := hz.2.1
  have hyU : (A.chart j).symm z ∈ Θ.U x := hKN (hsK hys)
  have hwb : Φ ((A.chart j).symm z) ∈ Metric.ball (0 : Fin D → ℂ) 1 := hΦt ▸ Φ.map_source hys
  have hcoe : ∀ a b : ℝ, (max ((a : EReal)) (b : EReal)).toReal = max a b := fun a b => by
    rw [← (EReal.coe_strictMono.monotone).map_max, EReal.toReal_coe]
  by_cases hyo : (A.chart j).symm z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s
  · have hwc : Φ ((A.chart j).symm z) ∉ ReciprocityTheory.AnForm.A.coordDiv S := (hiff _ hys).1 hyo
    have hls := (GlobalTheory.T.smooth_continuous_limsup_ext_eq D Y A _ u hopen hsm).2 _ hyo
    simp only [Function.comp, ReciprocityTheory.AnForm.A.limsupExt, hwc, if_false, Φ.left_inv hys, hls]
    rw [← EReal.coe_add, hcoe]
  · have hwc : Φ ((A.chart j).symm z) ∈ ReciprocityTheory.AnForm.A.coordDiv S := by
      by_contra h; exact hyo ((hiff _ hys).2 h)
    haveI : (𝓝[GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s] ((A.chart j).symm z)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (hdense _)
    have hmap : Filter.map Φ.symm (𝓝[Metric.ball 0 1 \ ReciprocityTheory.AnForm.A.coordDiv S]
        (Φ ((A.chart j).symm z))) = 𝓝[GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s] ((A.chart j).symm z) := by
      have hmt : Φ ((A.chart j).symm z) ∈ Φ.symm.source := Φ.map_source hys
      rw [Φ.symm.map_nhdsWithin_eq hmt, Φ.left_inv hys]
      have himg : Φ.symm '' (Φ.symm.source ∩ (Metric.ball 0 1 \ ReciprocityTheory.AnForm.A.coordDiv S)) =
          GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s ∩ Φ.source := by
        rw [hset]
        ext t; constructor
        · rintro ⟨w, ⟨-, hwt, -, hwo⟩, rfl⟩
          exact ⟨hwo, Φ.map_target hwt⟩
        · rintro ⟨hto, hts⟩
          exact ⟨Φ t, ⟨Φ.map_source hts, Φ.map_source hts, by
            simp only [Set.mem_preimage, Φ.left_inv hts]; exact ⟨hKN (hsK hts), hto⟩⟩, Φ.left_inv hts⟩
      rw [himg, ← nhdsWithin_restrict' _ (Φ.open_source.mem_nhds hys)]
    have hev : ∀ᶠ t in 𝓝[GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s] ((A.chart j).symm z), u t ≤ M' + 2 * |B| := by
      have hO : Φ.source ∩ Φ ⁻¹' Metric.ball 0 (1 / 2) ∈ 𝓝 ((A.chart j).symm z) :=
        (Φ.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hys, hz.2.2⟩
      exact eventually_nhdsWithin_iff.2
        (Filter.mem_of_superset hO fun t ht hto => hub t ht.1 ht.2 hto)
    have hten : Filter.Tendsto (fun t => 2 * Θ.φ x t) (𝓝[GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s] ((A.chart j).symm z))
        (𝓝 (2 * Θ.φ x ((A.chart j).symm z))) :=
      (((hcΘ.continuousAt ((Θ.isOpen_U x).mem_nhds hyU)).tendsto).const_mul 2).mono_left
        nhdsWithin_le_nhds
    have key := GlobalTheory.T.limsup_max_add_tendsto Y _ (fun t => 2 * Θ.φ x t) u _ κ _ hten hev
    simp only [Function.comp, ReciprocityTheory.AnForm.A.limsupExt, hwc, if_true, GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt]
    rw [← key, ← hmap, ← Filter.limsup_comp (fun t => max (2 * Θ.φ x t + u t) (-κ)) Φ.symm]
    rfl

end GlobalTheory.BdryChart
