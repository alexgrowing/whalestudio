import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StChartLeviThGe
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (contDiffOn_compat analyticAt_compat)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

namespace ChartLeviThGe

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem compat_chart (A : FinHolAtlas D X) (a : Fin A.n) : IsCompatChart A (A.chart a) :=
  fun j => ⟨A.holo j a, A.holo a j⟩

theorem eventuallyEq_comp_chart {β : Type*} (h : X → β) (ψ χ : OpenPartialHomeomorph X (Fin D → ℂ))
    {y : Fin D → ℂ} (hy : y ∈ χ.target) (hs : χ.symm y ∈ ψ.source) :
    h ∘ χ.symm =ᶠ[𝓝 y] (h ∘ ψ.symm) ∘ (ψ ∘ χ.symm) := by
  filter_upwards [(χ.continuousAt_symm hy).preimage_mem_nhds (ψ.open_source.mem_nhds hs)]
    with z hz
  simp [Function.comp, ψ.left_inv hz]

theorem contDiffAt_comp_symm {U : Set X} (hU : IsOpen U) {h : X → ℝ} (hh : A.SmoothOn U h)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {p : X} (hpU : p ∈ U)
    (hpψ : p ∈ ψ.source) : ContDiffAt ℝ 2 (h ∘ ψ.symm) (ψ p) := by
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target hU
  exact ((contDiffOn_compat hψ hU hh).contDiffAt
    (hO.mem_nhds ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using hpU⟩)).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem analyticAt_comp_compat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {F : X → E} {a : Fin A.n}
    {p : X} (hpa : p ∈ (A.chart a).source) (hpψ : p ∈ ψ.source)
    (hF : AnalyticAt ℂ (F ∘ (A.chart a).symm) (A.chart a p)) :
    AnalyticAt ℂ (F ∘ ψ.symm) (ψ p) := by
  have h1 : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using hpa⟩
  have h2 : AnalyticAt ℂ ((F ∘ (A.chart a).symm) ∘ (A.chart a ∘ ψ.symm)) (ψ p) :=
    hF.comp_of_eq h1 (by simp [ψ.left_inv hpψ])
  refine h2.congr ?_
  filter_upwards [(ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
    (by rw [ψ.left_inv hpψ]; exact (A.chart a).open_source.mem_nhds hpa)] with z hz
  simp [Function.comp, (A.chart a).left_inv hz]

theorem fderiv_compat_eq_zero {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ)
    {a : Fin A.n} {p : X} (ha : p ∈ (A.chart a).source) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ}
    (h : fderiv ℂ (A.chart a ∘ ψ.symm) (ψ p) v = 0) : v = 0 := by
  have hu : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using ha⟩
  have huy : (A.chart a ∘ ψ.symm) (ψ p) = A.chart a p := by simp [ψ.left_inv hpψ]
  have ht : AnalyticAt ℂ (ψ ∘ (A.chart a).symm) ((A.chart a ∘ ψ.symm) (ψ p)) := by
    rw [huy]; exact analyticAt_compat hψ a ha hpψ
  have hid : (ψ ∘ (A.chart a).symm) ∘ (A.chart a ∘ ψ.symm) =ᶠ[𝓝 (ψ p)] id := by
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hpψ),
      (ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
        (by rw [ψ.left_inv hpψ]; exact (A.chart a).open_source.mem_nhds ha)] with z hz1 hz2
    simp [Function.comp, (A.chart a).left_inv hz2, ψ.right_inv hz1]
  have hD := fderiv_comp (ψ p) ht.differentiableAt hu.differentiableAt
  rw [hid.fderiv_eq, fderiv_id] at hD
  have := congrArg (fun L => L v) hD
  simpa [h] using this

variable {om : LocPot X}

theorem levi_base_indep (hpot : IsPotential A om) {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
    (hψ : IsCompatChart A ψ) {x x' p : X} (hx : p ∈ om.U x) (hx' : p ∈ om.U x')
    (hpψ : p ∈ ψ.source) (v : Fin D → ℂ) :
    levi (om.φ x ∘ ψ.symm) (ψ p) v = levi (om.φ x' ∘ ψ.symm) (ψ p) v := by
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := hpot.2 x x' p ⟨hx, hx'⟩
  obtain ⟨a, ha⟩ := A.cover p
  have hGa : AnalyticAt ℂ (G ∘ ψ.symm) (ψ p) :=
    analyticAt_comp_compat hψ ha hpψ
      (hG a _ ⟨(A.chart a).map_source ha, by simpa [(A.chart a).left_inv ha] using hpW⟩)
  have hN : W ∩ om.U x ∩ om.U x' ∈ 𝓝 p :=
    ((hWo.inter (om.isOpen_U x)).inter (om.isOpen_U x')).mem_nhds ⟨⟨hpW, hx⟩, hx'⟩
  have hev : om.φ x ∘ ψ.symm =ᶠ[𝓝 (ψ p)]
      fun z => (om.φ x' ∘ ψ.symm) z + 1 * (G (ψ.symm z)).re := by
    filter_upwards [(ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
      (by rwa [ψ.left_inv hpψ])] with z hz
    have := hEq _ hz
    simp only [Function.comp]
    linarith
  have hre : ContDiffAt ℝ 2 (fun z => (G (ψ.symm z)).re) (ψ p) := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp (ψ p)
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun z => (G (ψ.symm z)).re) (ψ p) v = 0 := levi_re_analytic hGa v
  rw [levi_congr hev v, levi_add_smul 1
    (contDiffAt_comp_symm (om.isOpen_U x') (hpot.1 x') hψ hx' hpψ) hre v, h0]
  ring

theorem levi_pos_compat (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {x p : X}
    (hpx : p ∈ om.U x) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ} (hv : v ≠ 0) :
    0 < levi (om.φ x ∘ ψ.symm) (ψ p) v := by
  obtain ⟨a, ha⟩ := A.cover p
  have hu : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using ha⟩
  have huy : (A.chart a ∘ ψ.symm) (ψ p) = A.chart a p := by simp [ψ.left_inv hpψ]
  have hev := eventuallyEq_comp_chart (om.φ x) (A.chart a) ψ (ψ.map_source hpψ)
    (by rwa [ψ.left_inv hpψ])
  have hcd : ContDiffAt ℝ 2 (om.φ x ∘ (A.chart a).symm) ((A.chart a ∘ ψ.symm) (ψ p)) := by
    rw [huy]; exact contDiffAt_comp_symm (om.isOpen_U x) (hpot.1 x) (compat_chart A a) hpx ha
  rw [levi_congr hev v, levi_comp v hu hcd, huy]
  refine hpos x a _ ⟨(A.chart a).map_source ha, by simpa [(A.chart a).left_inv ha] using hpx⟩ _ ?_
  intro h0
  exact hv (fderiv_compat_eq_zero hψ ha hpψ h0)

theorem continuousAt_levi_self (hpot : IsPotential A om) {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
    (hψ : IsCompatChart A ψ) {p0 : X} (hp0 : p0 ∈ ψ.source) (v0 : Fin D → ℂ) :
    ContinuousAt (fun q : X × (Fin D → ℂ) => levi (om.φ q.1 ∘ ψ.symm) (ψ q.1) q.2) (p0, v0) := by
  have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' om.U p0) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (om.isOpen_U p0)
  have hcd : ContDiffOn ℝ 2 (om.φ p0 ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' om.U p0) :=
    (contDiffOn_compat hψ (om.isOpen_U p0) (hpot.1 p0)).of_le (WithTop.coe_le_coe.2 le_top)
  have hc := continuousOn_levi hV hcd
  have hmem : (ψ p0, v0) ∈ (ψ.target ∩ ψ.symm ⁻¹' om.U p0) ×ˢ (Set.univ : Set (Fin D → ℂ)) :=
    ⟨⟨ψ.map_source hp0, by simpa [ψ.left_inv hp0] using om.mem_U p0⟩, trivial⟩
  have h1 : ContinuousAt (fun r : (Fin D → ℂ) × (Fin D → ℂ) => levi (om.φ p0 ∘ ψ.symm) r.1 r.2)
      (ψ p0, v0) := hc.continuousAt ((hV.prod isOpen_univ).mem_nhds hmem)
  have h2 : ContinuousAt (fun q : X × (Fin D → ℂ) => (ψ q.1, q.2)) (p0, v0) :=
    ((ψ.continuousAt hp0).comp continuousAt_fst).prodMk continuousAt_snd
  refine (ContinuousAt.comp (g := fun r : (Fin D → ℂ) × (Fin D → ℂ) => levi (om.φ p0 ∘ ψ.symm) r.1 r.2)
    (f := fun q : X × (Fin D → ℂ) => (ψ q.1, q.2)) h1 h2).congr ?_
  have hN : (om.U p0 ∩ ψ.source) ×ˢ (Set.univ : Set (Fin D → ℂ)) ∈ 𝓝 (p0, v0) :=
    (((om.isOpen_U p0).inter ψ.open_source).prod isOpen_univ).mem_nhds ⟨⟨om.mem_U p0, hp0⟩, trivial⟩
  filter_upwards [hN] with q hq
  exact (levi_base_indep hpot hψ (om.mem_U q.1) hq.1.1 hq.1.2 q.2).symm

theorem exists_levi_lower (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {K : Set X}
    (hK : IsCompact K) (hKs : K ⊆ ψ.source) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x, p ∈ om.U x → ∀ v : Fin D → ℂ,
      c * ‖v‖ ^ 2 ≤ levi (om.φ x ∘ ψ.symm) (ψ p) v := by
  have hunit : ∀ v : Fin D → ℂ, v ≠ 0 → ‖‖v‖⁻¹ • v‖ = 1 := fun v hv => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  by_cases hne : (K ×ˢ sphere (0 : Fin D → ℂ) 1).Nonempty
  · have hcont : ContinuousOn (fun q : X × (Fin D → ℂ) => levi (om.φ q.1 ∘ ψ.symm) (ψ q.1) q.2)
        (K ×ˢ sphere (0 : Fin D → ℂ) 1) := fun q hq =>
      (continuousAt_levi_self hpot hψ (hKs hq.1) q.2).continuousWithinAt
    obtain ⟨q1, hq1, hmin⟩ := (hK.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
    have hq1v : q1.2 ≠ 0 := by
      intro h0
      have := hq1.2
      rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
      exact zero_ne_one this
    refine ⟨_, levi_pos_compat hpot hpos hψ (om.mem_U q1.1) (hKs hq1.1) hq1v, ?_⟩
    intro p hp x hx v
    rw [levi_base_indep hpot hψ hx (om.mem_U p) (hKs hp) v]
    by_cases hv : v = 0
    · subst hv; simp [levi_zero]
    have hm := isMinOn_iff.1 hmin (p, ‖v‖⁻¹ • v) ⟨hp, by rw [mem_sphere_zero_iff_norm]; exact hunit v hv⟩
    have hw : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]
    have hs : levi (om.φ p ∘ ψ.symm) (ψ p) v =
        ‖v‖ ^ 2 * levi (om.φ p ∘ ψ.symm) (ψ p) (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hw]
      exact levi_smul_dir _ _ _ _
    rw [hs, mul_comm]
    exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  · refine ⟨1, one_pos, fun p hp x hx v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp [levi_zero]
    exact absurd ⟨(p, ‖v‖⁻¹ • v), hp, by rw [mem_sphere_zero_iff_norm]; exact hunit v hv⟩ hne

end ChartLeviThGe

open ChartLeviThGe in

theorem ChartLeviThGe.proof : ChartLeviThGe.Statement := by
  intro X _ _ _ D A P om hpot hpos
  have hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ P.mid k, ∀ x, p ∈ om.U x →
      ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (om.φ x ∘ (P.chart k).symm) (P.chart k p) v := by
    intro k
    obtain ⟨c, hc0, hc⟩ := exists_levi_lower hpot hpos (P.compat k) isClosed_closure.isCompact
      (P.closure_mid k)
    exact ⟨c, hc0, fun p hp => hc p (subset_closure hp)⟩
  choose c hc0 hc using hc
  have hS : 0 ≤ ∑ k, 1 / c k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (hc0 k)).le
  have hc00 : 0 < 1 / (1 + ∑ k, 1 / c k) := one_div_pos.2 (by linarith)
  have hle : ∀ k, 1 / (1 + ∑ k, 1 / c k) ≤ c k := by
    intro k
    have h1 : 1 / c k ≤ 1 + ∑ j, 1 / c j := by
      have := Finset.single_le_sum (f := fun j => 1 / c j)
        (fun j _ => (one_div_pos.2 (hc0 j)).le) (Finset.mem_univ k)
      linarith
    calc 1 / (1 + ∑ j, 1 / c j) ≤ 1 / (1 / c k) := one_div_le_one_div_of_le (one_div_pos.2 (hc0 k)) h1
      _ = c k := one_div_one_div _
  refine ⟨_, hc00, fun f a ha hf hyp => ?_⟩
  intro x k' y hy w
  set c0 := 1 / (1 + ∑ k, 1 / c k) with hc0def
  set p := (A.chart k').symm y with hpdef
  have hpA : p ∈ (A.chart k').source := (A.chart k').map_target hy.1
  have hyA : A.chart k' p = y := (A.chart k').right_inv hy.1
  obtain ⟨hpθ, hpω⟩ := hy.2
  obtain ⟨k, hk⟩ := P.cover p
  have hkm : p ∈ P.mid k := P.inner_subset_mid k hk
  have hks : p ∈ (P.chart k).source := P.mid_subset_source k hkm
  have hg : AnalyticAt ℂ (P.chart k ∘ (A.chart k').symm) y := by
    have := analyticAt_compat (P.compat k) k' hpA hks
    rwa [hyA] at this
  have hgy : (P.chart k ∘ (A.chart k').symm) y = P.chart k p := rfl

  have hω : c0 * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2 ≤
      levi (om.φ x ∘ (A.chart k').symm) y w := by
    have hev := eventuallyEq_comp_chart (om.φ x) (P.chart k) (A.chart k') hy.1 hks
    have hcd : ContDiffAt ℝ 2 (om.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart k').symm) y) :=
      contDiffAt_comp_symm (om.isOpen_U x) (hpot.1 x) (P.compat k) hpω hks
    rw [levi_congr hev w, levi_comp w hg hcd, hgy]
    exact (mul_le_mul_of_nonneg_right (hle k) (sq_nonneg _)).trans (hc k p hkm x hpω _)

  have hθ : -a * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2 ≤
      levi ((fun z => P.th.φ x z + f z) ∘ (A.chart k').symm) y w := by
    obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := P.q_th k x p ⟨hpθ, hks⟩
    have hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 p :=
      ((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hpθ⟩, hks⟩
    have hev : (fun z => P.th.φ x z + f z) ∘ (A.chart k').symm =ᶠ[𝓝 y]
        fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart k').symm)) y' +
          (-1) * (G ((A.chart k').symm y')).re := by
      filter_upwards [((A.chart k').continuousAt_symm hy.1).preimage_mem_nhds hN] with y' hy'
      have h1 := hEq _ hy'
      simp only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]
      linarith
    have hGa : AnalyticAt ℂ (G ∘ (A.chart k').symm) y := hG k' y ⟨hy.1, hpW⟩
    have hcf : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart k').symm) y) := by
      have hq : ContDiffAt ℝ 2 (P.q k) (P.chart k p) :=
        ((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds
          ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)
      have hfψ := contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ p) hks
      exact hq.add hfψ
    have hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart k').symm)) y :=
      hcf.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)
    have hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart k').symm y')).re) y := by
      have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
        ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
      simpa [Function.comp_def] using this
    have h0 : levi (fun y' => (G ((A.chart k').symm y')).re) y w = 0 := levi_re_analytic hGa w
    rw [levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf, hgy]
    have := hyp k p hkm (fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w)
    linarith
  have hac : 0 ≤ a / c0 := div_nonneg ha hc00.le
  have h1 : -(a / c0) * levi (om.φ x ∘ (A.chart k').symm) y w ≤
      -(a / c0) * (c0 * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2) :=
    mul_le_mul_of_nonpos_left hω (by linarith)
  have h2 : -(a / c0) * (c0 * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2) =
      -a * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2 := by
    field_simp
  linarith

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
