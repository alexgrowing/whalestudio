import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.KaehlerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

noncomputable section

theorem two_le_smooth_kb : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast

theorem regChartData_isCompact_univ {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) : IsCompact (Set.univ : Set X) := by
  have hK : ∀ j, IsCompact ((R.ψ j).symm '' closure (R.W'' j)) := fun j => by
    have hc : IsCompact (closure (R.W'' j)) :=
      (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
        ((R.closure_W''_subset j).trans subset_closure)
    refine hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono ?_)
    exact (R.closure_W''_subset j).trans (subset_closure.trans
      ((R.closure_W'_subset j).trans (R.W_subset j)))
  refine (isCompact_iUnion hK).of_isClosed_subset isClosed_univ fun x _ => ?_
  obtain ⟨j, hx, hxW⟩ := R.cover x
  exact Set.mem_iUnion.2 ⟨j, R.ψ j x, subset_closure hxW, (R.ψ j).left_inv hx⟩

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_abs_le_local (A : FinHolAtlas D X) (θ om : LocPot X) (hθ : IsPotential A θ)
    (hom : IsPotential A om) (hpos : IsPosPot A om) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ M : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (θ.U p ∩ om.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin D → ℂ,
        |levi (θ.φ p ∘ (A.chart j).symm) y u| ≤ M * levi (om.φ p ∘ (A.chart j).symm) y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (θ.U p ∩ om.U p) with hO
  have hOo : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    ((θ.isOpen_U p).inter (om.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨θ.mem_U p, om.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have homs : ContDiffOn ℝ 2 (om.φ p ∘ c.symm) O :=
    ((hom.1 p j).mono fun y hy => ⟨hy.1, hy.2.2⟩).of_le two_le_smooth_kb
  have hθs : ContDiffOn ℝ 2 (θ.φ p ∘ c.symm) O :=
    ((hθ.1 p j).mono fun y hy => ⟨hy.1, hy.2.1⟩).of_le two_le_smooth_kb
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin D → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (om.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.2⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin D → ℂ) × (Fin D → ℂ) =>
      |levi (θ.φ p ∘ c.symm) q.1 q.2| / levi (om.φ p ∘ c.symm) q.1 q.2) K :=
    (((continuousOn_levi hOo hθs).mono hKO).abs).div ((continuousOn_levi hOo homs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨M, hM⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, M, hcb, fun y hy u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin D → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin D → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : |levi (θ.φ p ∘ c.symm) y v| / levi (om.φ p ∘ c.symm) y v ≤ M :=
      hM ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : |levi (θ.φ p ∘ c.symm) y v| ≤ M * levi (om.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg s)]
    have : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith

theorem levi_abs_le_global (A : FinHolAtlas D X) (hX : IsCompact (Set.univ : Set X))
    (θ om : LocPot X) (hθ : IsPotential A θ) (hom : IsPotential A om) (hpos : IsPosPot A om) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (θ.U x ∩ om.U x),
      ∀ v : Fin D → ℂ,
        |levi (θ.φ x ∘ (A.chart k).symm) y v| ≤ M * levi (om.φ x ∘ (A.chart k).symm) y v := by
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)
  have key := fun p => levi_abs_le_local A θ om hθ hom hpos p (chartIdx A p) (hsrc p)
  choose r hr m hsub hbd using key
  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := hX.elim_finite_subcover V hVo
    (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Metric.mem_ball_self (hr p)⟩)
  refine ⟨∑ p ∈ t, |m p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro x k y hy v
  set C := ∑ p ∈ t, |m p| with hC
  obtain ⟨hyk, hyU⟩ := hy
  have hqθ : (A.chart k).symm y ∈ θ.U x := hyU.1
  have hqom : (A.chart k).symm y ∈ om.U x := hyU.2
  set q := (A.chart k).symm y with hq
  obtain ⟨p, hpt, hqV⟩ : ∃ p ∈ t, q ∈ V p := by
    simpa using ht (Set.mem_univ q)
  set j := chartIdx A p with hj
  set c := A.chart j with hc
  have hqs : q ∈ c.source := hqV.1
  have hqb : c q ∈ Metric.ball (c p) (r p) := hqV.2
  have hcqO := hsub p (Metric.ball_subset_closedBall hqb)
  have hqp : q ∈ θ.U p ∩ om.U p := by
    have := hcqO.2; rwa [Set.mem_preimage, c.left_inv hqs] at this
  have hcqt : c q ∈ c.target := c.map_source hqs
  have hsc : c.symm (c q) = q := c.left_inv hqs
  set τ := c ∘ (A.chart k).symm with hτd
  have hτ : AnalyticAt ℂ τ y := A.holo k j y ⟨hyk, hqs⟩
  have hτy : τ y = c q := rfl
  have hsrcev : ∀ᶠ y' in 𝓝 y, (A.chart k).symm y' ∈ c.source :=
    ((A.chart k).continuousAt_symm hyk).preimage_mem_nhds (c.open_source.mem_nhds hqs)
  have hgerm : ∀ f : X → ℝ, f ∘ (A.chart k).symm =ᶠ[𝓝 y] (f ∘ c.symm) ∘ τ := fun f => by
    filter_upwards [hsrcev] with y' hy'
    simp only [Function.comp_apply, τ, c.left_inv hy']
  have hsm : ∀ P : LocPot X, IsPotential A P → ∀ z, q ∈ P.U z →
      ContDiffAt ℝ 2 (P.φ z ∘ c.symm) (c q) := by
    intro P hP z hz
    have hOz : IsOpen (c.target ∩ c.symm ⁻¹' P.U z) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target (P.isOpen_U z)
    exact ((hP.1 z j).of_le two_le_smooth_kb).contDiffAt
      (hOz.mem_nhds ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hz⟩)
  have hbase : ∀ P : LocPot X, IsPotential A P → q ∈ P.U x → q ∈ P.U p → ∀ u : Fin D → ℂ,
      levi (P.φ x ∘ c.symm) (c q) u = levi (P.φ p ∘ c.symm) (c q) u := by
    intro P hP hx hp u
    obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hP.2 x p q ⟨hx, hp⟩
    have hGa : AnalyticAt ℂ (G ∘ c.symm) (c q) :=
      hG j (c q) ⟨hcqt, by show c.symm (c q) ∈ W; rw [hsc]; exact hqW⟩
    have hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ c.symm) z).re) (c q) := by
      have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp (c q)
        (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
      simpa [Function.comp_def] using this
    have hev : P.φ x ∘ c.symm =ᶠ[𝓝 (c q)]
        fun z => (P.φ p ∘ c.symm) z + 1 * ((G ∘ c.symm) z).re := by
      have hopen : IsOpen (W ∩ P.U x ∩ P.U p) :=
        (hWo.inter (P.isOpen_U x)).inter (P.isOpen_U p)
      have : ∀ᶠ z in 𝓝 (c q), c.symm z ∈ W ∩ P.U x ∩ P.U p :=
        (c.continuousAt_symm hcqt).preimage_mem_nhds
          (hopen.mem_nhds (by rw [hsc]; exact ⟨⟨hqW, hx⟩, hp⟩))
      filter_upwards [this] with z hz
      have := hGeq (c.symm z) hz
      simp only [Function.comp_apply, one_mul]
      linarith
    rw [levi_congr hev, levi_add_smul 1 (hsm P hP p hp) hRe, levi_re_analytic hGa]
    ring
  have htr : ∀ P : LocPot X, IsPotential A P → q ∈ P.U x → q ∈ P.U p →
      levi (P.φ x ∘ (A.chart k).symm) y v = levi (P.φ p ∘ c.symm) (c q) (fderiv ℂ τ y v) := by
    intro P hP hx hp
    rw [levi_congr (hgerm _), levi_comp v hτ (by rw [hτy]; exact hsm P hP x hx), hτy,
      hbase P hP hx hp]
  have hb := hbd p (c q) (Metric.ball_subset_closedBall hqb) (fderiv ℂ τ y v)
  have hLom : 0 ≤ levi (om.φ p ∘ c.symm) (c q) (fderiv ℂ τ y v) := by
    rcases eq_or_ne (fderiv ℂ τ y v) 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (hpos p j (c q) ⟨hcqt, hcqO.2.2⟩ _ h0).le
  have hCm : m p ≤ C :=
    (le_abs_self (m p)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt)
  rw [htr θ hθ hqθ hqp.1, htr om hom hqom hqp.2]
  nlinarith

theorem KaehlerBound.proof : KaehlerBound.Statement := by
  intro D X _ A R
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A (regChartData_isCompact_univ R) R.θ R.om R.θ_pot
    R.om_pot R.om_pos
  have hK : (0 : ℝ) < M + 1 := by linarith
  have hsm : ∀ P : LocPot X, IsPotential A P → ∀ x k,
      ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x,
        ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y := fun P hP x k y hy =>
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have hsmul : ∀ (P : LocPot X) (a : ℝ) x k y, ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y →
      ∀ w, levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w =
        a * levi (P.φ x ∘ (A.chart k).symm) y w := by
    intro P a x k y hy w
    have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hy w
    have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
        fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
      funext z
      simp [LocPot.rsmul]
    rw [he, h, levi_const, zero_add]
  have key : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x),
      ∀ w : Fin D → ℂ,
        levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w =
            levi (R.θ.φ x ∘ (A.chart k).symm) y w + levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w =
            (M + 1) * levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          |levi (R.θ.φ x ∘ (A.chart k).symm) y w| ≤
            M * levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          0 ≤ levi (R.om.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    have hθs := hsm R.θ R.θ_pot x k y ⟨hy.1, hy.2.1⟩
    have homs := hsm R.om R.om_pot x k y ⟨hy.1, hy.2.2⟩
    refine ⟨?_, hsmul R.om (M + 1) x k y homs w, hM x k y hy w, ?_⟩
    · have he : (thetaOmega R).φ x ∘ (A.chart k).symm = fun z =>
          (R.θ.φ x ∘ (A.chart k).symm) z + 1 * (R.om.φ x ∘ (A.chart k).symm) z := by
        funext z
        show R.θ.φ x _ + R.om.φ x _ = _
        simp
      rw [he, levi_add_smul 1 hθs homs w, one_mul]
    · rcases eq_or_ne w 0 with h0 | h0
      · rw [h0, levi_zero]
      · exact (R.om_pos x k y ⟨hy.1, hy.2.2⟩ w h0).le
  refine ⟨⟨R.om.rsmul (M + 1), ReciprocityTheory.AnForm.M.isPotentialRsmul A (M + 1) R.om R.om_pot,
    fun x k y hy w hw => ?_⟩, ?_, ?_⟩
  · rw [hsmul R.om (M + 1) x k y (hsm R.om R.om_pot x k y hy) w]
    exact mul_pos hK (R.om_pos x k y hy w hw)
  · intro x k y hy w
    have hy' : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x) :=
      ⟨hy.1, hy.2.1.2.1, hy.2.1.2.2⟩
    obtain ⟨h1, h2, h3, h4⟩ := key x k y hy' w
    show 1 * levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w ≤
      1 * levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w
    rw [h1, h2]
    have := abs_le.mp h3
    nlinarith
  · intro x k y hy w
    have hy' : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x) :=
      ⟨hy.1, hy.2.2.1, hy.2.2.2⟩
    obtain ⟨h1, h2, h3, h4⟩ := key x k y hy' w
    show -1 * levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w ≤
      1 * levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w
    rw [h1, h2]
    have := abs_le.mp h3
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
