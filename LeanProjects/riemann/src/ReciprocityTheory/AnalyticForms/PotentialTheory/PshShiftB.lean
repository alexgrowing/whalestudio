import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

namespace ReciprocityTheory.AnForm.M

open Filter Topology FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.2 le_top
  | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤))
  | norm_num
  | simp
  | decide

theorem pshShift_local (A : FinHolAtlas e X) (Ω : LocPot X) (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (w : X → ℝ) (hw : A.Smooth w) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        m * levi (Ω.φ p ∘ (A.chart j).symm) y u ≤ levi (w ∘ (A.chart j).symm) y u := by
  classical
  set φ : (Fin e → ℂ) → ℝ := Ω.φ p ∘ (A.chart j).symm with hφdef
  set ψ : (Fin e → ℂ) → ℝ := w ∘ (A.chart j).symm with hψdef
  set S : Set (Fin e → ℂ) := (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p with hSdef
  have hSo : IsOpen S := (A.chart j).isOpen_inter_preimage_symm (Ω.isOpen_U p)
  have hz0 : A.chart j p ∈ S := by
    refine ⟨(A.chart j).map_source hp, ?_⟩
    show (A.chart j).symm (A.chart j p) ∈ Ω.U p
    rw [(A.chart j).left_inv hp]
    exact Ω.mem_U p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo _ hz0
  have hsub : Metric.closedBall (A.chart j p) (ε / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hφc : ContDiffOn ℝ 2 φ S := (hΩ.1 p j).of_le two_le_infty
  have hψc : ContDiffOn ℝ 2 ψ S :=
    ((hw j).of_le two_le_infty).mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩)
  have hLφ := continuousOn_levi hSo hφc
  have hLψ := continuousOn_levi hSo hψc
  set K : Set ((Fin e → ℂ) × (Fin e → ℂ)) :=
    Metric.closedBall (A.chart j p) (ε / 2) ×ˢ Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKS : K ⊆ S ×ˢ Set.univ := Set.prod_mono hsub (Set.subset_univ _)
  have hposK : ∀ q ∈ K, 0 < levi φ q.1 q.2 := by
    intro q hq
    refine hpos p j q.1 (hsub hq.1) q.2 ?_
    intro h0
    have h1 := hq.2
    rw [h0] at h1
    simp at h1
  have hg : ContinuousOn
      (fun q : (Fin e → ℂ) × (Fin e → ℂ) => levi ψ q.1 q.2 / levi φ q.1 q.2) K :=
    (hLψ.mono hKS).div (hLφ.mono hKS) (fun q hq => (hposK q hq).ne')
  obtain ⟨M, hM⟩ := hK.bddBelow_image hg
  refine ⟨ε / 2, by positivity, M, hsub, ?_⟩
  intro y hy u
  by_cases hu : u = 0
  · subst hu
    simp [levi_zero]
  · have ht : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨s, v, hv, rfl⟩ : ∃ s : ℝ, ∃ v ∈ Metric.sphere (0 : Fin e → ℂ) 1, u = s • v := by
      refine ⟨‖u‖, ‖u‖⁻¹ • u, ?_, ?_⟩
      · simp [norm_smul, hu, ht.ne']
      · simp [smul_smul, hu, ht.ne']
    have hq : ((y, v) : (Fin e → ℂ) × (Fin e → ℂ)) ∈ K := ⟨hy, hv⟩
    have h1 := hM ⟨(y, v), hq, rfl⟩
    have h2 := hposK _ hq
    simp only at h1 h2
    have h3 : M * levi φ y v ≤ levi ψ y v := by
      rwa [le_div_iff₀ h2] at h1
    rw [levi_smul_dir, levi_smul_dir]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]

theorem plurisubharmonicShift_proof : PshShiftStatement := by
  intro e X _ _ _ A Ω hΩ hpos w hw
  classical
  choose jq hjq using A.cover
  choose r hr m hsubq hlocq using fun q => pshShift_local A Ω hΩ hpos w hw q (jq q) (hjq q)
  have hVo : ∀ q, IsOpen ((A.chart (jq q)).source ∩
      A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q)) := fun q =>
    (A.chart (jq q)).continuousOn.isOpen_inter_preimage (A.chart (jq q)).open_source
      Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun q => (A.chart (jq q)).source ∩ A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q))
    hVo (fun q _ => Set.mem_iUnion.2 ⟨q, hjq q, Metric.mem_ball_self (hr q)⟩)
  refine ⟨∑ q ∈ t, |m q|, ?_⟩
  intro x k y hy u
  show 0 ≤ levi ((fun z => w z + (∑ q ∈ t, |m q|) * Ω.φ x z) ∘ (A.chart k).symm) y u
  have hyk : y ∈ (A.chart k).target := hy.1
  have hzx : (A.chart k).symm y ∈ Ω.U x :=
    (show (A.chart k).symm y ∈ Set.univ ∩ Ω.U x from hy.2).2
  obtain ⟨q, hqt, hzq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((A.chart k).symm y)))
  have hzq1 : (A.chart k).symm y ∈ (A.chart (jq q)).source ∩
      A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q) := hzq
  have hsub1 := hsubq q
  have hloc1 := hlocq q
  have hC : -m q ≤ ∑ q ∈ t, |m q| :=
    (neg_le_abs (m q)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hqt)
  generalize ∑ q ∈ t, |m q| = C at hC ⊢
  generalize jq q = jj at hzq1 hsub1 hloc1
  obtain ⟨hzj, hzb⟩ := hzq1
  have hτS : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' Ω.U q :=
    hsub1 (Metric.ball_subset_closedBall hzb)
  have hzq' : (A.chart k).symm y ∈ Ω.U q := by
    have h := hτS.2
    rwa [Set.mem_preimage, (A.chart jj).left_inv hzj] at h
  have hτx : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' Ω.U x := by
    refine ⟨(A.chart jj).map_source hzj, ?_⟩
    rw [Set.mem_preimage, (A.chart jj).left_inv hzj]
    exact hzx
  have hψ2 : ContDiffAt ℝ 2 (w ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hw jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
      ⟨(A.chart jj).map_source hzj, Set.mem_univ _⟩)).of_le two_le_infty
  have hΦx2 : ContDiffAt ℝ 2 (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hΩ.1 x jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm (Ω.isOpen_U x)).mem_nhds
      hτx)).of_le two_le_infty
  have hΦq2 : ContDiffAt ℝ 2 (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hΩ.1 q jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm (Ω.isOpen_U q)).mem_nhds
      hτS)).of_le two_le_infty
  have hτa : AnalyticAt ℂ (A.chart jj ∘ (A.chart k).symm) y := A.holo k jj y ⟨hyk, hzj⟩
  have hf2 : ContDiffAt ℝ 2 ((fun z => w z + C * Ω.φ x z) ∘ (A.chart jj).symm)
      ((A.chart jj ∘ (A.chart k).symm) y) := hψ2.add (contDiffAt_const.mul hΦx2)
  have hev1 : (fun z => w z + C * Ω.φ x z) ∘ (A.chart k).symm =ᶠ[𝓝 y]
      ((fun z => w z + C * Ω.φ x z) ∘ (A.chart jj).symm) ∘ (A.chart jj ∘ (A.chart k).symm) := by
    refine Filter.eventuallyEq_of_mem
      (((A.chart k).isOpen_inter_preimage_symm (A.chart jj).open_source).mem_nhds ⟨hyk, hzj⟩) ?_
    intro y' hy'
    simp only [Function.comp_apply]
    rw [(A.chart jj).left_inv hy'.2]
  have hpt : (A.chart jj ∘ (A.chart k).symm) y = A.chart jj ((A.chart k).symm y) := rfl
  set v := fderiv ℂ (A.chart jj ∘ (A.chart k).symm) y u with hvdef
  have hL : levi ((fun z => w z + C * Ω.φ x z) ∘ (A.chart k).symm) y u =
      levi (w ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v +
        C * levi (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    rw [levi_congr hev1, levi_comp u hτa hf2, hpt]
    exact levi_add_smul C hψ2 hΦx2 v
  obtain ⟨W, hWo, hzW, G, hG, hGeq⟩ := hΩ.2 x q ((A.chart k).symm y) ⟨hzx, hzq'⟩
  have hτW : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' (W ∩ Ω.U x ∩ Ω.U q) := by
    refine ⟨(A.chart jj).map_source hzj, ?_⟩
    rw [Set.mem_preimage, (A.chart jj).left_inv hzj]
    exact ⟨⟨hzW, hzx⟩, hzq'⟩
  have hN2 := ((A.chart jj).isOpen_inter_preimage_symm
    ((hWo.inter (Ω.isOpen_U x)).inter (Ω.isOpen_U q))).mem_nhds hτW
  have hGa : AnalyticAt ℂ (G ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    hG jj _ ⟨hτW.1, hτW.2.1.1⟩
  have hev2 : Ω.φ x ∘ (A.chart jj).symm =ᶠ[𝓝 (A.chart jj ((A.chart k).symm y))]
      fun y' => (Ω.φ q ∘ (A.chart jj).symm) y' + 1 * ((G ∘ (A.chart jj).symm) y').re := by
    refine Filter.eventuallyEq_of_mem hN2 ?_
    intro y' hy'
    have := hGeq _ hy'.2
    simp only [Function.comp_apply]
    linarith
  have hev3 : (fun y' => ((G ∘ (A.chart jj).symm) y').re)
      =ᶠ[𝓝 (A.chart jj ((A.chart k).symm y))]
      fun y' => (Ω.φ x ∘ (A.chart jj).symm) y' - (Ω.φ q ∘ (A.chart jj).symm) y' := by
    refine Filter.eventuallyEq_of_mem hN2 ?_
    intro y' hy'
    have := hGeq _ hy'.2
    simp only [Function.comp_apply]
    linarith
  have hRe2 : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart jj).symm) y').re)
      (A.chart jj ((A.chart k).symm y)) :=
    (hΦx2.sub hΦq2).congr_of_eventuallyEq hev3
  have hLx : levi (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v =
      levi (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    rw [levi_congr hev2, levi_add_smul 1 hΦq2 hRe2 v, levi_re_analytic hGa v]
    ring
  have hloc2 := hloc1 (A.chart jj ((A.chart k).symm y)) (Metric.ball_subset_closedBall hzb) v
  have hnn : 0 ≤ levi (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    by_cases hv0 : v = 0
    · rw [hv0, levi_zero]
    · exact (hpos q jj _ hτS v hv0).le
  rw [hL, hLx]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m q + C) hnn]

end

end ReciprocityTheory.AnForm.M
