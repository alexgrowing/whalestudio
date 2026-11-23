import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftB

namespace ReciprocityTheory.AnForm.P

open Filter Topology MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff

noncomputable section

namespace TailChernBound

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_smul' {f : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : Fin e → ℂ) : levi (fun y => c * f y) z w = c * levi f z w := by
  have hd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
    (hf.eventually (by decide)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h2 : fderiv ℝ (fun y => c * f y) =ᶠ[𝓝 z] fun y => c • fderiv ℝ f y :=
    hd.mono fun y hy => (hy.hasFDerivAt.const_mul c).fderiv
  have h3 : fderiv ℝ (fderiv ℝ (fun y => c * f y)) z = c • fderiv ℝ (fderiv ℝ f) z := by
    rw [h2.fderiv_eq]
    exact (hdd.hasFDerivAt.const_smul c).fderiv
  unfold levi
  rw [h3]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem levi_rsmul_lemma (φ : (Fin e → ℂ) → ℝ) (z w : Fin e → ℂ) (t : ℝ) :
    levi φ z (t • w) = t ^ 2 * levi φ z w := by
  unfold levi
  rw [smul_comm Complex.I t w]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem chern_local (A : FinHolAtlas e X) (Θ L : LocPot X) (hΘ : IsPotential A Θ)
    (hpos : IsPosPot A Θ) (hL : IsPotential A L) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        |levi (L.φ p ∘ (A.chart j).symm) y u| ≤ m * levi (Θ.φ p ∘ (A.chart j).symm) y u := by
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p)) :=
    (A.chart j).isOpen_inter_preimage_symm ((Θ.isOpen_U p).inter (L.isOpen_U p))
  have haS : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p) :=
    ⟨(A.chart j).map_source hp, by
      rw [Set.mem_preimage, (A.chart j).left_inv hp]; exact ⟨Θ.mem_U p, L.mem_U p⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo _ haS
  have hcb : Metric.closedBall (A.chart j p) (ε / 2) ⊆
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hΘs : ContDiffOn ℝ 2 (Θ.φ p ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p)) := by
    have h : ContDiffOn ℝ ∞ (Θ.φ p ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p)) := (hΘ.1 p j).mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
    exact_mod_cast contDiffOn_infty.1 h 2
  have hLs : ContDiffOn ℝ 2 (L.φ p ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p)) := by
    have h : ContDiffOn ℝ ∞ (L.φ p ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p)) := (hL.1 p j).mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_right))
    exact_mod_cast contDiffOn_infty.1 h 2
  have hcF := continuousOn_levi hSo hΘs
  have hcH := continuousOn_levi hSo hLs
  have hK : IsCompact (Metric.closedBall (A.chart j p) (ε / 2) ×ˢ
      Metric.sphere (0 : Fin e → ℂ) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKS : Metric.closedBall (A.chart j p) (ε / 2) ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 ⊆
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U p ∩ L.U p)) ×ˢ Set.univ :=
    Set.prod_mono hcb (Set.subset_univ _)
  obtain ⟨c, hc, hcmin⟩ : ∃ c > 0, ∀ q ∈ Metric.closedBall (A.chart j p) (ε / 2) ×ˢ
      Metric.sphere (0 : Fin e → ℂ) 1, c ≤ levi (Θ.φ p ∘ (A.chart j).symm) q.1 q.2 := by
    by_cases hK0 : (Metric.closedBall (A.chart j p) (ε / 2) ×ˢ
        Metric.sphere (0 : Fin e → ℂ) 1).Nonempty
    · obtain ⟨q0, hq0K, hmin⟩ := hK.exists_isMinOn hK0 (hcF.mono hKS)
      have hq0 : q0.2 ≠ 0 := fun h0 => by
        have h1 := hq0K.2
        rw [mem_sphere_zero_iff_norm, h0, norm_zero] at h1
        exact zero_ne_one h1
      exact ⟨_, hpos p j q0.1 ⟨(hcb hq0K.1).1, (hcb hq0K.1).2.1⟩ q0.2 hq0,
        fun q hq => isMinOn_iff.1 hmin q hq⟩
    · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hK0⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcH.mono hKS)
  refine ⟨ε / 2, by positivity, M / c, hcb, fun y hy u => ?_⟩
  by_cases hu : u = 0
  · subst hu
    simp [levi_zero]
  have ht : 0 < ‖u‖ := norm_pos_iff.2 hu
  obtain ⟨u0, hu0def⟩ : ∃ u0 : Fin e → ℂ, u0 = (‖u‖⁻¹ : ℝ) • u := ⟨_, rfl⟩
  have hu_eq : u = ‖u‖ • u0 := by
    rw [hu0def, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hu0 : u0 ∈ Metric.sphere (0 : Fin e → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hu0def]
    exact norm_smul_inv_norm hu
  have hH0 : |levi (L.φ p ∘ (A.chart j).symm) y u0| ≤ M := by
    have h1 := hM (y, u0) ⟨hy, hu0⟩
    simpa [Real.norm_eq_abs] using h1
  have hF0 : c ≤ levi (Θ.φ p ∘ (A.chart j).symm) y u0 := hcmin (y, u0) ⟨hy, hu0⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hH0
  have e1 : levi (L.φ p ∘ (A.chart j).symm) y u =
      ‖u‖ ^ 2 * levi (L.φ p ∘ (A.chart j).symm) y u0 := by
    rw [← levi_rsmul_lemma]
    congr 1
  have e2 : levi (Θ.φ p ∘ (A.chart j).symm) y u =
      ‖u‖ ^ 2 * levi (Θ.φ p ∘ (A.chart j).symm) y u0 := by
    rw [← levi_rsmul_lemma]
    congr 1
  rw [e1, e2, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hMc : M ≤ M / c * levi (Θ.φ p ∘ (A.chart j).symm) y u0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    exact mul_le_mul_of_nonneg_left hF0 hM0
  calc ‖u‖ ^ 2 * |levi (L.φ p ∘ (A.chart j).symm) y u0|
      ≤ ‖u‖ ^ 2 * M := mul_le_mul_of_nonneg_left hH0 (sq_nonneg _)
    _ ≤ ‖u‖ ^ 2 * (M / c * levi (Θ.φ p ∘ (A.chart j).symm) y u0) :=
        mul_le_mul_of_nonneg_left hMc (sq_nonneg _)
    _ = M / c * (‖u‖ ^ 2 * levi (Θ.φ p ∘ (A.chart j).symm) y u0) := by ring

theorem levi_lin {f g : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (a b : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (w : Fin e → ℂ) :
    levi (fun y => a * f y + b * g y) z w = a * levi f z w + b * levi g z w := by
  have hdf : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
    (hf.eventually (by decide)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hdg : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ g y :=
    (hg.eventually (by decide)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hddf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hddg : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h2 : fderiv ℝ (fun y => a * f y + b * g y) =ᶠ[𝓝 z]
      fun y => a • fderiv ℝ f y + b • fderiv ℝ g y :=
    (hdf.and hdg).mono fun y hy =>
      ((hy.1.hasFDerivAt.const_mul a).add (hy.2.hasFDerivAt.const_mul b)).fderiv
  have h3 : fderiv ℝ (fderiv ℝ (fun y => a * f y + b * g y)) z =
      a • fderiv ℝ (fderiv ℝ f) z + b • fderiv ℝ (fderiv ℝ g) z := by
    rw [h2.fderiv_eq]
    exact ((hddf.hasFDerivAt.const_smul a).add (hddg.hasFDerivAt.const_smul b)).fderiv
  unfold levi
  rw [h3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem base_change (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x p q : X)
    (j : Fin A.n) (hqs : q ∈ (A.chart j).source) (hqx : q ∈ P.U x) (hqp : q ∈ P.U p)
    (u : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) (A.chart j q) u =
      levi (P.φ p ∘ (A.chart j).symm) (A.chart j q) u := by
  obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hP.2 x p q ⟨hqx, hqp⟩
  have ha_t : A.chart j q ∈ (A.chart j).target := (A.chart j).map_source hqs
  have hsa : (A.chart j).symm (A.chart j q) = q := (A.chart j).left_inv hqs
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U x ∩ P.U p)) :=
    (A.chart j).isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U x)).inter (P.isOpen_U p))
  have haS : A.chart j q ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U x ∩ P.U p) :=
    ⟨ha_t, by rw [Set.mem_preimage, hsa]; exact ⟨⟨hqW, hqx⟩, hqp⟩⟩
  have hev : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j q)]
      fun y => 1 * (P.φ p ∘ (A.chart j).symm) y + 1 * ((G ∘ (A.chart j).symm) y).re := by
    filter_upwards [hSo.mem_nhds haS] with y hy
    have h1 := hGeq ((A.chart j).symm y) hy.2
    simp only [Function.comp_apply]
    linarith
  have hpo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U p) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U p)
  have hpa : A.chart j q ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U p :=
    ⟨ha_t, by rw [Set.mem_preimage, hsa]; exact hqp⟩
  have hsx : ContDiffAt ℝ 2 (P.φ p ∘ (A.chart j).symm) (A.chart j q) := by
    have h := (hP.1 p j).contDiffAt (hpo.mem_nhds hpa)
    exact_mod_cast contDiffAt_infty.1 h 2
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) (A.chart j q) :=
    hG j (A.chart j q) ⟨ha_t, by rw [Set.mem_preimage, hsa]; exact hqW⟩
  have hre : ContDiffAt ℝ 2 (fun y => ((G ∘ (A.chart j).symm) y).re) (A.chart j q) :=
    Complex.reCLM.contDiff.contDiffAt.comp (A.chart j q)
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
  have h2 := levi_lin (z := A.chart j q) (1 : ℝ) 1 hsx hre u
  rw [levi_congr hev u, h2, levi_re_analytic hGa u]
  ring

theorem exists_levi_nonneg_chern_bound [CompactSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) (hL : IsPotential A L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (∀ a : ℝ, -|a| ≤ ε * a) → ∀ x k,
      ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (Θ.U x ∩ L.U x), ∀ v : Fin e → ℂ,
        0 ≤ levi ((fun z => C * Θ.φ x z + ε * L.φ x z) ∘ (A.chart k).symm) y v := by
  choose j hj using A.cover
  choose r hr m hsub hbd using fun p => chern_local A Θ L hΘ hpos hL p (j p) (hj p)
  have hVo : ∀ p, IsOpen ((A.chart (j p)).source ∩
      A.chart (j p) ⁻¹' Metric.ball (A.chart (j p) p) (r p)) := fun p =>
    (A.chart (j p)).continuousOn.isOpen_inter_preimage (A.chart (j p)).open_source
      Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (A.chart (j p)).source ∩ A.chart (j p) ⁻¹' Metric.ball (A.chart (j p) p) (r p))
    hVo (fun x _ => Set.mem_iUnion.2 ⟨x, hj x, Metric.mem_ball_self (hr x)⟩)
  obtain ⟨C, hC0, hCm⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ t, m i ≤ C :=
    ⟨∑ i ∈ t, |m i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i hi =>
      (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |m i|)
        (fun i _ => abs_nonneg _) hi)⟩
  refine ⟨C, hC0, ?_⟩
  intro ε hε x k y hy v
  have hU := ht (Set.mem_univ ((A.chart k).symm y))
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, exists_prop] at hU
  obtain ⟨i, hit, hqi⟩ := hU
  have hq_src : (A.chart k).symm y ∈ (A.chart (j i)).source := hqi.1
  have hb_ball : A.chart (j i) ((A.chart k).symm y) ∈
      Metric.closedBall (A.chart (j i) i) (r i) := Metric.ball_subset_closedBall hqi.2
  have hb := hsub i hb_ball
  have hsb : (A.chart (j i)).symm (A.chart (j i) ((A.chart k).symm y)) = (A.chart k).symm y :=
    (A.chart (j i)).left_inv hq_src
  have hqΘi : (A.chart k).symm y ∈ Θ.U i := by
    have h : (A.chart (j i)).symm (A.chart (j i) ((A.chart k).symm y)) ∈ Θ.U i := hb.2.1
    rwa [hsb] at h
  have hqLi : (A.chart k).symm y ∈ L.U i := by
    have h : (A.chart (j i)).symm (A.chart (j i) ((A.chart k).symm y)) ∈ L.U i := hb.2.2
    rwa [hsb] at h
  have hqΘx : (A.chart k).symm y ∈ Θ.U x := hy.2.1
  have hqLx : (A.chart k).symm y ∈ L.U x := hy.2.2
  have hyT : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart (j i)).source :=
    ⟨hy.1, hq_src⟩
  have hτ : AnalyticAt ℂ (A.chart (j i) ∘ (A.chart k).symm) y := A.holo k (j i) y hyT
  have hOT : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart (j i)).source) :=
    (A.chart k).isOpen_inter_preimage_symm (A.chart (j i)).open_source
  have hchg : ∀ P : LocPot X, IsPotential A P → (A.chart k).symm y ∈ P.U x →
      levi (P.φ x ∘ (A.chart k).symm) y v =
        levi (P.φ x ∘ (A.chart (j i)).symm) (A.chart (j i) ((A.chart k).symm y))
          (fderiv ℂ (A.chart (j i) ∘ (A.chart k).symm) y v) := by
    intro P hP hqx
    have hev : (P.φ x ∘ (A.chart k).symm) =ᶠ[𝓝 y]
        (P.φ x ∘ (A.chart (j i)).symm) ∘ (A.chart (j i) ∘ (A.chart k).symm) := by
      filter_upwards [hOT.mem_nhds hyT] with z hz
      simp only [Function.comp_apply, (A.chart (j i)).left_inv hz.2]
    have hO : IsOpen ((A.chart (j i)).target ∩ (A.chart (j i)).symm ⁻¹' P.U x) :=
      (A.chart (j i)).isOpen_inter_preimage_symm (P.isOpen_U x)
    have hm : (A.chart (j i) ∘ (A.chart k).symm) y ∈
        (A.chart (j i)).target ∩ (A.chart (j i)).symm ⁻¹' P.U x :=
      ⟨(A.chart (j i)).map_source hq_src, by
        simp only [Set.mem_preimage, Function.comp_apply, hsb]; exact hqx⟩
    have hsm : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart (j i)).symm)
        ((A.chart (j i) ∘ (A.chart k).symm) y) := by
      have h := (hP.1 x (j i)).contDiffAt (hO.mem_nhds hm)
      exact_mod_cast contDiffAt_infty.1 h 2
    exact (levi_congr hev v).trans (levi_comp v hτ hsm)
  have eΘ := (hchg Θ hΘ hqΘx).trans
    (base_change A Θ hΘ x i ((A.chart k).symm y) (j i) hq_src hqΘx hqΘi _)
  have eL := (hchg L hL hqLx).trans
    (base_change A L hL x i ((A.chart k).symm y) (j i) hq_src hqLx hqLi _)
  have hbd' := hbd i _ hb_ball (fderiv ℂ (A.chart (j i) ∘ (A.chart k).symm) y v)
  have hF0 : 0 ≤ levi (Θ.φ i ∘ (A.chart (j i)).symm) (A.chart (j i) ((A.chart k).symm y))
      (fderiv ℂ (A.chart (j i) ∘ (A.chart k).symm) y v) := by
    by_cases hw0 : fderiv ℂ (A.chart (j i) ∘ (A.chart k).symm) y v = 0
    · rw [hw0, levi_zero]
    · exact (hpos i (j i) _ ⟨hb.1, hb.2.1⟩ _ hw0).le
  have hFk : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart k).symm) y := by
    have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' Θ.U x) :=
      (A.chart k).isOpen_inter_preimage_symm (Θ.isOpen_U x)
    have h := (hΘ.1 x k).contDiffAt (hO.mem_nhds ⟨hy.1, hqΘx⟩)
    exact_mod_cast contDiffAt_infty.1 h 2
  have hLk : ContDiffAt ℝ 2 (L.φ x ∘ (A.chart k).symm) y := by
    have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' L.U x) :=
      (A.chart k).isOpen_inter_preimage_symm (L.isOpen_U x)
    have h := (hL.1 x k).contDiffAt (hO.mem_nhds ⟨hy.1, hqLx⟩)
    exact_mod_cast contDiffAt_infty.1 h 2
  have hlin := levi_lin (z := y) C ε hFk hLk v
  refine le_of_le_of_eq ?_ hlin.symm
  rw [eΘ, eL]
  have h1 := hε (levi (L.φ i ∘ (A.chart (j i)).symm) (A.chart (j i) ((A.chart k).symm y))
      (fderiv ℂ (A.chart (j i) ∘ (A.chart k).symm) y v))
  have h2 := mul_le_mul_of_nonneg_right (hCm i hit) hF0
  linarith

end TailChernBound

namespace TailBoundAlt

theorem add_φ {X : Type} [TopologicalSpace X] (P Q : LocPot X) :
    (P + Q).φ = fun x y => P.φ x y + Q.φ x y := rfl

theorem mInt_congr_phi {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Ψ : Fin e → LocPot X) (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  simp only [mInt, integralWith, locDens, h]

theorem mInt_zero {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) : mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt
  split_ifs with hne
  · simp [integralWith]
  · rfl

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (h : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem isPsh_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P Q : LocPot X)
    (hP : IsPsh A P) (hU : ∀ x, Q.U x ⊆ P.U x) (hφ : Q.φ = P.φ) : IsPsh A Q := by
  intro x j y hy w
  rw [hφ]
  exact hP x j y ⟨hy.1, hU x hy.2⟩ w

theorem mInt_lower {d : ℕ} {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (B : FinHolAtlas d Y) (Ψ : Fin d → LocPot Y) (hΨ : ∀ i, IsPotential B (Ψ i))
    (hΨp : ∀ i, IsPsh B (Ψ i)) (g : Y → ℝ) (hg : Continuous g) (a : ℝ) (hga : ∀ y, -a ≤ g y) :
    -a * mInt B Ψ (fun _ => 1) ≤ mInt B Ψ g := by
  have h0 := mIntNonneg B Ψ hΨ hΨp (fun y => 1 * g y + (fun _ => a) y) (fun y => by
    simp only [one_mul]; linarith [hga y])
  have hl := mIntLinear B Ψ hΨ 1 g (fun _ => a) (mIntegrableCont B Ψ hΨ g hg)
    (mIntegrableCont B Ψ hΨ _ continuous_const)
  have hl2 := mIntLinear B Ψ hΨ a (fun _ => 1) (fun _ => 0)
    (mIntegrableCont B Ψ hΨ _ continuous_const) (mIntegrableCont B Ψ hΨ _ continuous_const)
  have hz := mInt_zero B Ψ
  have ha : mInt B Ψ (fun _ => a) = a * mInt B Ψ (fun _ => 1) := by
    have e1 : (fun _ : Y => a) = fun x => a * (fun _ : Y => (1 : ℝ)) x + (fun _ : Y => (0 : ℝ)) x := by
      funext x; ring
    rw [e1, hl2, hz, add_zero]
  rw [hl, ha] at h0
  linarith

theorem mInt_nonpos {d : ℕ} {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (B : FinHolAtlas d Y) (Ψ : Fin d → LocPot Y) (hΨ : ∀ i, IsPotential B (Ψ i))
    (hΨp : ∀ i, IsPsh B (Ψ i)) (g : Y → ℝ) (hg : Continuous g) (hg0 : ∀ y, g y ≤ 0) :
    mInt B Ψ g ≤ 0 := by
  unfold mInt
  split_ifs with hne
  · unfold integralWith
    refine Finset.sum_nonpos fun j _ => ?_
    refine MeasureTheory.integral_nonpos_of_ae
      (Filter.Eventually.mono
        (MeasureTheory.ae_restrict_mem (B.chart j).open_target.measurableSet) fun y hy => ?_)
    have h1 := hne.some.nonneg j ((B.chart j).symm y)
    have h2 := locDens_nonneg B Ψ hΨ hΨp j hy
    have h3 := hg0 ((B.chart j).symm y)
    show _ * _ * _ ≤ (0 : ℝ)
    nlinarith [mul_nonneg h1 h2]
  · exact le_rfl

theorem exists_psh_chern_bound {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Θ L : LocPot X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hL : IsPotential A L) :
    ∃ C : ℝ, 0 ≤ C ∧ IsPsh A (Θ.rsmul C + L) ∧ IsPsh A (Θ.rsmul C + L.rsmul (-1)) := by
  obtain ⟨C, hC0, hC⟩ := TailChernBound.exists_levi_nonneg_chern_bound A Θ L hΘ hΘp hL
  refine ⟨C, hC0, ?_, ?_⟩
  · intro x j y hy w
    have key : (Θ.rsmul C + L).φ x = fun z => C * Θ.φ x z + 1 * L.φ x z := by
      rw [add_φ]
      funext z
      simp [LocPot.rsmul]
    rw [key]
    exact hC 1 (fun a => by rw [one_mul]; exact neg_abs_le a) x j y hy w
  · intro x j y hy w
    have key : (Θ.rsmul C + L.rsmul (-1)).φ x = fun z => C * Θ.φ x z + (-1) * L.φ x z := by
      rw [add_φ]
      funext z
      simp [LocPot.rsmul]
    rw [key]
    exact hC (-1) (fun a => by rw [neg_one_mul, neg_le_neg_iff]; exact le_abs_self a) x j y hy w

end TailBoundAlt

end

end ReciprocityTheory.AnForm.P
