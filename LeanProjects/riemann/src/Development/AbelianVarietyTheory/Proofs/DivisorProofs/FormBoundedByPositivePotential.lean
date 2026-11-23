import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffMulOfTsupport

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.ChernCompare

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem compat_self (A : FinHolAtlas e X) (j : Fin A.n) : IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem pot_contDiffAt {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (x : X) {z : Fin e → ℂ}
    (hz : z ∈ ψ.target) (hx : ψ.symm z ∈ P.U x) : ContDiffAt ℝ 2 (P.φ x ∘ ψ.symm) z :=
  ((ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ (P.isOpen_U x) (hP.1 x)).contDiffAt
    ((ψ.isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hz, hx⟩)).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem levi_base_compat {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (x : X) {z : Fin e → ℂ}
    (hz : z ∈ ψ.target) (hx : ψ.symm z ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ (ψ.symm z) ∘ ψ.symm) z w = levi (P.φ x ∘ ψ.symm) z w := by
  obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ := hP.2 (ψ.symm z) x (ψ.symm z) ⟨P.mem_U _, hx⟩
  have hVo : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (W ∩ P.U (ψ.symm z) ∩ P.U x)) :=
    ψ.isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U _)).inter (P.isOpen_U x))
  have hyV : z ∈ ψ.target ∩ ψ.symm ⁻¹' (W ∩ P.U (ψ.symm z) ∩ P.U x) :=
    ⟨hz, ⟨⟨hyW, P.mem_U _⟩, hx⟩⟩
  have hGa : AnalyticAt ℂ (G ∘ ψ.symm) z :=
    ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun hψ hG hz hyW
  have hRe : ContDiffAt ℝ 2 (fun u => ((G ∘ ψ.symm) u).re) z := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have h1 : (P.φ (ψ.symm z) ∘ ψ.symm) =ᶠ[𝓝 z]
      (fun u => (P.φ x ∘ ψ.symm) u + 1 * ((G ∘ ψ.symm) u).re) := by
    filter_upwards [hVo.mem_nhds hyV] with u hu
    have := hGeq (ψ.symm u) hu.2
    simp only [Function.comp_apply]
    linarith
  rw [levi_congr h1, levi_add_smul 1 (pot_contDiffAt hP hψ x hz hx) hRe, levi_re_analytic hGa]
  ring

theorem formAt_chart {A : FinHolAtlas e X} (P : LocPot X) (hP : IsPotential A P)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (j : Fin A.n)
    {z : Fin e → ℂ} (hz : z ∈ ψ.target) (hj : ψ.symm z ∈ (A.chart j).source) (w : Fin e → ℂ) :
    formAt ψ P z w = formAt (A.chart j) P (A.chart j (ψ.symm z))
      (fderiv ℂ (A.chart j ∘ ψ.symm) z w) := by
  have hT : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
  have hl : (A.chart j).symm (A.chart j (ψ.symm z)) = ψ.symm z := (A.chart j).left_inv hj
  have hφ : ContDiffAt ℝ 2 (P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) := by
    refine pot_contDiffAt hP (compat_self A j) _ ((A.chart j).map_source hj) ?_
    simp only [Function.comp_apply]
    rw [hl]
    exact P.mem_U _
  have hev : (P.φ (ψ.symm z) ∘ ψ.symm) =ᶠ[𝓝 z]
      ((P.φ (ψ.symm z) ∘ (A.chart j).symm) ∘ (A.chart j ∘ ψ.symm)) := by
    filter_upwards [(ψ.isOpen_inter_preimage_symm (A.chart j).open_source).mem_nhds ⟨hz, hj⟩]
      with u hu
    simp [(A.chart j).left_inv hu.2]
  unfold formAt
  rw [hl, levi_congr hev, levi_comp w hT hφ]
  rfl

theorem local_bound {A : FinHolAtlas e X} {P Q : LocPot X} (hP : IsPotential A P)
    (hQ : IsPotential A Q) (hQp : IsPosPot A Q) (y0 : X) :
    ∃ j : Fin A.n, ∃ N : Set X, IsOpen N ∧ y0 ∈ N ∧ N ⊆ (A.chart j).source ∧ ∃ C : ℝ, 0 < C ∧
      ∀ y ∈ N, ∀ v, |formAt (A.chart j) P (A.chart j y) v| ≤
        C * formAt (A.chart j) Q (A.chart j y) v := by
  obtain ⟨j, hj⟩ := A.cover y0
  set c := A.chart j with hc
  set V := c.target ∩ c.symm ⁻¹' (P.U y0 ∩ Q.U y0) with hV
  have hVo : IsOpen V := c.isOpen_inter_preimage_symm ((P.isOpen_U y0).inter (Q.isOpen_U y0))
  have hu0 : c y0 ∈ V := ⟨c.map_source hj, by
    simp only [Set.mem_preimage, c.left_inv hj]; exact ⟨P.mem_U _, Q.mem_U _⟩⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo (c y0) hu0
  set B := Metric.closedBall (c y0) (r / 2) with hB
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hrV
  set S := Metric.sphere (0 : Fin e → ℂ) 1 with hS
  have hK : IsCompact (B ×ˢ S) := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hsub : B ×ˢ S ⊆ V ×ˢ Set.univ := Set.prod_mono hBV (Set.subset_univ _)
  have hsP : ContDiffOn ℝ 2 (P.φ y0 ∘ c.symm) V :=
    (potSmoothOn A P hP y0 j).mono fun u hu => ⟨hu.1, hu.2.1⟩
  have hsQ : ContDiffOn ℝ 2 (Q.φ y0 ∘ c.symm) V :=
    (potSmoothOn A Q hQ y0 j).mono fun u hu => ⟨hu.1, hu.2.2⟩
  have hcP := (continuousOn_levi hVo hsP).mono hsub
  have hcQ := (continuousOn_levi hVo hsQ).mono hsub
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcP
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ p ∈ B ×ˢ S, m ≤ levi (Q.φ y0 ∘ c.symm) p.1 p.2 := by
    rcases (B ×ˢ S).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by rw [he] at hp; exact hp.elim⟩
    · obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hne hcQ
      refine ⟨_, ?_, fun p hp => hmin hp⟩
      have h1 : p0.2 ≠ 0 := fun h => by
        have := hp0.2
        rw [h, hS, Metric.mem_sphere, dist_self] at this
        exact zero_ne_one this
      exact hQp y0 j p0.1 ⟨(hBV hp0.1).1, (hBV hp0.1).2.2⟩ p0.2 h1
  obtain ⟨m, hm0, hmQ⟩ := hm
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  refine ⟨j, c.source ∩ c ⁻¹' Metric.ball (c y0) (r / 2),
    c.isOpen_inter_preimage Metric.isOpen_ball, ⟨hj, Metric.mem_ball_self (by linarith)⟩,
    Set.inter_subset_left, M' / m + 1, by positivity, fun y hy v => ?_⟩
  have huB : c y ∈ B := Metric.ball_subset_closedBall hy.2
  have hyc : c.symm (c y) = y := c.left_inv hy.1
  have key : |levi (P.φ y0 ∘ c.symm) (c y) v| ≤
      (M' / m + 1) * levi (Q.φ y0 ∘ c.symm) (c y) v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp [levi_zero]
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖v‖ := ⟨_, rfl⟩
      have ht0 : 0 < t := ht ▸ norm_pos_iff.2 hv
      obtain ⟨v1, hv1⟩ : ∃ v1 : Fin e → ℂ, v1 = t⁻¹ • v := ⟨_, rfl⟩
      have hvv : v = t • v1 := by rw [hv1, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
      have hv1S : v1 ∈ S := by
        rw [hS, mem_sphere_zero_iff_norm, hv1, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos ht0, ← ht, inv_mul_cancel₀ ht0.ne']
      have hp : (c y, v1) ∈ B ×ˢ S := ⟨huB, hv1S⟩
      have a1 : |levi (P.φ y0 ∘ c.symm) (c y) v1| ≤ M' := by
        have := hM _ hp
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      have a2 : m ≤ levi (Q.φ y0 ∘ c.symm) (c y) v1 := hmQ _ hp
      have a3 : |levi (P.φ y0 ∘ c.symm) (c y) v1| ≤
          (M' / m + 1) * levi (Q.φ y0 ∘ c.symm) (c y) v1 := by
        have e1 : M' = M' / m * m := by field_simp
        have b1 : M' / m * m ≤ M' / m * levi (Q.φ y0 ∘ c.symm) (c y) v1 :=
          mul_le_mul_of_nonneg_left a2 (by positivity)
        have b2 : 0 ≤ levi (Q.φ y0 ∘ c.symm) (c y) v1 := hm0.le.trans a2
        rw [add_mul, one_mul]
        linarith
      have eP : levi (P.φ y0 ∘ c.symm) (c y) v = t ^ 2 * levi (P.φ y0 ∘ c.symm) (c y) v1 := by
        rw [← levi_smul_dir, ← hvv]
      have eQ : levi (Q.φ y0 ∘ c.symm) (c y) v = t ^ 2 * levi (Q.φ y0 ∘ c.symm) (c y) v1 := by
        rw [← levi_smul_dir, ← hvv]
      rw [eP, eQ, abs_mul, abs_of_nonneg (sq_nonneg t)]
      calc t ^ 2 * |levi (P.φ y0 ∘ c.symm) (c y) v1|
          ≤ t ^ 2 * ((M' / m + 1) * levi (Q.φ y0 ∘ c.symm) (c y) v1) :=
            mul_le_mul_of_nonneg_left a3 (sq_nonneg t)
        _ = (M' / m + 1) * (t ^ 2 * levi (Q.φ y0 ∘ c.symm) (c y) v1) := by ring
  have hbP : formAt c P (c y) v = 2 / Real.pi * levi (P.φ y0 ∘ c.symm) (c y) v := by
    unfold formAt
    rw [levi_base_compat hP (compat_self A j) y0 (c.map_source hy.1)
      (by rw [hyc]; exact (hyc ▸ (hBV huB).2.1 : y ∈ P.U y0))]
  have hbQ : formAt c Q (c y) v = 2 / Real.pi * levi (Q.φ y0 ∘ c.symm) (c y) v := by
    unfold formAt
    rw [levi_base_compat hQ (compat_self A j) y0 (c.map_source hy.1)
      (by rw [hyc]; exact (hyc ▸ (hBV huB).2.2 : y ∈ Q.U y0))]
  rw [hbP, hbQ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
  linarith

theorem chern_le_kahler : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (P Q : LocPot X), IsPotential A P → IsPotential A Q → IsPosPot A Q →
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ →
      ∀ z ∈ ψ.target, ∀ w, |formAt ψ P z w| ≤ C * formAt ψ Q z w := by
  intro e X _ _ _ A P Q hP hQ hQp
  choose j N hNo hyN hNs C hC hb using fun y => local_bound hP hQ hQp y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hyN y⟩)
  refine ⟨∑ y ∈ t, C y + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun y _ => (hC y).le) one_pos, ?_⟩
  intro ψ hψ z hz w
  obtain ⟨y0, hy0t, hy0⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (ψ.symm z)))
  have hs := hNs y0 hy0
  rw [formAt_chart P hP hψ (j y0) hz hs, formAt_chart Q hQ hψ (j y0) hz hs]
  have h1 := hb y0 (ψ.symm z) hy0 (fderiv ℂ (A.chart (j y0) ∘ ψ.symm) z w)
  have hQ0 : 0 ≤ formAt (A.chart (j y0)) Q (A.chart (j y0) (ψ.symm z))
      (fderiv ℂ (A.chart (j y0) ∘ ψ.symm) z w) := by
    have := (abs_nonneg _).trans h1
    exact (mul_nonneg_iff_of_pos_left (hC y0)).1 this
  have hle : C y0 ≤ ∑ y ∈ t, C y + 1 :=
    (Finset.single_le_sum (fun y _ => (hC y).le) hy0t).trans (le_add_of_nonneg_right zero_le_one)
  exact h1.trans (mul_le_mul_of_nonneg_right hle hQ0)

end

end GlobalTheory.ChernCompare
