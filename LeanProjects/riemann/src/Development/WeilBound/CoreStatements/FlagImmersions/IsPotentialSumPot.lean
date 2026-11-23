import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftB

noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology GlobalTheory.CompanionTheory.Ar.PB
open scoped ContDiff

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def dl (A : FinHolAtlas e X) (P : LocPot X) (j : Fin A.n) (y w : Fin e → ℂ) : ℝ :=
  levi (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w

theorem c2 {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  (contDiffAt_of_isPotential A P hP x j ⟨hy, hx⟩).of_le two_le_infty

theorem levi_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) y w = dl A P j y w := by
  set c := A.chart j with hc
  set p := c.symm y with hp
  obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hP.2 x p p ⟨hx, P.mem_U p⟩
  have hGa : AnalyticAt ℂ (G ∘ c.symm) y := hG j y ⟨hy, hqW⟩
  have hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ c.symm) z).re) y := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have hbase : P.φ x ∘ c.symm =ᶠ[𝓝 y]
      fun z => (P.φ p ∘ c.symm) z + 1 * ((G ∘ c.symm) z).re := by
    have hopen : IsOpen (W ∩ P.U x ∩ P.U p) := (hWo.inter (P.isOpen_U x)).inter (P.isOpen_U p)
    have : ∀ᶠ z in 𝓝 y, c.symm z ∈ W ∩ P.U x ∩ P.U p :=
      (c.continuousAt_symm hy).preimage_mem_nhds (hopen.mem_nhds ⟨⟨hqW, hx⟩, P.mem_U p⟩)
    filter_upwards [this] with z hz
    have := hGeq (c.symm z) hz
    simp only [Function.comp_apply, one_mul]
    linarith
  rw [levi_congr hbase, levi_add_smul 1 (c2 hP p j hy (P.mem_U p)) hRe, levi_re_analytic hGa]
  simp only [dl, mul_zero, add_zero]
  rfl

theorem isPsh_iff {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) :
    IsPsh A P ↔ ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, 0 ≤ dl A P j y w := by
  refine ⟨fun h j y hy w => h _ j y ⟨hy, P.mem_U _⟩ w, fun h x j y hy w => ?_⟩
  rw [levi_base hP x j hy.1 hy.2]
  exact h j y hy.1 w

theorem dl_nonneg {A : FinHolAtlas e X} {P : LocPot X} (h : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : 0 ≤ dl A P j y w :=
  h _ j y ⟨hy, P.mem_U _⟩ w

theorem dl_nonneg_of_pos {A : FinHolAtlas e X} {P : LocPot X} (h : IsPosPot A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : 0 ≤ dl A P j y w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [dl, levi_zero]
  · exact (h _ j y ⟨hy, P.mem_U _⟩ w hw).le

theorem dl_add_rsmul {A : FinHolAtlas e X} {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q)
    (c : ℝ) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    dl A (P + Q.rsmul c) j y w = dl A P j y w + c * dl A Q j y w :=
  levi_add_smul c (c2 hP _ j hy (P.mem_U _)) (c2 hQ _ j hy (Q.mem_U _)) w

theorem levi_const {ι : Type} [Fintype ι] (a : ℝ) (z w : ι → ℂ) : levi (fun _ => a) z w = 0 := by
  simp [levi]

theorem dl_rsmul {A : FinHolAtlas e X} {Q : LocPot X} (hQ : IsPotential A Q)
    (c : ℝ) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    dl A (Q.rsmul c) j y w = c * dl A Q j y w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const (c2 hQ _ j hy (Q.mem_U _)) w
  rw [levi_const] at h
  simp only [zero_add] at h
  exact h

theorem levi_sum {ι σ : Type} [Fintype ι] (s : Finset σ) (c : σ → ℝ) (f : σ → (ι → ℂ) → ℝ) {z : ι → ℂ}
    (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) (w : ι → ℂ) :
    levi (fun y => ∑ a ∈ s, c a * f a y) z w = ∑ a ∈ s, c a * levi (f a) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi_const]
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => ∑ a ∈ s, c a * f a y) z :=
      ContDiffAt.sum fun a _ => contDiffAt_const.mul (hf a)
    have h := levi_add_smul (c a) h1 (hf a) w
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm (c a * _), ← h]
    simp only [add_comm]

theorem dl_sumPot {A : FinHolAtlas e X} {σ : Type} [Fintype σ] (c : σ → ℝ) {P : σ → LocPot X}
    (hP : ∀ a, IsPotential A (P a)) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (w : Fin e → ℂ) : dl A (sumPot c P) j y w = ∑ a, c a * dl A (P a) j y w :=
  levi_sum Finset.univ c (fun a => (P a).φ ((A.chart j).symm y) ∘ (A.chart j).symm)
    (fun a => c2 (hP a) _ j hy ((P a).mem_U _)) w

theorem isPotential_sumPot {A : FinHolAtlas e X} {σ : Type} [Fintype σ] (c : σ → ℝ) {P : σ → LocPot X}
    (hP : ∀ a, IsPotential A (P a)) : IsPotential A (sumPot c P) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have : ContDiffOn ℝ ∞ (fun z => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) z)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (sumPot c P).U x) :=
      ContDiffOn.sum fun a _ => contDiffOn_const.mul
        (((hP a).1 x j).mono fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2 a⟩)
    exact this
  · have h := fun a => (hP a).2 x x' y ⟨Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a⟩
    choose W hWo hyW G hG hGe using h
    refine ⟨⋂ a, W a, isOpen_iInter_of_finite hWo, Set.mem_iInter.2 hyW, fun z => ∑ a, (c a : ℂ) * G a z,
      fun j z hz => ?_, fun z hz => ?_⟩
    · have : AnalyticAt ℂ (fun z => ∑ a, (c a : ℂ) * (G a ∘ (A.chart j).symm) z) z :=
        Finset.analyticAt_fun_sum _ fun a _ =>
          analyticAt_const.mul (hG a j z ⟨hz.1, Set.mem_iInter.1 hz.2 a⟩)
      exact this
    · simp only [sumPot, Complex.re_sum, Complex.re_ofReal_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hGe a z ⟨⟨Set.mem_iInter.1 hz.1.1 a, Set.mem_iInter.1 hz.1.2 a⟩, Set.mem_iInter.1 hz.2 a⟩]
      ring

theorem dl_chart {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (j k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart k).target) (hq : (A.chart k).symm y ∈ (A.chart j).source) (v : Fin e → ℂ) :
    dl A P k y v = dl A P j (A.chart j ((A.chart k).symm y))
      (fderiv ℂ (A.chart j ∘ (A.chart k).symm) y v) := by
  set q := (A.chart k).symm y with hqd
  set c := A.chart j with hc
  have hcqt : c q ∈ c.target := c.map_source hq
  have hsc : c.symm (c q) = q := c.left_inv hq
  set τ := c ∘ (A.chart k).symm with hτd
  have hτ : AnalyticAt ℂ τ y := A.holo k j y ⟨hy, hq⟩
  have hτy : τ y = c q := rfl
  have hgerm : P.φ q ∘ (A.chart k).symm =ᶠ[𝓝 y] (P.φ q ∘ c.symm) ∘ τ := by
    have : ∀ᶠ y' in 𝓝 y, (A.chart k).symm y' ∈ c.source :=
      ((A.chart k).continuousAt_symm hy).preimage_mem_nhds (c.open_source.mem_nhds hq)
    filter_upwards [this] with y' hy'
    simp only [Function.comp_apply, τ, c.left_inv hy']
  have hU : c.symm (c q) ∈ P.U q := by rw [hsc]; exact P.mem_U q
  have h2 := c2 hP q j hcqt hU
  change levi (P.φ q ∘ (A.chart k).symm) y v = _
  rw [levi_congr hgerm, levi_comp v hτ (by rw [hτy]; exact h2), hτy]
  exact levi_base hP q j hcqt hU _

theorem compare_local {A : FinHolAtlas e X} {Ω Q : LocPot X} (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (hQ : IsPotential A Q) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, ∀ y ∈ Metric.ball (A.chart j p) r, y ∈ (A.chart j).target → ∀ u : Fin e → ℂ,
        dl A Q j y u ≤ m * dl A Ω j y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (Ω.U p ∩ Q.U p) with hO
  have hOo : IsOpen O :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target ((Ω.isOpen_U p).inter (Q.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨Ω.mem_U p, Q.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have hΩs : ContDiffOn ℝ 2 (Ω.φ p ∘ c.symm) O :=
    ((hΩ.1 p j).mono (fun y hy => ⟨hy.1, hy.2.1⟩)).of_le two_le_infty
  have hws : ContDiffOn ℝ 2 (Q.φ p ∘ c.symm) O :=
    ((hQ.1 p j).mono (fun y hy => ⟨hy.1, hy.2.2⟩)).of_le two_le_infty
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (Ω.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.1⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin e → ℂ) × (Fin e → ℂ) =>
      levi (Q.φ p ∘ c.symm) q.1 q.2 / levi (Ω.φ p ∘ c.symm) q.1 q.2) K :=
    ((continuousOn_levi hOo hws).mono hKO).div ((continuousOn_levi hOo hΩs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨m, hm⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, m, fun y hy' hyt u => ?_⟩
  have hy := Metric.ball_subset_closedBall hy'
  rw [← levi_base hΩ p j hyt (hcb hy).2.1, ← levi_base hQ p j hyt (hcb hy).2.2]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin e → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin e → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : levi (Q.φ p ∘ c.symm) y v / levi (Ω.φ p ∘ c.symm) y v ≤ m := hm ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : levi (Q.φ p ∘ c.symm) y v ≤ m * levi (Ω.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir]
    have : 0 ≤ s ^ 2 := by positivity
    nlinarith

theorem compare_global [CompactSpace X] {A : FinHolAtlas e X} {Ω Q : LocPot X} (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (hQ : IsPotential A Q) :
    ∃ c₀ > (0 : ℝ), ∀ k, ∀ y ∈ (A.chart k).target, ∀ v, c₀ * dl A Q k y v ≤ dl A Ω k y v := by
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p => Classical.choose_spec (A.cover p)
  have key := fun p => compare_local hΩ hpos hQ p (chartIdx A p) (hsrc p)
  choose r hr m hbd using key
  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Metric.mem_ball_self (hr p)⟩)
  have hC0 : 0 ≤ ∑ p ∈ t, |m p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(1 + ∑ p ∈ t, |m p|)⁻¹, by positivity, fun k y hy v => ?_⟩
  obtain ⟨p, hpt, hqV⟩ : ∃ p ∈ t, (A.chart k).symm y ∈ V p := by
    simpa using ht (Set.mem_univ ((A.chart k).symm y))
  rw [dl_chart hΩ _ k hy hqV.1, dl_chart hQ _ k hy hqV.1]
  have ht' := (A.chart _).map_source hqV.1
  have hb := hbd p _ hqV.2 ht' (fderiv ℂ (A.chart (chartIdx A p) ∘ (A.chart k).symm) y v)
  have h0 := dl_nonneg_of_pos hpos _ ht' (fderiv ℂ (A.chart (chartIdx A p) ∘ (A.chart k).symm) y v)
  have hCm : m p ≤ ∑ p ∈ t, |m p| :=
    (le_abs_self (m p)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt)
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

end RootFieldNumerics.A1
