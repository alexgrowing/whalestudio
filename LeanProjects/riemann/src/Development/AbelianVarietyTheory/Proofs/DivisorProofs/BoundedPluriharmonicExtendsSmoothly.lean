import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBoundedByPositivePotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicLogSingularExtendStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open scoped ContDiff

noncomputable section

namespace GlobalTheory.BdExtend

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem smoothOn_cont {U : Set X} (hU : IsOpen U) {u : X → ℝ} (hu : A.SmoothOn U u) : ContinuousOn u U := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨j, hj⟩ := A.cover x
  have h2 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds
      ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩)).continuousAt
  have h3 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    h2.comp ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem dense_compl {Z : Set X} (hZ : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) = 0) : Dense Zᶜ := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨j, hj⟩ := A.cover x
  by_contra h0
  have hsub : U ⊆ Z := fun y hy => by
    by_contra hyZ
    exact h0 ⟨y, hy, hyZ⟩
  have hpos := ((A.chart j).isOpen_inter_preimage_symm hU).measure_pos volume
    ⟨A.chart j x, (A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact hpos.ne' (measure_mono_null (inter_subset_inter_right _ (preimage_mono hsub)) (hZ j))

theorem glue {Z : Set X} (hZ : Dense Zᶜ) {u : X → ℝ}
    (h : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ g : X → ℝ, A.SmoothOn V g ∧ ∀ y ∈ V, y ∉ Z → g y = u y) :
    ∃ g : X → ℝ, A.Smooth g ∧ ∀ x, x ∉ Z → g x = u x := by
  choose V hVo hxV g hg hgu using h
  refine ⟨fun y => g y y, fun j z hz => ?_, fun x hx => hgu x x (hxV x) hx⟩
  have key : ∀ x, ∀ y ∈ V x, g y y = g x y := by
    intro x y hy
    have hO := (hVo x).inter (hVo y)
    have h1 : EqOn (g y) (g x) ((V x ∩ V y) ∩ Zᶜ) := fun p hp => by
      rw [hgu y p hp.1.2 hp.2, hgu x p hp.1.1 hp.2]
    exact h1.of_subset_closure ((smoothOn_cont (hVo y) (hg y)).mono inter_subset_right)
      ((smoothOn_cont (hVo x) (hg x)).mono inter_subset_left) inter_subset_left
      (hZ.open_subset_closure_inter hO) ⟨hy, hxV y⟩
  apply ContDiffAt.contDiffWithinAt
  have hN := ((A.chart j).isOpen_inter_preimage_symm (hVo ((A.chart j).symm z))).mem_nhds ⟨hz.1, hxV _⟩
  refine ((hg _ j).contDiffAt hN).congr_of_eventuallyEq ?_
  filter_upwards [hN] with p hp
  exact key _ _ hp.2

theorem levi_zero_compat {Z : Set X} (hZ : IsClosed Z) {Θ : LocPot X} {u : X → ℝ} (hΘ : IsPotential A Θ)
    (hu : A.SmoothOn Zᶜ u)
    (hL : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, leviAt A (Θ + LocPot.ofFun u) j y w = 0)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (x : X) {z : Fin e → ℂ}
    (hz : z ∈ ψ.target) (hx : ψ.symm z ∈ Θ.U x) (hzZ : ψ.symm z ∉ Z) (w : Fin e → ℂ) :
    levi ((fun y => Θ.φ x y + u y) ∘ ψ.symm) z w = 0 := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hT : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
  have hl : (A.chart j).symm (A.chart j (ψ.symm z)) = ψ.symm z := (A.chart j).left_inv hj
  have hm := (A.chart j).map_source hj
  have hc := GlobalTheory.ChernCompare.compat_self A j
  have h1 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) (A.chart j (ψ.symm z)) :=
    GlobalTheory.ChernCompare.pot_contDiffAt hΘ hc x hm (by rw [hl]; exact hx)
  have h1' : ContDiffAt ℝ 2 (Θ.φ ((A.chart j).symm (A.chart j (ψ.symm z))) ∘ (A.chart j).symm)
      (A.chart j (ψ.symm z)) :=
    GlobalTheory.ChernCompare.pot_contDiffAt hΘ hc _ hm (Θ.mem_U _)
  have h2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) (A.chart j (ψ.symm z)) :=
    ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds
      ⟨hm, by simpa [hl] using hzZ⟩)).of_le (WithTop.coe_le_coe.2 le_top)
  have hev : ((fun y => Θ.φ x y + u y) ∘ ψ.symm) =ᶠ[𝓝 z]
      ((fun p => (Θ.φ x ∘ (A.chart j).symm) p + 1 * (u ∘ (A.chart j).symm) p) ∘ (A.chart j ∘ ψ.symm)) := by
    filter_upwards [(ψ.isOpen_inter_preimage_symm (A.chart j).open_source).mem_nhds ⟨hz, hj⟩] with p hp
    simp [(A.chart j).left_inv hp.2]
  rw [levi_congr hev, levi_comp w hT (h1.add (contDiffAt_const.mul h2))]
  have h3 := hL j _ hm (by rw [hl]; exact hzZ) (fderiv ℂ (A.chart j ∘ ψ.symm) z w)
  have h4 : ((Θ + LocPot.ofFun u).φ ((A.chart j).symm (A.chart j (ψ.symm z))) ∘ (A.chart j).symm) =
      fun p => (Θ.φ ((A.chart j).symm (A.chart j (ψ.symm z))) ∘ (A.chart j).symm) p +
        1 * (u ∘ (A.chart j).symm) p := by
    funext p
    rw [one_mul]
    rfl
  unfold leviAt at h3
  rw [h4, levi_add_smul 1 h1' h2,
    GlobalTheory.ChernCompare.levi_base_compat hΘ hc x hm (by rw [hl]; exact hx)] at h3
  rw [Function.comp_apply, levi_add_smul 1 h1 h2]
  exact h3

theorem log_growth (C B ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, ∀ r a l : ℝ, Real.exp 1 ≤ r → |a| ≤ C * Real.log r →
    r ≤ B - 2 * l → |a| ≤ K - ε * l := by
  have hC : 0 < |C| + 1 := by positivity
  set t := ε / (2 * (|C| + 1)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : (|C| + 1) * t = ε / 2 := by rw [ht]; field_simp
  refine ⟨ε / 2 * B - (|C| + 1) * (1 + Real.log t), fun r a l hr ha hl => ?_⟩
  have hr1 : 1 ≤ r := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hr
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr1
  have h1 : Real.log (r * t) ≤ r * t - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_mul (by positivity) ht0.ne'] at h1
  have h2 : C * Real.log r ≤ (|C| + 1) * Real.log r :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hlog
  have h3 : (|C| + 1) * Real.log r ≤ (|C| + 1) * (r * t - 1 - Real.log t) :=
    mul_le_mul_of_nonneg_left (by linarith) hC.le
  have h4 : (|C| + 1) * (r * t - 1 - Real.log t) = ε / 2 * r - (|C| + 1) * (1 + Real.log t) := by
    rw [← ht1]; ring
  have h5 : ε / 2 * r ≤ ε / 2 * (B - 2 * l) := mul_le_mul_of_nonneg_left hl (by positivity)
  nlinarith

theorem prod_match {n : ℕ} (σ : Fin n → Option (Fin e)) (hσ : ∀ k k' i, σ k = some i → σ k' = some i → k = k')
    (f : Fin e → ℂ) (T : Finset (Fin e)) (hT : ∀ i, i ∈ T ↔ ∃ k, σ k = some i) :
    ∏ k, (σ k).elim 1 f = ∏ i ∈ T, f i := by
  classical
  have h1 : ∀ k, (σ k).elim 1 f = ∏ i, if σ k = some i then f i else 1 := by
    intro k
    cases h : σ k with
    | none => simp
    | some a => simp
  simp_rw [h1]
  rw [Finset.prod_comm, ← Finset.prod_subset (Finset.subset_univ T)]
  · refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨k, hk⟩ := (hT i).1 hi
    rw [Finset.prod_eq_single k]
    · simp [hk]
    · intro k' _ hk'
      rw [if_neg fun h => hk' (hσ k' k i h hk)]
    · simp
  · intro i _ hi
    refine Finset.prod_eq_one fun k _ => if_neg fun h => hi ((hT i).2 ⟨k, h⟩)

theorem local_shape {Z : Set X} {r : X → ℝ} {L : LocPot X} {s : X → X → ℂ} (hs : IsBdSec A Z r L s) {n : ℕ}
    {W : Fin n → Set X} (hW : IsSNC A L s (fun _ => 1) W) (x : X) :
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∃ S : Finset (Fin e),
      (∀ i ∈ S, ψ x i = 0) ∧ ∃ B : ℝ, ∀ᶠ z in 𝓝 (ψ x), z ∈ ψ.target ∧ (ψ.symm z ∉ Z ↔ ∀ i ∈ S, z i ≠ 0) ∧
        (ψ.symm z ∉ Z → r (ψ.symm z) ≤ B - 2 * ∑ i ∈ S, Real.log ‖z i‖) := by
  classical
  obtain ⟨hL, hsec, -, hZ, -, hr⟩ := hs
  obtain ⟨ψ, hψ, hx, hU, σ, hσ, -, v, hv, hv0, hsv⟩ := hW x
  set T : Finset (Fin e) := Finset.univ.filter fun i => ∃ k, σ k = some i with hT
  set S : Finset (Fin e) := T.filter fun i => ψ x i = 0 with hS
  set S' : Finset (Fin e) := T.filter fun i => ¬ ψ x i = 0 with hS'
  set h : (Fin e → ℂ) → ℂ := fun z => (v ∘ ψ.symm) z * ∏ i ∈ S', z i with hh
  have hm := ψ.map_source hx
  have hl := ψ.left_inv hx
  have hhc : ContinuousAt h (ψ x) :=
    (PLAux.analyticAt_compat_fun hψ hv hm (by rw [hl]; exact hx)).continuousAt.mul
      (continuous_finset_prod _ fun i _ => continuous_apply i).continuousAt
  have hh0 : h (ψ x) ≠ 0 := by
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i hi => (Finset.mem_filter.1 hi).2)
    simpa [hl] using hv0 x hx
  have hfac : ∀ z ∈ ψ.target, s x (ψ.symm z) = h z * ∏ i ∈ S, z i := by
    intro z hz
    rw [hsv _ (ψ.map_target hz), hh, mul_assoc, mul_comm (∏ i ∈ S', z i), hS, hS',
      Finset.prod_filter_mul_prod_filter_not, ← prod_match σ hσ z T (by simp [hT])]
    refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
    cases σ k with
    | none => rfl
    | some a => simp [ψ.right_inv hz]
  have hφc : ContinuousAt (L.φ x ∘ ψ.symm) (ψ x) :=
    (GlobalTheory.ChernCompare.pot_contDiffAt hL hψ x hm (by rw [hl]; exact L.mem_U x)).continuousAt
  set H : (Fin e → ℂ) → ℝ := fun z => Real.exp 1 - 2 * Real.log ‖h z‖ + 2 * (L.φ x ∘ ψ.symm) z with hH
  have hHc : ContinuousAt H (ψ x) :=
    (continuousAt_const.sub (continuousAt_const.mul (hhc.norm.log (norm_ne_zero_iff.2 hh0)))).add
      (continuousAt_const.mul hφc)
  refine ⟨ψ, hψ, hx, S, fun i hi => (Finset.mem_filter.1 hi).2, H (ψ x) + 1, ?_⟩
  filter_upwards [ψ.open_target.mem_nhds hm, hhc.eventually_ne hh0,
    hHc.eventually (gt_mem_nhds (lt_add_one (H (ψ x))))] with z hz hz0 hzH
  have hnorm := hsec.2 (ψ.symm z) x (ψ.symm z) ⟨L.mem_U _, hU (ψ.map_target hz)⟩
  have hiff : ψ.symm z ∉ Z ↔ ∀ i ∈ S, z i ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hZ, P.bdry, mem_setOf_eq, ← norm_eq_zero,
      ← mul_eq_zero_iff_right (Real.exp_pos (-L.φ (ψ.symm z) (ψ.symm z))).ne', hnorm,
      mul_eq_zero_iff_right (Real.exp_pos _).ne', norm_eq_zero, hfac z hz, mul_eq_zero_iff_left hz0]
  refine ⟨hz, hiff, fun hzZ => ?_⟩
  have hS0 := hiff.1 hzZ
  rw [hr _ hzZ, P.rW, logNormSec, hnorm, hfac z hz, norm_mul, norm_prod,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hz0)
      (Finset.prod_ne_zero_iff.2 fun i hi => norm_ne_zero_iff.2 (hS0 i hi))) (Real.exp_pos _).ne',
    Real.log_mul (norm_ne_zero_iff.2 hz0) (Finset.prod_ne_zero_iff.2 fun i hi => norm_ne_zero_iff.2 (hS0 i hi)),
    Real.log_prod fun i hi => norm_ne_zero_iff.2 (hS0 i hi), Real.log_exp]
  simp only [hH, Function.comp_apply] at hzH ⊢
  linarith

theorem local_ext {Z : Set X} (hZ : IsClosed Z) {r : X → ℝ} {L : LocPot X} {s : X → X → ℂ} (hs : IsBdSec A Z r L s)
    {n : ℕ} {W : Fin n → Set X} (hW : IsSNC A L s (fun _ => 1) W) {Θ : LocPot X} {u : X → ℝ} {C : ℝ}
    (hΘ : IsPotential A Θ) (hu : A.SmoothOn Zᶜ u)
    (hL : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, leviAt A (Θ + LocPot.ofFun u) j y w = 0)
    (hC : ∀ x, x ∉ Z → |u x| ≤ C * Real.log (r x)) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ g : X → ℝ, A.SmoothOn V g ∧ ∀ y ∈ V, y ∉ Z → g y = u y := by
  obtain ⟨ψ, hψ, hx, S, hS, B, hB⟩ := local_shape hs hW x
  have hm := ψ.map_source hx
  have hl := ψ.left_inv hx
  have hφc : ContinuousAt (Θ.φ x ∘ ψ.symm) (ψ x) :=
    (GlobalTheory.ChernCompare.pot_contDiffAt hΘ hψ x hm (by rw [hl]; exact Θ.mem_U x)).continuousAt
  have h1 : ∀ᶠ z in 𝓝 (ψ x), ψ.symm z ∈ Θ.U x :=
    mem_of_superset ((ψ.isOpen_inter_preimage_symm (Θ.isOpen_U x)).mem_nhds
      ⟨hm, by simpa [hl] using Θ.mem_U x⟩) inter_subset_right
  have h2 : ∀ᶠ z in 𝓝 (ψ x), |(Θ.φ x ∘ ψ.symm) z| < |(Θ.φ x ∘ ψ.symm) (ψ x)| + 1 :=
    hφc.abs.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨R₀, hR₀, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hB.and (h1.and h2))
  have hb' : ∀ z ∈ ball (ψ x) (min R₀ 1), _ := fun z hz => hb z (ball_subset_ball (min_le_left _ _) hz)
  obtain ⟨ρ, hρ, hρR, g, hg, hgf⟩ := GlobalTheory.T.pluriharmonic_log_singular_extend e S (ψ x) (min R₀ 1) ((fun y => Θ.φ x y + u y) ∘ ψ.symm)
    (lt_min hR₀ one_pos) (min_le_right _ _) hS
    (by
      refine ContDiffOn.add (f := Θ.φ x ∘ ψ.symm) (g := u ∘ ψ.symm) ?_ ?_
      · exact (PLAux.contDiffOn_compat hψ (Θ.isOpen_U x) (hΘ.1 x)).mono fun z hz =>
          ⟨(hb' z hz.1).1.1, (hb' z hz.1).2.1⟩
      · exact (PLAux.contDiffOn_compat hψ hZ.isOpen_compl hu).mono fun z hz =>
          ⟨(hb' z hz.1).1.1, (hb' z hz.1).1.2.1.2 hz.2⟩)
    (fun z hz hz0 w => levi_zero_compat hZ hΘ hu hL hψ x (hb' z hz).1.1 (hb' z hz).2.1 ((hb' z hz).1.2.1.2 hz0) w)
    (fun ε hε => by
      obtain ⟨K, hK⟩ := log_growth C B ε hε
      refine ⟨|(Θ.φ x ∘ ψ.symm) (ψ x)| + 1 + K, fun z hz hz0 => ?_⟩
      have hzZ := (hb' z hz).1.2.1.2 hz0
      have h3 := hK _ _ _ (hs.exp_le _ _ _ _ hzZ) (hC _ hzZ) ((hb' z hz).1.2.2 hzZ)
      have h4 := (hb' z hz).2.2
      have h5 := abs_add_le (Θ.φ x (ψ.symm z)) (u (ψ.symm z))
      simp only [Function.comp_apply] at h4 ⊢
      linarith)
  have hV : ∀ y ∈ ψ.source ∩ ψ ⁻¹' ball (ψ x) ρ, ψ y ∈ ball (ψ x) (min R₀ 1) := fun y hy =>
    ball_subset_ball hρR hy.2
  refine ⟨ψ.source ∩ ψ ⁻¹' ball (ψ x) ρ, ψ.isOpen_inter_preimage isOpen_ball, ⟨hx, mem_ball_self hρ⟩,
    fun y => g (ψ y) - Θ.φ x y, fun j => ?_, fun y hy hyZ => ?_⟩
  · refine ContDiffOn.sub (f := g ∘ (ψ ∘ (A.chart j).symm)) (g := Θ.φ x ∘ (A.chart j).symm) ?_ ?_
    · refine hg.comp (fun z hz => ?_) fun z hz => hz.2.2
      exact (((hψ j).1 z ⟨hz.1, hz.2.1⟩).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
    · refine (hΘ.1 x j).mono fun z hz => ⟨hz.1, ?_⟩
      have := (hb' _ (hV _ hz.2)).2.1
      rwa [ψ.left_inv hz.2.1] at this
  · have h3 := (hb' _ (hV y hy)).1.2.1
    rw [ψ.left_inv hy.1] at h3
    have h4 := hgf _ hy.2 (h3.1 hyZ)
    simp only [Function.comp_apply, ψ.left_inv hy.1] at h4
    simp only [h4]
    ring

theorem smooth_extension : ∀ (e : ℕ) (M : Man e), M.FromSec → ∀ (σ : Fin (M.n + 1)) (Θ : LocPot (M.X σ))
    (u : M.X σ → ℝ) (C : ℝ), IsPotential (M.A σ) Θ → (M.A σ).SmoothOn (M.Z σ)ᶜ u →
    (∀ j, ∀ y ∈ ((M.A σ).chart j).target, ((M.A σ).chart j).symm y ∉ M.Z σ → ∀ w,
      GlobalTheory.Mean4O.leviAt (M.A σ) (Θ + LocPot.ofFun u) j y w = 0) →
    (∀ x, x ∉ M.Z σ → |u x| ≤ C * Real.log (M.r σ x)) →
    ∃ g : M.X σ → ℝ, (M.A σ).Smooth g ∧ ∀ x, x ∉ M.Z σ → g x = u x := by
  intro e M hM σ Θ u C hΘ hu hL hC
  obtain ⟨-, L, s, hs, n, W, hW⟩ := hM σ
  exact glue (dense_compl (M.bd σ).2.1) (local_ext (M.bd σ).1 hs hW hΘ hu hL hC)

end GlobalTheory.BdExtend
