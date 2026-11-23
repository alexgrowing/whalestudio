import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace PositivityTheory.Xgp.c_grad_atlas

theorem mono_bd {r a c C t : ℝ} (hr : 1 ≤ r) (ha : 0 ≤ a) (ht : t ≤ c * r ^ c)
    (h1 : a * |c| ≤ C) (h2 : |c| ≤ C) : a * t ≤ C * r ^ C := by
  have hC : 0 ≤ C := le_trans (abs_nonneg c) h2
  have hr0 : 0 < r := by linarith
  have hrC : 0 < r ^ C := Real.rpow_pos_of_pos hr0 C
  have hrc0 : 0 < r ^ c := Real.rpow_pos_of_pos hr0 c
  have h3 : a * t ≤ a * (c * r ^ c) := mul_le_mul_of_nonneg_left ht ha
  rcases le_or_gt 0 c with hc | hc
  · have hcC : c ≤ C := le_trans (le_abs_self c) h2
    have hrc : r ^ c ≤ r ^ C := Real.rpow_le_rpow_of_exponent_le hr hcC
    have hac : a * c ≤ C := by
      rw [abs_of_nonneg hc] at h1
      exact h1
    calc a * t ≤ a * (c * r ^ c) := h3
      _ = (a * c) * r ^ c := by ring
      _ ≤ C * r ^ c := mul_le_mul_of_nonneg_right hac hrc0.le
      _ ≤ C * r ^ C := mul_le_mul_of_nonneg_left hrc hC
  · have h4 : c * r ^ c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hrc0.le
    have h5 : a * (c * r ^ c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha h4
    nlinarith [mul_nonneg hC hrC.le]

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : s x x ≠ 0 := hx
  obtain ⟨j, hj⟩ := A.cover x
  have hf := hs.1 x j
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (L.U x) := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, (A.chart j).left_inv hj]
    exact L.mem_U x
  have hc1 : ContinuousAt (s x ∘ (A.chart j).symm) ((A.chart j) x) := (hf _ hmem).continuousAt
  have hc2 : ContinuousAt ((s x ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    hc1.comp ((A.chart j).continuousAt hj)
  have heq : ((s x ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 x] s x := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  have hc : ContinuousAt (s x) x := hc2.congr heq
  have hne : ∀ᶠ y in 𝓝 x, s x y ≠ 0 := hc.eventually_ne hx'
  filter_upwards [hne, (L.isOpen_U x).mem_nhds (L.mem_U x)] with y hy hyU
  show s y y ≠ 0
  intro h0
  have key := hs.2 x y y ⟨hyU, L.mem_U y⟩
  rw [h0, norm_zero, zero_mul] at key
  have : 0 < ‖s x y‖ * Real.exp (-L.φ x y) := mul_pos (norm_pos_iff.mpr hy) (Real.exp_pos _)
  linarith

theorem local_bd {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hs : IsSection A L s) (hn : ∀ y, logNormSec L s y ≤ 0) (hAB : A.Compatible B)
    (ph : X → ℝ) (hph : A.SmoothOn (bdry s)ᶜ ph) (j : Fin B.n) (y₀ : Fin e → ℂ) (hy₀ : y₀ ∈ (B.chart j).target)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ) (hψ : IsCompatChart A ψ) (hV : IsOpen V)
    (hx : (B.chart j).symm y₀ ∈ V) (hVs : V ⊆ ψ.source)
    (hb : ∀ x' ∈ V, x' ∉ bdry s →
      ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) :
    ∃ C₅, ∀ᶠ y in 𝓝 y₀, ∀ C, C₅ ≤ C → (B.chart j).symm y ∉ bdry s →
      ‖fderiv ℝ (ph ∘ (B.chart j).symm) y‖ ≤
        C * rW L s ((B.chart j).symm y) ^ C * Real.exp (rW L s ((B.chart j).symm y) / 2) := by
  set φ := B.chart j with hφ
  set τ : (Fin e → ℂ) → (Fin e → ℂ) := ψ ∘ φ.symm with hτ
  have hx₀ψ : φ.symm y₀ ∈ ψ.source := hVs hx
  obtain ⟨k, hk⟩ := A.cover (φ.symm y₀)
  have hτan : AnalyticAt ℂ τ y₀ := by
    have h1 : AnalyticAt ℂ (A.chart k ∘ φ.symm) y₀ := hAB.2 j k y₀ ⟨hy₀, hk⟩
    have h2 : AnalyticAt ℂ (ψ ∘ (A.chart k).symm) ((A.chart k ∘ φ.symm) y₀) := by
      apply (hψ k).1
      refine ⟨(A.chart k).map_source hk, ?_⟩
      simp only [Set.mem_preimage, Function.comp_apply, (A.chart k).left_inv hk]
      exact hx₀ψ
    have h3 := h2.comp h1
    apply h3.congr
    have hnb : φ.symm ⁻¹' (A.chart k).source ∈ 𝓝 y₀ :=
      (φ.continuousAt_symm hy₀).preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [hnb] with y hy
    simp [hτ, (A.chart k).left_inv hy]
  have hev := hτan.eventually_analyticAt
  have hdc : ContinuousAt (fderiv ℂ τ) y₀ := hτan.fderiv.continuousAt
  set K := ‖fderiv ℂ τ y₀‖ + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hKev : ∀ᶠ y in 𝓝 y₀, ‖fderiv ℂ τ y‖ < K :=
    hdc.norm.eventually (Iio_mem_nhds (by linarith))
  have hW : ∀ᶠ y in 𝓝 y₀, y ∈ φ.target ∧ φ.symm y ∈ V := by
    have h1 : φ.target ∈ 𝓝 y₀ := φ.open_target.mem_nhds hy₀
    have h2 : φ.symm ⁻¹' V ∈ 𝓝 y₀ := (φ.continuousAt_symm hy₀).preimage_mem_nhds (hV.mem_nhds hx)
    filter_upwards [h1, h2] with y a b
    exact ⟨a, b⟩
  refine ⟨max (K * |c|) |c|, ?_⟩
  have hWnhds : ∀ᶠ y in 𝓝 y₀, ∀ᶠ y' in 𝓝 y, y' ∈ φ.target ∧ φ.symm y' ∈ V := hW.eventually_nhds
  filter_upwards [hev, hKev, hW, hWnhds] with y hyan hyK hyW hyW'
  intro C hC hyb
  have hx'V : φ.symm y ∈ V := hyW.2
  have hx'ψ : φ.symm y ∈ ψ.source := hVs hx'V
  have hτy : τ y = ψ (φ.symm y) := rfl
  have hψt : τ y ∈ ψ.target := by
    rw [hτy]
    exact ψ.map_source hx'ψ
  have hψl : ψ.symm (τ y) = φ.symm y := by
    rw [hτy]
    exact ψ.left_inv hx'ψ
  have hgd : DifferentiableAt ℝ (ph ∘ ψ.symm) (τ y) := by
    obtain ⟨k', hk'⟩ := A.cover (φ.symm y)
    have hopen : IsOpen ((A.chart k').target ∩ (A.chart k').symm ⁻¹' (bdry s)ᶜ) :=
      (A.chart k').continuousOn_symm.isOpen_inter_preimage (A.chart k').open_target
        (isOpen_compl_bdry A L s hs)
    have hmem : (A.chart k') (φ.symm y) ∈ (A.chart k').target ∩ (A.chart k').symm ⁻¹' (bdry s)ᶜ := by
      refine ⟨(A.chart k').map_source hk', ?_⟩
      simp only [Set.mem_preimage, (A.chart k').left_inv hk']
      exact hyb
    have hd1 : DifferentiableAt ℝ (ph ∘ (A.chart k').symm) ((A.chart k') (φ.symm y)) :=
      ((hph k').differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
    have hd2 : AnalyticAt ℂ ((A.chart k') ∘ ψ.symm) (τ y) := by
      apply (hψ k').2
      refine ⟨hψt, ?_⟩
      simp only [Set.mem_preimage, hψl]
      exact hk'
    have hd3 : DifferentiableAt ℝ ((ph ∘ (A.chart k').symm) ∘ ((A.chart k') ∘ ψ.symm)) (τ y) := by
      apply DifferentiableAt.comp (τ y)
      · rw [Function.comp_apply, hψl]
        exact hd1
      · exact hd2.differentiableAt.restrictScalars ℝ
    apply hd3.congr_of_eventuallyEq
    have hnb : ψ.symm ⁻¹' (A.chart k').source ∈ 𝓝 (τ y) :=
      (ψ.continuousAt_symm hψt).preimage_mem_nhds
        ((A.chart k').open_source.mem_nhds (by rw [hψl]; exact hk'))
    filter_upwards [hnb] with z hz
    simp [(A.chart k').left_inv hz]
  have hτd : DifferentiableAt ℝ τ y := hyan.differentiableAt.restrictScalars ℝ
  have hfeq : fderiv ℝ (ph ∘ φ.symm) y = fderiv ℝ ((ph ∘ ψ.symm) ∘ τ) y := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hyW'] with z hz
    simp [hτ, ψ.left_inv (hVs hz.2)]
  have hchain : fderiv ℝ ((ph ∘ ψ.symm) ∘ τ) y =
      (fderiv ℝ (ph ∘ ψ.symm) (τ y)).comp (fderiv ℝ τ y) := fderiv_comp y hgd hτd
  have hτn : ‖fderiv ℝ τ y‖ ≤ K := by
    rw [(hyan.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv]
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact hyK.le
  have hgb : ‖fderiv ℝ (ph ∘ ψ.symm) (τ y)‖ ≤
      c * rW L s (φ.symm y) ^ c * Real.exp (rW L s (φ.symm y) / 2) := hb _ hx'V hyb
  have hr1 : 1 ≤ rW L s (φ.symm y) := by
    have h0 := hn (φ.symm y)
    have he : (1:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    show 1 ≤ Real.exp 1 - 2 * logNormSec L s (φ.symm y)
    linarith
  have hm := mono_bd (t := c * rW L s (φ.symm y) ^ c) hr1 hK0 le_rfl
    (le_trans (le_max_left _ _) hC) (le_trans (le_max_right _ _) hC)
  have hE : 0 < Real.exp (rW L s (φ.symm y) / 2) := Real.exp_pos _
  rw [hfeq, hchain]
  calc ‖(fderiv ℝ (ph ∘ ψ.symm) (τ y)).comp (fderiv ℝ τ y)‖
      ≤ ‖fderiv ℝ (ph ∘ ψ.symm) (τ y)‖ * ‖fderiv ℝ τ y‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (c * rW L s (φ.symm y) ^ c * Real.exp (rW L s (φ.symm y) / 2)) * K :=
      mul_le_mul hgb hτn (norm_nonneg _) (le_trans (norm_nonneg _) hgb)
    _ = (K * (c * rW L s (φ.symm y) ^ c)) * Real.exp (rW L s (φ.symm y) / 2) := by ring
    _ ≤ (C * rW L s (φ.symm y) ^ C) * Real.exp (rW L s (φ.symm y) / 2) :=
      mul_le_mul_of_nonneg_right hm hE.le

end PositivityTheory.Xgp.c_grad_atlas

open PositivityTheory.Xgp.c_grad_atlas in

theorem PositivityTheory.Xgp.t_c_grad_atlas : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → ∀ ph : X → ℝ, A.SmoothOn (bdry s)ᶜ ph → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ), IsCompatChart A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry s → ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) → ∃ C₅, ∀ C, C₅ ≤ C → IsGradBound B L s ph C := by
  intro e X _ _ _ A B L s nb m W hpot hsec hsnc hn had ph hph hloc
  have hj : ∀ j : Fin B.n, ∃ D : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) (3 / 2), ∀ C, D ≤ C →
      (B.chart j).symm y ∉ bdry s →
      ‖fderiv ℝ (ph ∘ (B.chart j).symm) y‖ ≤
        C * rW L s ((B.chart j).symm y) ^ C * Real.exp (rW L s ((B.chart j).symm y) / 2) := by
    intro j
    have hl : ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) (3 / 2), ∃ D : ℝ, ∀ᶠ z in 𝓝 y, ∀ C, D ≤ C →
        (B.chart j).symm z ∉ bdry s →
        ‖fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤
          C * rW L s ((B.chart j).symm z) ^ C * Real.exp (rW L s ((B.chart j).symm z) / 2) := by
      intro y hy
      have hyt : y ∈ (B.chart j).target :=
        had.2.1 j (Metric.closedBall_subset_closedBall (by norm_num) hy)
      obtain ⟨ψ, V, c, hψ, hV, hxV, hVs, hb⟩ := hloc ((B.chart j).symm y)
      exact local_bd A B L s hsec hn had.1 ph hph j y hyt ψ V c hψ hV hxV hVs hb
    choose! D hD using hl
    obtain ⟨t, -, hcov⟩ := (isCompact_closedBall (0 : Fin e → ℂ) (3 / 2)).elim_nhds_subcover
      (fun y => {z | ∀ C, D y ≤ C → (B.chart j).symm z ∉ bdry s →
        ‖fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤
          C * rW L s ((B.chart j).symm z) ^ C * Real.exp (rW L s ((B.chart j).symm z) / 2)})
      (fun y hy => hD y hy)
    refine ⟨∑ y ∈ t, |D y|, ?_⟩
    intro z hz C hC hzb
    obtain ⟨y, hyt, hzU⟩ := Set.mem_iUnion₂.1 (hcov hz)
    have h1 : D y ≤ ∑ y ∈ t, |D y| :=
      le_trans (le_abs_self _) (Finset.single_le_sum (f := fun y => |D y|) (fun i _ => abs_nonneg _) hyt)
    exact hzU C (le_trans h1 hC) hzb
  choose Dj hDj using hj
  refine ⟨∑ j, |Dj j|, ?_⟩
  intro C hC j y hy hyb
  have h1 : Dj j ≤ ∑ j, |Dj j| :=
    le_trans (le_abs_self _) (Finset.single_le_sum (f := fun j => |Dj j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))
  exact hDj j y (Metric.ball_subset_closedBall hy) C (le_trans h1 hC) hyb
