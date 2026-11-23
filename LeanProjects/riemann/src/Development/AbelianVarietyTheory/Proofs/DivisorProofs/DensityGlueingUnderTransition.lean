import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDensityOfTransitionStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem part_compl_eq_zero {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {ρ : AlgChart p σ 1 → CxPts p σ → ℝ} {K : Set (CxPts p σ)} (hK : MeasurableSet K)
    (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → ρ c y ≤ 0) : part ρ Kᶜ = 0 := by
  have key : part ρ ≤ (part ρ).restrict K := iSup_le fun c => by
    have e : ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) Kᶜ = 0 := by
      rw [ChartGlue.chartMeas_apply _ _ hK.compl]
      refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
        (c.e.open_source.measurableSet.inter hK.compl) Set.inter_subset_left) ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1]
      exact ENNReal.ofReal_eq_zero.2 (h c y hy.1 hy.2)
    rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ 1 =>
      ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c)
  refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
  rw [Measure.restrict_apply hK.compl, Set.compl_inter_self, measure_empty]

theorem integral_re_dbar_eq_zero {n : ℕ} {F : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (u : ReciprocityTheory.L2DbarEstimates.V n) :
    Integrable (fun v => (dbar F v u).re) ∧ ∫ v, (dbar F v u).re = 0 := by
  have hint : ∀ w : ReciprocityTheory.L2DbarEstimates.V n, Integrable (fun y => fderiv ℝ F y w) := fun w =>
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => dbar F v u) := by
    simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  refine ⟨Complex.reCLM.integrable_comp hD, ?_⟩
  have h0 : ∫ v, dbar F v u = 0 := by
    simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n F hF hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n F hF hc]
    simp
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

theorem total_dbar_eq_zero_of_compact_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → ∀ (c₀ : AlgChart p σ 1) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → m c y = 0) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  intro k _ X p σ _ _ m h1 h2 c₀ K hK hKs h3
  set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y =>
    (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ
  have hD : IsDens ρ := GlobalTheory.T.dbar_density_of_transition k X p σ m h1 h2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet

  have hz : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → ρ c y = 0 := fun c y hy hyK => by
    have hW := ChartGlue.isOpen_over c.e hK.isClosed.isOpen_compl
    have he : (fun v => m c (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun _ => 0 := by
      filter_upwards [hW.mem_nhds (ChartGlue.mem_over c.e hy hyK)] with v hv
      exact h3 c _ (c.e.map_target hv.1) hv.2
    simp only [hρ]
    rw [dbar_congr he, dbar_apply]
    simp

  set A : Set (ReciprocityTheory.L2DbarEstimates.V 1) := c₀.e '' K with hAdef
  have hA : IsCompact A := hK.image_of_continuousOn (c₀.e.continuousOn.mono hKs)
  have hAt : A ⊆ c₀.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c₀.e.map_source (hKs hy)
  set F : ReciprocityTheory.L2DbarEstimates.V 1 → ℂ := c₀.e.target.indicator fun v => m c₀ (c₀.e.symm v) with hFdef
  have hF0 : ∀ v ∉ A, F v = 0 := fun v hv => by
    by_cases ht : v ∈ c₀.e.target
    · rw [hFdef, Set.indicator_of_mem ht]
      refine h3 c₀ _ (c₀.e.map_target ht) fun hk => hv ⟨_, hk, c₀.e.right_inv ht⟩
    · rw [hFdef, Set.indicator_of_notMem ht]
  have hFt : ∀ v ∈ c₀.e.target, F =ᶠ[𝓝 v] fun v => m c₀ (c₀.e.symm v) := fun v hv => by
    filter_upwards [c₀.e.open_target.mem_nhds hv] with w hw
    rw [hFdef, Set.indicator_of_mem hw]
  have hFA : ∀ v ∉ A, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFC : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ c₀.e.target
    · have := h1 c₀ _ (c₀.e.map_target ht)
      rw [c₀.e.right_inv ht] at this
      exact this.congr_of_eventuallyEq (hFt v ht)
    · exact contDiffAt_const.congr_of_eventuallyEq (hFA v fun h => ht (hAt h))
  have hFs : HasCompactSupport F := HasCompactSupport.intro hA hF0
  obtain ⟨hHi, hH0⟩ := integral_re_dbar_eq_zero hFC hFs (EuclideanSpace.single 0 1)
  set H : ReciprocityTheory.L2DbarEstimates.V 1 → ℝ := fun v => (dbar F v (EuclideanSpace.single 0 1)).re with hHdef
  have hHA : ∀ v ∉ A, H v = 0 := fun v hv => by
    simp only [hHdef]
    rw [dbar_congr (hFA v hv), dbar_apply]
    simp
  have hHt : ∀ v ∈ A, H v = ρ c₀ (c₀.e.symm v) := fun v hv => by
    simp only [hHdef, hρ]
    rw [dbar_congr (hFt v (hAt hv)), c₀.e.right_inv (hAt hv)]

  have hl : ∀ τ : ℝ → ℝ, τ 0 = 0 → ∫⁻ v, ENNReal.ofReal (τ (H v)) =
      ∫⁻ v in A, ENNReal.ofReal (τ (ρ c₀ (c₀.e.symm v))) := fun τ h0 => by
    rw [← lintegral_indicator hA.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A
    · rw [Set.indicator_of_mem hv, hHt v hv]
    · rw [Set.indicator_of_notMem hv, hHA v hv, h0, ENNReal.ofReal_zero]
  have hp : part ρ Set.univ = ∫⁻ v, ENNReal.ofReal (H v) := by
    rw [hl (fun t => t) rfl, ← measure_add_measure_compl hKm,
      part_compl_eq_zero hKm fun c y hy hyK => (hz c y hy hyK).le, add_zero,
      hD.part_apply c₀ hKm hKs]
  have hn : part (fun c y => -ρ c y) Set.univ = ∫⁻ v, ENNReal.ofReal (-H v) := by
    rw [hl (fun t => -t) neg_zero, ← measure_add_measure_compl hKm,
      part_compl_eq_zero hKm fun c y hy hyK => by rw [hz c y hy hyK, neg_zero], add_zero,
      hD.neg.part_apply c₀ hKm hKs]
  rw [total, hp, hn, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi]
  exact hH0

end GlobalTheory.CurveDens
