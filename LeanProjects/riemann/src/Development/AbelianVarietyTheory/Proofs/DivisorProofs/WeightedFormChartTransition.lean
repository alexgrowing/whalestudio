import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormTransitionCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianAdjugateDivergenceFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityGlueingUnderTransition
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

theorem IsDens.neg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ρ : AlgChart p σ D → CxPts p σ → ℝ} (h : IsDens ρ) : IsDens fun c y => -ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', mul_neg], fun c => (h.2 c).neg⟩

theorem part_compl_eq_zero {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ρ : AlgChart p σ D → CxPts p σ → ℝ} {K : Set (CxPts p σ)} (hK : MeasurableSet K)
    (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, y ∉ K → ρ c y ≤ 0) : part ρ Kᶜ = 0 := by
  have key : part ρ ≤ (part ρ).restrict K := iSup_le fun c => by
    have e : ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) Kᶜ = 0 := by
      rw [ChartGlue.chartMeas_apply _ _ hK.compl]
      refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
        (c.e.open_source.measurableSet.inter hK.compl) Set.inter_subset_left) ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1]
      exact ENNReal.ofReal_eq_zero.2 (h c y hy.1 hy.2)
    rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c)
  refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
  rw [Measure.restrict_apply hK.compl, Set.compl_inter_self, measure_empty]

theorem total_dbar_eq_zero_of_compact_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (α : AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ), (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => α c (c.e.symm v) j) (c.e y)) → (∀ (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ j, α c y j = ∑ a, transMat c c' y a j * α c' y a) → ∀ (c₀ : AlgChart p σ (d + 1)) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, y ∉ K → ∀ j, α c y j = 0) → total (fun (c : AlgChart p σ (d + 1)) y => mix d (chernMat φ c y) (Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1))) = 0 := by
  intro k _ X p σ d _ _ B φ hφ α h1 h2 c₀ K hK hKs h3
  set N : AlgChart p σ (d + 1) → CxPts p σ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun c y =>
    Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1) with hN
  set ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ := fun c y => mix d (chernMat φ c y) (N c y) with hρ
  have hD : IsDens ρ := GlobalTheory.T.chart_form_transition_compatible k X p σ d _ α (chernMat_isForm k X p σ (d + 1) B φ hφ) h1 h2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet

  have hz : ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, y ∉ K → ρ c y = 0 := fun c y hy hyK => by
    have hW := ChartGlue.isOpen_over c.e hK.isClosed.isOpen_compl
    have hN0 : N c y = 0 := by
      ext j l
      have he : (fun v => α c (c.e.symm v) j) =ᶠ[𝓝 (c.e y)] fun _ => 0 := by
        filter_upwards [hW.mem_nhds (ChartGlue.mem_over c.e hy hyK)] with v hv
        exact h3 c _ (c.e.map_target hv.1) hv.2 j
      simp only [hN, Matrix.of_apply, Matrix.zero_apply]
      rw [dbar_congr he, dbar_const]
      rfl
    simp only [hρ, hN0, mix, Matrix.mul_zero, trace_zero, Complex.zero_re, mul_zero]

  set A : Set (V (d + 1)) := c₀.e '' K with hAdef
  have hA : IsCompact A := hK.image_of_continuousOn (c₀.e.continuousOn.mono hKs)
  have hAt : A ⊆ c₀.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c₀.e.map_source (hKs hy)
  have hα : ∀ v ∈ c₀.e.target, ∀ j, ContDiffAt ℝ 1 (fun w => α c₀ (c₀.e.symm w) j) v := fun v hv j => by
    have := h1 c₀ _ (c₀.e.map_target hv) j
    rwa [c₀.e.right_inv hv] at this

  have loc : ∀ v ∈ c₀.e.target, ∃ u : V (d + 1) → ℂ, ContDiffAt ℝ 3 u v ∧
      ∀ᶠ w in 𝓝 v, chernMat φ c₀ (c₀.e.symm w) = cHess (d + 1) u w := fun v hv => by
    have ho := ChartGlue.isOpen_over c₀.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick φ.isLB (c₀.e.symm v))))
    have hm : v ∈ c₀.e.target ∩ c₀.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c₀.e.symm v))) :=
      ⟨hv, mem_pick φ.isLB _⟩
    have hs : ContDiffOn ℝ ∞ (fun w => ((φ.φ (pick φ.isLB (c₀.e.symm v)) (c₀.e.symm w) : ℝ) : ℂ))
        (c₀.e.target ∩ c₀.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c₀.e.symm v)))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart (hφ _) c₀)
    refine ⟨_, (hs.contDiffAt (ho.mem_nhds hm)).of_le (by norm_cast), ?_⟩
    filter_upwards [ho.mem_nhds hm] with w hw
    unfold chernMat
    rw [c₀.hess_eq hφ (c₀.e.map_target hw.1) hw.2 (mem_pick _ _), AlgChart.hess, c₀.e.right_inv hw.1]

  have hadj : ∀ v ∈ c₀.e.target,
      (∀ l j, ContDiffAt ℝ 1 (fun w => (chernMat φ c₀ (c₀.e.symm w)).adjugate l j) v) ∧
      ∀ j, ∑ l, dbar (fun w => (chernMat φ c₀ (c₀.e.symm w)).adjugate l j) v (EuclideanSpace.single l 1) = 0 :=
    fun v hv => by
    obtain ⟨u, hu, he⟩ := loc v hv
    obtain ⟨P1, P2⟩ := GlobalTheory.T.complex_hessian_adjugate_divergence_free (d + 1) u v hu
    have he' : ∀ l j, (fun w => (chernMat φ c₀ (c₀.e.symm w)).adjugate l j) =ᶠ[𝓝 v]
        fun w => (cHess (d + 1) u w).adjugate l j := fun l j => he.mono fun w hw => by
      dsimp only
      rw [hw]
    refine ⟨fun l j => (P1 l j).congr_of_eventuallyEq (he' l j), fun j => ?_⟩
    rw [← P2 j]
    exact Finset.sum_congr rfl fun l _ => by rw [dbar_congr (he' l j)]

  set G : Fin (d + 1) → V (d + 1) → ℂ := fun l v =>
    ∑ j, (chernMat φ c₀ (c₀.e.symm v)).adjugate l j * α c₀ (c₀.e.symm v) j with hGdef
  set F : Fin (d + 1) → V (d + 1) → ℂ := fun l => c₀.e.target.indicator (G l) with hFdef
  have hF0 : ∀ l, ∀ v ∉ A, F l v = 0 := fun l v hv => by
    by_cases ht : v ∈ c₀.e.target
    · simp only [hFdef, Set.indicator_of_mem ht, hGdef]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h3 c₀ _ (c₀.e.map_target ht) (fun hk => hv ⟨_, hk, c₀.e.right_inv ht⟩) j, mul_zero]
    · simp only [hFdef, Set.indicator_of_notMem ht]
  have hFt : ∀ l, ∀ v ∈ c₀.e.target, F l =ᶠ[𝓝 v] G l := fun l v hv => by
    filter_upwards [c₀.e.open_target.mem_nhds hv] with w hw
    simp only [hFdef, Set.indicator_of_mem hw]
  have hFA : ∀ l, ∀ v ∉ A, F l =ᶠ[𝓝 v] fun _ => 0 := fun l v hv => by
    filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 l w hw
  have hGC : ∀ l, ∀ v ∈ c₀.e.target, ContDiffAt ℝ 1 (G l) v := fun l v hv =>
    ContDiffAt.sum fun j _ => ((hadj v hv).1 l j).mul (hα v hv j)
  have hFC : ∀ l, ContDiff ℝ 1 (F l) := fun l => contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ c₀.e.target
    · exact (hGC l v ht).congr_of_eventuallyEq (hFt l v ht)
    · exact contDiffAt_const.congr_of_eventuallyEq (hFA l v fun h => ht (hAt h))
  have hFs : ∀ l, HasCompactSupport (F l) := fun l => HasCompactSupport.intro hA (hF0 l)

  have hid : ∀ v ∈ c₀.e.target, ((chernMat φ c₀ (c₀.e.symm v)).adjugate * N c₀ (c₀.e.symm v)).trace =
      ∑ l, dbar (F l) v (EuclideanSpace.single l 1) := fun v hv => by
    have hd : ∀ l, dbar (F l) v (EuclideanSpace.single l 1) = ∑ j,
        ((chernMat φ c₀ (c₀.e.symm v)).adjugate l j *
          dbar (fun w => α c₀ (c₀.e.symm w) j) v (EuclideanSpace.single l 1) +
        dbar (fun w => (chernMat φ c₀ (c₀.e.symm w)).adjugate l j) v (EuclideanSpace.single l 1) *
          α c₀ (c₀.e.symm v) j) := fun l => by
      rw [dbar_congr (hFt l v hv), hGdef,
        dbar_sum (A := fun j w => (chernMat φ c₀ (c₀.e.symm w)).adjugate l j * α c₀ (c₀.e.symm w) j)
          (fun j _ => (((hadj v hv).1 l j).mul (hα v hv j)).differentiableAt (by norm_num)),
        ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl fun j _ => dbar_mul (((hadj v hv).1 l j).differentiableAt (by norm_num))
        ((hα v hv j).differentiableAt (by norm_num)) _
    have h0 : ∑ l, ∑ j, dbar (fun w => (chernMat φ c₀ (c₀.e.symm w)).adjugate l j) v (EuclideanSpace.single l 1) *
        α c₀ (c₀.e.symm v) j = 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun j _ => by rw [← Finset.sum_mul, (hadj v hv).2 j, zero_mul]
    simp only [hd, Finset.sum_add_distrib, h0, add_zero]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hN, Matrix.of_apply, c₀.e.right_inv hv]
  set H : V (d + 1) → ℝ := fun v => d.factorial / Real.pi ^ (d + 1) *
    ∑ l, (dbar (F l) v (EuclideanSpace.single l 1)).re with hHdef
  have hI := fun l => GlobalTheory.CurveDens.integral_re_dbar_eq_zero (hFC l) (hFs l) (EuclideanSpace.single l 1)
  have hHi : Integrable H := (integrable_finset_sum _ fun l _ => (hI l).1).const_mul _
  have hH0 : ∫ v, H v = 0 := by
    simp only [hHdef]
    rw [integral_const_mul, integral_finset_sum _ fun l _ => (hI l).1]
    simp [fun l => (hI l).2]
  have hHA : ∀ v ∉ A, H v = 0 := fun v hv => by
    simp only [hHdef]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun l _ => ?_)
    rw [dbar_congr (hFA l v hv), dbar_const]
    rfl
  have hHt : ∀ v ∈ A, H v = ρ c₀ (c₀.e.symm v) := fun v hv => by
    simp only [hHdef, hρ, mix]
    rw [hid v (hAt hv), Complex.re_sum]

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

end GlobalTheory.MixDens
