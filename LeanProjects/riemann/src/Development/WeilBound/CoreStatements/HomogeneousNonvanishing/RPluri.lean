import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CPluri

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

private theorem continuousOn_levi_of_contDiffOn' {e : ℕ} (d : (Fin e → ℂ) → ℝ) (c : Fin e → ℂ) (r : ℝ) (w : Fin e → ℂ)
    (hd2 : ContDiffOn ℝ 2 d (Metric.ball c r)) :
    ContinuousOn (fun v => ReciprocityTheory.AnForm.levi d v w) (Metric.ball c r) := by
  have hc0 := ReciprocityTheory.AnForm.continuousOn_levi Metric.isOpen_ball hd2
  refine hc0.comp (f := fun v : Fin e → ℂ => (v, w)) ?_ ?_
  · exact (continuous_id.prodMk continuous_const).continuousOn
  · intro v hv
    exact Set.mk_mem_prod hv (Set.mem_univ w)

open HolomorphicMinorCharts ReciprocityTheory.AnForm in
theorem r_pluri : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P Q : LocPot X), IsPotential A P → IsPotential A Q → IsOpen U → Dense U → SamePot A U P Q → SamePot A Set.univ P Q := by
  intro e X _ _ _ A U P Q hP hQ hUo hUd hS x _
  obtain ⟨j, hxj⟩ := A.cover x
  set ψ := A.chart j with hψ
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) :=
    ψ.isOpen_inter_preimage_symm ((P.isOpen_U x).inter (Q.isOpen_U x))
  have hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x) := by
    refine ⟨ψ.map_source hxj, ?_⟩
    show ψ.symm (ψ x) ∈ P.U x ∩ Q.U x
    rw [ψ.left_inv hxj]
    exact ⟨P.mem_U x, Q.mem_U x⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO (ψ x) hxO
  set d : (Fin e → ℂ) → ℝ := fun z => P.φ x (ψ.symm z) - Q.φ x (ψ.symm z) with hdd
  have h1 := (hP.1 x j).mono (fun v (hv : v ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) => (⟨hv.1, hv.2.1⟩ : v ∈ ψ.target ∩ ψ.symm ⁻¹' P.U x))
  have h2 := (hQ.1 x j).mono (fun v (hv : v ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) => (⟨hv.1, hv.2.2⟩ : v ∈ ψ.target ∩ ψ.symm ⁻¹' Q.U x))
  have hd2 : ContDiffOn ℝ 2 d (Metric.ball (ψ x) r) :=
    ((h1.sub h2).mono hball).of_le (WithTop.coe_le_coe.mpr le_top)
  clear_value d
  clear h1 h2
  have hzero : ∀ z ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x), ψ.symm z ∈ U → ∀ w, levi d z w = 0 := by
    intro z hz hzU w
    have hyPx : ψ.symm z ∈ P.U x := hz.2.1
    have hyQx : ψ.symm z ∈ Q.U x := hz.2.2
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hEq1⟩ := hP.2 x (ψ.symm z) (ψ.symm z) ⟨hyPx, P.mem_U _⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hEq2⟩ := hQ.2 x (ψ.symm z) (ψ.symm z) ⟨hyQx, Q.mem_U _⟩
    obtain ⟨V3, hV3o, hyV3, G3, hG3, hEq3⟩ := hS (ψ.symm z) hzU
    have hNo : IsOpen (W1 ∩ W2 ∩ V3 ∩ P.U x ∩ P.U (ψ.symm z) ∩ Q.U x ∩ Q.U (ψ.symm z)) :=
      ((((((hW1o.inter hW2o).inter hV3o).inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter
        (Q.isOpen_U x)).inter (Q.isOpen_U _))
    have hyN : ψ.symm z ∈ W1 ∩ W2 ∩ V3 ∩ P.U x ∩ P.U (ψ.symm z) ∩ Q.U x ∩ Q.U (ψ.symm z) :=
      ⟨⟨⟨⟨⟨⟨hyW1, hyW2⟩, hyV3⟩, hyPx⟩, P.mem_U _⟩, hyQx⟩, Q.mem_U _⟩
    have hH : AnalyticAt ℂ (fun v => G1 (ψ.symm v) - G2 (ψ.symm v) + G3 (ψ.symm v)) z :=
      ((hG1 j z ⟨hz.1, hyW1⟩).sub (hG2 j z ⟨hz.1, hyW2⟩)).add (hG3 j z ⟨hz.1, hyV3⟩)
    have hev : d =ᶠ[𝓝 z] fun v => (G1 (ψ.symm v) - G2 (ψ.symm v) + G3 (ψ.symm v)).re := by
      have hmem := (ψ.continuousAt_symm hz.1).preimage_mem_nhds (hNo.mem_nhds hyN)
      filter_upwards [hmem] with v hv
      obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hv
      have e1 := hEq1 _ ⟨⟨a1, a4⟩, a5⟩
      have e2 := hEq2 _ ⟨⟨a2, a6⟩, a7⟩
      have e3 := hEq3 _ a3
      simp only [hdd, Complex.add_re, Complex.sub_re]
      linarith
    rw [levi_congr hev w]
    exact levi_re_analytic hH w
  have hlevi : ∀ z ∈ Metric.ball (ψ x) r, ∀ w, levi d z w = 0 := by
    intro z hz w
    by_contra hne
    have hcw := continuousOn_levi_of_contDiffOn' d (ψ x) r w hd2
    have hca : ContinuousAt (fun v => levi d v w) z := hcw.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    have hM : (fun v => levi d v w) ⁻¹' {b | b ≠ 0} ∩ Metric.ball (ψ x) r ∈ 𝓝 z :=
      Filter.inter_mem (hca.preimage_mem_nhds (isOpen_ne.mem_nhds hne)) (Metric.isOpen_ball.mem_nhds hz)
    obtain ⟨M, hMsub, hMo, hzM⟩ := mem_nhds_iff.mp hM
    have hzt : z ∈ ψ.target := (hball (hMsub hzM).2).1
    have hne2 : (ψ.source ∩ ψ ⁻¹' M).Nonempty := by
      refine ⟨ψ.symm z, ψ.map_target hzt, ?_⟩
      show ψ (ψ.symm z) ∈ M
      rw [ψ.right_inv hzt]
      exact hzM
    obtain ⟨u, ⟨hus, huM⟩, huU⟩ := hUd.inter_open_nonempty _ (ψ.isOpen_inter_preimage hMo) hne2
    have hvM := hMsub huM
    apply hvM.1
    apply hzero (ψ u) (hball hvM.2)
    rw [ψ.left_inv hus]
    exact huU
  obtain ⟨G0, hG0an, hG0eq⟩ := exists_re_of_levi_zero hr hd2 hlevi
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) r, ψ.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hxj, Metric.mem_ball_self hr⟩, fun y => G0 (ψ y), ?_, ?_⟩
  · exact holoOn_of_compat (isCompatChart_chart A j) Set.inter_subset_left (fun y hy => hG0an _ hy.2)
  · intro y hy
    have h := hG0eq (ψ y) hy.2
    simp only [hdd, ψ.left_inv hy.1] at h
    exact h

end PositivityTheory.UnitarySelfGeneration
