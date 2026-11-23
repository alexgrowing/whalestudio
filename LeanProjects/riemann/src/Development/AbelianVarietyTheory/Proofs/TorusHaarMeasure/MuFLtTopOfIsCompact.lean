import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatFin

open GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem muF_lt_top_of_isCompact {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {K : Set (V (nd X))}
    (hK : IsCompact K) (hKO : K ⊆ OmF X x0) : muF X x0 K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image (OntoB.densF_continuousOn.mono hKO)
  unfold muF
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (densF X x0 z) ∂(volume.restrict (OmF X x0))
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(volume.restrict (OmF X x0)) :=
        setLIntegral_mono' hK.measurableSet fun z hz =>
          ENNReal.ofReal_le_ofReal (hM ⟨z, hz, rfl⟩)
    _ = ENNReal.ofReal M * (volume.restrict (OmF X x0)) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)

theorem muF_borSat_eq (hI : MeasInvStatement (E := E)) {r : ℕ} (X : Data E r)
    {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1) {C : Set (Frame X.Ψ r)}
    (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (cpt X x0 ⁻¹' borSat X C) = muF X x1 (cpt X x1 ⁻¹' borSat X C) := by
  have hS := measurableSet_borSat X hK hC
  have h := hI r X x0 x1 h0 h1 ((borSat X C).indicator 1) (measurable_one.indicator hS) (by
    intro x _ b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS)]
      rfl
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x0).measurable hS),
    ← lintegral_indicator_one ((FundSetPf.cont_cpt X x1).measurable hS)]
  exact h

theorem muF_sat_lt_top (hI : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (C : Set (Frame X.Ψ r)) (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (sat X x0 C) < ⊤ := by
  rw [sat_eq_preimage X x0 hC]
  refine hK.induction_on (p := fun s => muF X x0 (cpt X x0 ⁻¹' borSat X s) < ⊤) ?_ ?_ ?_ ?_
  · have : borSat X (∅ : Set (Frame X.Ψ r)) = ∅ := by
      ext y; simp [borSat]
    simp [this]
  · intro s t hst ht
    refine (measure_mono fun z hz => ?_).trans_lt ht
    obtain ⟨x, hx, h⟩ := hz
    exact ⟨x, hst hx, h⟩
  · intro s t hs ht
    refine (measure_mono (t := cpt X x0 ⁻¹' borSat X s ∪ cpt X x0 ⁻¹' borSat X t)
      fun z hz => ?_).trans_lt (measure_union_lt_top hs ht)
    obtain ⟨x, hx | hx, h⟩ := hz
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · intro x hx
    have hxd := hC hx
    obtain ⟨x1, hx1, b1, hb1, hxe⟩ := ortho_holds r X x hxd
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, huniq⟩ := lu_holds r X x1 hx1
    have h0 := IW.zero_mem_OmF X x1 hx1
    obtain ⟨u1, u2, -⟩ := huniq 0 h0 b1 hb1
    rw [IW.cpt_zero, ← hxe] at u1 u2
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((OntoB.isOpen_OmF X x1).mem_nhds h0)
    have hW : {y | y ∈ X.dom ∧ Δ y ≠ 0} ∈ 𝓝 x :=
      ((FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)).mem_nhds
        ⟨hxd, u1⟩
    have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt hW
    have hV : zOf ⁻¹' Metric.closedBall 0 ρ ∈ 𝓝 x :=
      hzc.preimage_mem_nhds (by rw [u2]; exact Metric.closedBall_mem_nhds _ hρ)
    refine ⟨{y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ,
      mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hW hV), ?_⟩
    have hKc : IsCompact (cpt X x1 '' Metric.closedBall 0 ρ) :=
      (isCompact_closedBall _ _).image (FundSetPf.cont_cpt X x1)
    have hKd : cpt X x1 '' Metric.closedBall 0 ρ ⊆ X.dom := by
      rintro _ ⟨z, hz, rfl⟩
      exact hball hz
    calc muF X x0 (cpt X x0 ⁻¹' borSat X
          ({y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ))
        ≤ muF X x0 (cpt X x0 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨y, ⟨⟨hyd, hyΔ⟩, hyz⟩, b, hb, h⟩ := hz
          obtain ⟨-, hb', hy⟩ := hdec y hyd hyΔ
          refine ⟨_, ⟨zOf y, hyz, rfl⟩, rmul (bOf y) b, ExtFPf.mul_mem X hb' hb, ?_⟩
          rw [← ExtFPf.rmul_assoc, ← hy, h]
      _ = muF X x1 (cpt X x1 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) :=
          muF_borSat_eq hI X hx0 hx1 hKc hKd
      _ ≤ muF X x1 (Metric.closedBall 0 ρ) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨_, ⟨z', hz', rfl⟩, b, hb, h⟩ := hz
          rw [← ExtFPf.rmul_oneF X (cpt X x1 z)] at h
          rwa [FundSetPf.cpt_uniq X hx1 (ExtFPf.oneF_mem X) hb h]
      _ < ⊤ := muF_lt_top_of_isCompact X x1 (isCompact_closedBall _ _) hball

end GlobalTheory.SatFin
