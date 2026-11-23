import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassPos
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotDens
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveDegreeVert
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

theorem ProjPotMassPos.isPotential_congr {e : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas e X} {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by
  obtain ⟨hs, hd⟩ := hP
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have h := hs x j
    rw [hU x] at h
    refine h.congr fun w hw => ?_
    simp only [Function.comp_apply]
    exact (hφ x _ ((hU x).symm ▸ hw.2)).symm
  · rw [← hU x, ← hU x'] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hd x x' y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    rw [← hU x, ← hU x'] at hz
    rw [← hφ x z hz.1.2, ← hφ x' z hz.2]
    exact hGe z hz

theorem ProjPotMassPos.isPotential_multiprojPot {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val) :
    IsPotential BV (multiprojPot R V) := by
  let L : HermLine ι := CurveDegreeVert.fsLine (fun _ : K => 2)
  have hL : L.h = fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ ((2 : ℕ) : ℤ) := by
    funext z
    simp only [L, CurveDegreeVert.fsLine, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]
  have h1 := isPotentialPullback R.A BV Subtype.val hH (potOf R L)
    (isPotential_potOf R (CurveDegreeVert.isSmoothHerm_fsLine _))
  refine ProjPotMassPos.isPotential_congr (P := (potOf R L).pullback Subtype.val hH.1) (fun _ => rfl) (fun y z hz => ?_) h1
  have hm := (R.mem y.1 z.1 hz).1
  show Real.log (L.h (R.lift y.1 z.1)) = ∑ k, Real.log (∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)
  have hpos : ∀ k, 0 < ∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hm k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun i => ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ i))
  rw [hL]
  simp only [zpow_natCast, Real.sq_sqrt (hpos _).le]
  exact Real.log_prod (fun k _ => (hpos k).ne')

theorem ProjPotMassPos.of_found (hD : ProjPotDens.Statement) : ProjPotMassPos.Statement := by
  intro K _ ι _ P J n R V BV hH hV C hC hCF
  obtain ⟨x, hxC, hxF⟩ := hCF
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have hPot : ∀ _ : Fin n, IsPotential BV (multiprojPot R V) := fun _ =>
    ProjPotMassPos.isPotential_multiprojPot hH
  have hCont := locDensCont BV (fun _ => multiprojPot R V) hPot
  have hDs := hD K ι P J n R V BV hH
  have hMI : MIntegrable BV (fun _ => multiprojPot R V) (C.indicator fun _ => (1 : ℝ)) := by
    intro i Kc hK hKc
    have hS : IsOpen ((BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C) :=
      (BV.chart i).isOpen_inter_preimage_symm hC
    refine IntegrableOn.congr_fun ((((hCont i).mono hK).integrableOn_compact hKc).indicator
      hS.measurableSet) (fun y hy => ?_) hKc.measurableSet
    by_cases hyC : (BV.chart i).symm y ∈ C
    · rw [Set.indicator_of_mem (show y ∈ (BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C from
        ⟨hK hy, hyC⟩), Set.indicator_of_mem hyC, one_mul]
    · rw [Set.indicator_of_notMem (show y ∉ (BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C from
        fun h => hyC h.2), Set.indicator_of_notMem hyC, zero_mul]
  have hPn : Nonempty (ChartPartition BV) := existsPartition BV
  unfold mInt
  rw [dif_pos hPn]
  unfold integralWith
  set χ := hPn.some
  have hnn : ∀ i, ∀ y ∈ (BV.chart i).target, 0 ≤ χ.χ i ((BV.chart i).symm y) *
      C.indicator (fun _ => (1 : ℝ)) ((BV.chart i).symm y) *
        locDens BV (fun _ => multiprojPot R V) i y := fun i y hy =>
    mul_nonneg (mul_nonneg (χ.nonneg i _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      (hDs i y hy).1
  obtain ⟨j, hj⟩ : ∃ j, 0 < χ.χ j x := by
    by_contra h
    push Not at h
    have h1 := χ.sum_eq_one x
    have h2 : ∑ j, χ.χ j x ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith
  refine Finset.sum_pos' (fun i _ => setIntegral_nonneg (BV.chart i).open_target.measurableSet
    (hnn i)) ⟨j, Finset.mem_univ _, ?_⟩
  have hxj : x ∈ (BV.chart j).source := χ.tsupport_subset j (subset_tsupport _ hj.ne')
  set u := BV.chart j x
  have hut : u ∈ (BV.chart j).target := (BV.chart j).map_source hxj
  have hsu : (BV.chart j).symm u = x := (BV.chart j).left_inv hxj
  have hχc : ContinuousAt (fun y => χ.χ j ((BV.chart j).symm y)) u := by
    have h := (χ.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt ((BV.chart j).open_target.mem_nhds hut)
  have hev : ∀ᶠ y in 𝓝 u, y ∈ (BV.chart j).target ∧ 0 < χ.χ j ((BV.chart j).symm y) *
      C.indicator (fun _ => (1 : ℝ)) ((BV.chart j).symm y) *
        locDens BV (fun _ => multiprojPot R V) j y := by
    have hC' : ∀ᶠ y in 𝓝 u, (BV.chart j).symm y ∈ C :=
      ((BV.chart j).continuousAt_symm hut).preimage_mem_nhds (by rw [hsu]; exact hC.mem_nhds hxC)
    have hD' : ∀ᶠ y in 𝓝 u, 0 < locDens BV (fun _ => multiprojPot R V) j y :=
      ((hCont j).continuousAt ((BV.chart j).open_target.mem_nhds hut)).eventually
        (lt_mem_nhds ((hDs j u hut).2 (by rw [hsu]; exact hxF)))
    have hχ' : ∀ᶠ y in 𝓝 u, 0 < χ.χ j ((BV.chart j).symm y) :=
      hχc.eventually (lt_mem_nhds (show 0 < χ.χ j ((BV.chart j).symm u) by rw [hsu]; exact hj))
    filter_upwards [(BV.chart j).open_target.mem_nhds hut, hC', hD', hχ'] with y h1 h2 h3 h4
    refine ⟨h1, mul_pos (mul_pos h4 ?_) h3⟩
    rw [Set.indicator_of_mem h2]
    exact one_pos
  obtain ⟨W, hWs, hWo, huW⟩ := mem_nhds_iff.mp hev
  have hint := integrableOn_weight BV χ (fun _ => multiprojPot R V) _ hMI j
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem (BV.chart j).open_target.measurableSet (hnn j)) hint]
  refine lt_of_lt_of_le (hWo.measure_pos volume ⟨u, huW⟩) (measure_mono fun y hy => ?_)
  exact ⟨(hWs hy).2.ne', (hWs hy).1⟩

end GroundTheory.Heights₂.Heights.Targets
