import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem one_lt_top (ha : 0 < a) : 1 < detModule E a (splitCentre E a 1) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  change (1 : ℝ) < Real.exp _
  exact Real.one_lt_exp_iff.2 (by positivity)

private theorem band_zero : band E 0 = Set.univ := Set.eq_univ_of_forall fun _ => Or.inl rfl

private theorem band_pos (ha : 0 < a) :
    band E a = detModule E a ⁻¹' Set.Ico 1 (detModule E a (splitCentre E a 1)) := by
  ext g
  simp only [band, Set.mem_setOf_eq, ha.ne', false_or, Set.mem_preimage, Set.mem_Ico]

private theorem measurableSet_band : MeasurableSet (band E a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [band_zero]; exact MeasurableSet.univ
  · rw [band_pos ha]
    have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
      continuous_subtype_val.comp continuous_detModule
    exact hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))

private theorem meas_retract : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable

private theorem muOne_apply (μ : Measure (GA E a)) {A : Set (G1 E a)} (hA : MeasurableSet A) :
    muOne μ A = μ (retractOne ⁻¹' A ∩ band E a) := by
  rw [muOne, Measure.map_apply meas_retract hA, Measure.restrict_apply (meas_retract hA)]

omit [IsTotallyComplex E] in
private theorem retract_mul_left (x : G1 E a) (g : GA E a) :
    retractOne ((x : GA E a) * g) = x * retractOne g := by
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul,
    mul_assoc]

private theorem band_mul_left (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul]

private theorem isCompact_posIcc (s t : {r : ℝ // 0 < r}) : IsCompact (Set.Icc s t) := by
  refine Topology.IsInducing.subtypeVal.isCompact_iff.2 ?_
  convert isCompact_Icc (a := (s : ℝ)) (b := (t : ℝ)) using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, s.2.trans_le hx.1⟩, hx, rfl⟩

end

theorem UpperTheory.V.KernelIndexFullLattice.muHaar_holds :
    UpperTheory.V.KernelIndexFullLattice.MuHaar := by
  intro E _ _ _ a μ _
  have h1 : (muOne μ).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    have hm : Measurable fun y : G1 E a => x * y := measurable_const_mul x
    rw [Measure.map_apply hm hA, muOne_apply μ (hm hA), muOne_apply μ hA,
      ← measure_preimage_mul μ (x : GA E a) (retractOne ⁻¹' A ∩ band E a)]
    congr 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, retract_mul_left, band_mul_left]
  have h2 : IsFiniteMeasureOnCompacts (muOne μ) := by
    refine ⟨fun C hC => ?_⟩
    rw [muOne_apply μ hC.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      exact (Set.toFinite _).isCompact.measure_lt_top
    · have hc : Continuous fun p : G1 E a × {r : ℝ // 0 < r} => (p.1 : GA E a) * centralSection E a p.2 :=
        (continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd)
      refine lt_of_le_of_lt (measure_mono ?_)
        ((hC.prod (isCompact_posIcc 1 (detModule E a (splitCentre E a 1)))).image hc).measure_lt_top
      rintro g ⟨hg, hb⟩
      rw [band_pos ha] at hb
      refine ⟨(retractOne g, detModule E a g), ⟨hg, hb.1, hb.2.le⟩, ?_⟩
      change (retractOne g : GA E a) * centralSection E a (detModule E a g) = g
      rw [coe_retractOne, inv_mul_cancel_right]
  have h3 : (muOne μ).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨x, hx⟩ := hne
    have hO : IsOpen (retractOne ⁻¹' U : Set (GA E a)) := hU.preimage continuous_retractOne
    rw [muOne_apply μ hU.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      rw [band_zero, Set.inter_univ]
      refine hO.measure_ne_zero μ ⟨1, ?_⟩
      change retractOne _ ∈ U
      rwa [Subsingleton.elim (retractOne _) x]
    · obtain ⟨s, hs1, hs2⟩ : ∃ s : {r : ℝ // 0 < r}, 1 < s ∧ s < detModule E a (splitCentre E a 1) := by
        obtain ⟨s, h1, h2⟩ := exists_between (show (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) from one_lt_top ha)
        exact ⟨⟨s, one_pos.trans h1⟩, h1, h2⟩
      have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
        continuous_subtype_val.comp continuous_detModule
      have hI : IsOpen (detModule E a ⁻¹' Set.Ioo 1 (detModule E a (splitCentre E a 1)) : Set (GA E a)) :=
        (isOpen_Ioo (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ))).preimage hc
      have hd : detModule E a ((x : GA E a) * centralSection E a s) = s := by
        rw [map_mul, (mem_normOneGL_iff_detModule).1 x.2, detModule_centralSection ha, one_mul]
      have hr : retractOne ((x : GA E a) * centralSection E a s) = x := by
        ext1
        rw [coe_retractOne, hd, mul_inv_cancel_right]
      have hp := (hO.inter hI).measure_ne_zero μ ⟨(x : GA E a) * centralSection E a s, by
        rw [Set.mem_preimage, hr]; exact hx, by rw [Set.mem_preimage, hd]; exact ⟨hs1, hs2⟩⟩
      intro h0
      refine hp (measure_mono_null ?_ h0)
      rw [band_pos ha]
      exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.Ioo_subset_Ico_self)
  exact {}
