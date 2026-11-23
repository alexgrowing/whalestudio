import Mathlib
import GroundTheory.AutomorphicForms.TraceFormulaCentralizer

open MeasureTheory Topology Filter Set Function
open scoped ENNReal NNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Unimodular

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [LocallyCompactSpace H] [T2Space H] in

theorem isFundamentalDomain_preimage_mul_right (L : Subgroup H) [DiscreteTopology L]
    (ν : Measure H) (g : H) :
    IsFundamentalDomain L ((· * g) ⁻¹' fundamentalDomain L) ν := by
  refine IsFundamentalDomain.mk' ((measurableSet_fundamentalDomain L).preimage
    (measurable_mul_const g)).nullMeasurableSet fun h => ?_
  obtain ⟨l, hl, hlu⟩ := existsUnique_smul_mem_fundamentalDomain L (h * g)
  refine ⟨l, ?_, fun l' hl' => hlu l' ?_⟩
  · show (l • h) * g ∈ fundamentalDomain L
    rw [smul_mul_assoc]
    exact hl
  · have hl'' : (l' • h) * g ∈ fundamentalDomain L := hl'
    rw [smul_mul_assoc] at hl''
    exact hl''

theorem isMulRightInvariant_of_compactSpace (L : Subgroup H) [DiscreteTopology L]
    [CompactSpace (RightCosetSpace L)] (ν : Measure H) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  constructor
  intro g
  have hD := isFundamentalDomain_fundamentalDomain L ν
  have h0 : ν (fundamentalDomain L) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have htop : ν (fundamentalDomain L) ≠ ∞ := by
    rw [← quotientMeasure_univ ν hD]
    exact measure_ne_top _ _
  set c : ℝ≥0 := Measure.haarScalarFactor (Measure.map (· * g) ν) ν
  have hc : Measure.map (· * g) ν = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : Measure.map (· * g) ν (fundamentalDomain L) = ν (fundamentalDomain L) := by
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain L)]
    exact (isFundamentalDomain_preimage_mul_right L ν g).measure_eq hD
  have hc1 : c = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have : (c : ℝ≥0∞) * ν (fundamentalDomain L) = 1 * ν (fundamentalDomain L) := by
      rw [h2, one_mul]
    rwa [ENNReal.mul_left_inj h0 htop, ENNReal.coe_eq_one] at this
  rw [hc, hc1, one_smul]

omit [T2Space H] in

theorem inv_eq_self_of_isMulRightInvariant (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.inv = ν := by
  set c : ℝ≥0 := Measure.haarScalarFactor ν.inv ν
  have hc : ν.inv = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv ν) = (c ^ 2 : ℝ≥0) • ν := by
    rw [← Measure.inv_def ν, hc, Measure.map_smul, ← Measure.inv_def ν, hc, smul_smul, pow_two]
  have hν : ν = (c ^ 2 : ℝ≥0) • ν := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have h3 : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * ν K = 1 * ν K := by
    conv_rhs => rw [hν]
    simp
  have h4 : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj ((isOpen_interior.measure_pos ν K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
      K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

end Unimodular

section Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]

theorem isMulRightInvariant_centralizer (γ : Γ)
    (ν : Measure (Subgroup.centralizer {(γ : G)})) [ν.IsHaarMeasure] : ν.IsMulRightInvariant :=
  have := compactSpace_centralizerLattice Γ γ
  isMulRightInvariant_of_compactSpace (centralizerLattice Γ (γ : G)) ν

theorem quotientMeasure_centralizerLattice_univ_ne_zero_ne_top (γ : Γ)
    (ν : Measure (Subgroup.centralizer {(γ : G)})) [ν.IsHaarMeasure] :
    quotientMeasure (centralizerLattice Γ (γ : G)) ν univ ≠ 0 ∧
      quotientMeasure (centralizerLattice Γ (γ : G)) ν univ ≠ ∞ := by
  have := compactSpace_centralizerLattice Γ γ
  have hD := isFundamentalDomain_fundamentalDomain (centralizerLattice Γ (γ : G)) ν
  refine ⟨?_, measure_ne_top _ _⟩
  rw [quotientMeasure_univ ν hD]
  exact hD.measure_ne_zero (NeZero.ne ν)

def weilMeasure (μ : Measure G) (γ : Γ) (ν : Measure (Subgroup.centralizer {(γ : G)})) :
    Measure (RightCosetSpace (Subgroup.centralizer {(γ : G)})) :=
  (quotientMeasure (centralizerLattice Γ (γ : G)) ν univ)⁻¹ •
    Measure.map (mapOfLe (centralizerIn_le_centralizer Γ γ))
      (quotientMeasure (centralizerIn Γ γ) μ)

theorem isWeilMeasure_weilMeasure (μ : Measure G) [μ.IsHaarMeasure] (γ : Γ)
    (ν : Measure (Subgroup.centralizer {(γ : G)})) [ν.IsHaarMeasure] :
    IsWeilMeasure (Subgroup.centralizer {(γ : G)}) μ ν (weilMeasure Γ μ γ ν) := by
  intro φ F hφ hF
  have := isMulRightInvariant_centralizer Γ γ ν
  have hinv := inv_eq_self_of_isMulRightInvariant ν
  obtain ⟨hv0, hvtop⟩ := quotientMeasure_centralizerLattice_univ_ne_zero_ne_top Γ γ ν
  set vol := quotientMeasure (centralizerLattice Γ (γ : G)) ν univ with hvol
  set E := fundamentalDomain (centralizerIn Γ (γ : G)) with hE
  have hEm : MeasurableSet E := measurableSet_fundamentalDomain _
  have hm2 : Measurable fun p : G × Subgroup.centralizer {(γ : G)} => φ ((p.2 : G) * p.1) :=
    hφ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  have hFm : Measurable F := by
    refine measurable_from_quotient.2 ?_
    have : F ∘ Quotient.mk'' = fun x => ∫⁻ h, φ ((h : G) * x) ∂ν := funext hF
    rw [this]
    exact hm2.lintegral_prod_right'

  have hS : ∀ y : G, ν {h : Subgroup.centralizer {(γ : G)} | (h : G)⁻¹ * y ∈ E} = vol := by
    intro y
    have h1 : {h : Subgroup.centralizer {(γ : G)} | (h : G)⁻¹ * y ∈ E} =
        {k : Subgroup.centralizer {(γ : G)} | (k : G) * y ∈ E}⁻¹ := by
      ext h
      simp
    rw [h1, ← Measure.inv_apply, hinv]
    exact (quotientMeasure_univ ν (isFundamentalDomain_centralizerLattice Γ (γ : G) ν y)).symm
  rw [weilMeasure, lintegral_smul_measure, lintegral_map hFm (measurable_mapOfLe _),
    lintegral_quotientMeasure]
  simp only [mapOfLe_mk, hF]
  rw [← hvol, ← hE]
  rw [smul_eq_mul, lintegral_lintegral_swap
    (f := fun (g : G) (h : Subgroup.centralizer {(γ : G)}) => φ ((h : G) * g)) hm2.aemeasurable]
  have key : ∀ h : Subgroup.centralizer {(γ : G)},
      ∫⁻ x in E, φ ((h : G) * x) ∂μ = ∫⁻ y, E.indicator 1 ((h : G)⁻¹ * y) * φ y ∂μ := by
    intro h
    rw [← lintegral_indicator hEm,
      ← lintegral_mul_left_eq_self (fun y => E.indicator 1 ((h : G)⁻¹ * y) * φ y) (h : G)]
    refine lintegral_congr fun x => ?_
    show E.indicator (fun x => φ ((h : G) * x)) x =
      E.indicator 1 ((h : G)⁻¹ * ((h : G) * x)) * φ ((h : G) * x)
    rw [inv_mul_cancel_left]
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp_rw [key]
  have hm3 : Measurable fun p : Subgroup.centralizer {(γ : G)} × G =>
      E.indicator 1 ((p.1 : G)⁻¹ * p.2) * φ p.2 :=
    ((measurable_one.indicator hEm).comp
      (((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd).measurable)).mul
      (hφ.comp measurable_snd)
  rw [lintegral_lintegral_swap hm3.aemeasurable]
  have inner : ∀ y : G, ∫⁻ h : Subgroup.centralizer {(γ : G)},
      E.indicator 1 ((h : G)⁻¹ * y) * φ y ∂ν = vol * φ y := by
    intro y
    have hmy : Measurable fun h : Subgroup.centralizer {(γ : G)} =>
        E.indicator (1 : G → ℝ≥0∞) ((h : G)⁻¹ * y) :=
      (measurable_one.indicator hEm).comp
        ((continuous_subtype_val.inv.mul continuous_const).measurable)
    rw [lintegral_mul_const _ hmy]
    congr 1
    have : (fun h : Subgroup.centralizer {(γ : G)} => E.indicator (1 : G → ℝ≥0∞) ((h : G)⁻¹ * y)) =
        {h : Subgroup.centralizer {(γ : G)} | (h : G)⁻¹ * y ∈ E}.indicator 1 := by
      funext h
      by_cases hh : (h : G)⁻¹ * y ∈ E
      · simp [hh]
      · simp [hh]
    have hSm : MeasurableSet {h : Subgroup.centralizer {(γ : G)} | (h : G)⁻¹ * y ∈ E} :=
      hEm.preimage (continuous_subtype_val.inv.mul continuous_const).measurable
    rw [this, lintegral_indicator_one hSm, hS y]
  simp_rw [inner]
  rw [lintegral_const_mul _ hφ, ← mul_assoc, ENNReal.inv_mul_cancel hv0 hvtop, one_mul]

theorem exists_isWeilMeasure (μ : Measure G) [μ.IsHaarMeasure] (γ : Γ)
    (ν : Measure (Subgroup.centralizer {(γ : G)})) [ν.IsHaarMeasure] :
    ∃ ρ, IsWeilMeasure (Subgroup.centralizer {(γ : G)}) μ ν ρ :=
  ⟨_, isWeilMeasure_weilMeasure Γ μ γ ν⟩

end Weil

end RightCosetSpace

end

end GroundTheory.Automorphic
