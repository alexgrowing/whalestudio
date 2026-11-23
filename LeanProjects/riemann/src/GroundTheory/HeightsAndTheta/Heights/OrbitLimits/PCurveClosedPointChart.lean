import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

noncomputable section

namespace CurveClosedPointChartAlt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k)

abbrev fld : IntermediateField ℚ Ω :=
  CoordinateConeArithVar.ratioField (SegreChart.segre y) (fun _ ↦ f)

def pt : (Σ _ : Unit, ∀ k, ι k) → fld y f :=
  CoordinateConeArithVar.ratioPtL (SegreChart.segre y) (fun _ ↦ f)

theorem coe_pt (q : Σ _ : Unit, ∀ k, ι k) :
    ((pt y f q : fld y f) : Ω) = SegreChart.segre y q / SegreChart.segre y ⟨(), f⟩ := rfl

variable {y f}

theorem numberField (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : NumberField (fld y f) := by
  have : Finite (coneRatios (SegreChart.segre y) fun _ ↦ f) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (fld y f) := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    exact (SegreChart.isAlgebraic_segre_ratio hP f hf g).isIntegral)
  exact {}

theorem isArithVar_pt (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    IsArithVar (mCoordIdeal (pt y f)) 1 := by
  rw [pt, CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ fun _ ↦ (SegreChart.segre_ne_zero_iff y f).mpr hf]
  exact SegreChart.isArithVar_segre hP f hf

theorem pt_ne_zero_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    pt y f ⟨(), g⟩ ≠ 0 ↔ ∀ k, y ⟨k, g k⟩ ≠ 0 := by
  rw [← SegreChart.segre_ne_zero_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, coe_pt, div_eq_zero_iff, not_or,
    and_iff_left ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem coe_pt_ratio (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g h : ∀ k, ι k) :
    ((pt y f ⟨(), h⟩ / pt y f ⟨(), g⟩ : fld y f) : Ω) =
      SegreChart.segre y ⟨(), h⟩ / SegreChart.segre y ⟨(), g⟩ := by
  rw [IntermediateField.coe_div, coe_pt, coe_pt,
    div_div_div_cancel_right₀ ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem map_chartRingZ (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0) :
    (chartRingZ (pt y f) (fun _ ↦ g)).map (algebraMap (fld y f) Ω).toIntAlgHom = chartRingZ y g := by
  rw [chartRingZ, ← Algebra.adjoin_image, ← Set.range_comp, ← SegreChart.chartRingZ_segre y g hg, chartRingZ]
  congr 2
  funext q
  obtain ⟨⟨⟩, h⟩ := q
  exact coe_pt_ratio hf g h

theorem mem_chartRingZ_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0)
    (x : fld y f) : x ∈ chartRingZ (pt y f) (fun _ ↦ g) ↔ (x : Ω) ∈ chartRingZ y g := by
  rw [← map_chartRingZ hf g hg, Subalgebra.mem_map]
  refine ⟨fun h ↦ ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨x', hx', he⟩
  rwa [show x' = x from Subtype.ext he] at hx'

theorem mem_curveRing_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (x : fld y f) :
    x ∈ curveRing (pt y f) ↔ (x : Ω) ∈ curveRing y := by
  rw [mem_curveRing, mem_curveRing]
  refine ⟨fun h g hg ↦ (mem_chartRingZ_iff hf g hg x).1 (h _ fun _ ↦ (pt_ne_zero_iff hf g).2 hg),
    fun h c hc ↦ ?_⟩
  have hc' := (pt_ne_zero_iff hf (c ())).1 (hc ())
  exact (mem_chartRingZ_iff hf (c ()) hc' x).2 (h _ hc')

theorem exists_of_mem_curveRing (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) {b : Ω} (hb : b ∈ curveRing y) :
    ∃ x : fld y f, (x : Ω) = b := by
  have h := mem_curveRing.mp hb f hf
  rw [← map_chartRingZ hf f hf, Subalgebra.mem_map] at h
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x, hx⟩

end CurveClosedPointChartAlt

open CurveClosedPointChartAlt in

theorem CurveClosedPointChart.proof : CurveClosedPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y hP m hm
  have := SegreChart.charZero_of_isArithVar hP
  obtain ⟨f, hf⟩ := SegreChart.exists_chart hP
  have := numberField hP hf
  let φ : curveRing (pt y f) →+* curveRing y :=
    RingHom.codRestrict ((algebraMap (fld y f) Ω).comp (curveRing (pt y f)).subtype) (curveRing y)
      fun x ↦ (mem_curveRing_iff hf x).1 x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := exists_of_mem_curveRing hf hb
    exact ⟨⟨x, (mem_curveRing_iff hf x).2 hb⟩, rfl⟩
  have hm' : (m.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  obtain ⟨t, ht, hrat⟩ := ClosedPointChart.proof ClosedPointUnitSection.proof (∀ k, ι k) (fld y f) (pt y f)
    (isArithVar_pt hP hf) (m.comap φ) hm'
  have hyt := (pt_ne_zero_iff hf t).1 ht
  refine ⟨t, hyt, fun p ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := hrat (Function.update t p.1 p.2)
  refine ⟨φ a, φ b, hb, ?_⟩
  have h1 := congrArg (fun x : fld y f ↦ (x : Ω)) hab
  simp only [IntermediateField.coe_mul] at h1
  rw [coe_pt_ratio hf, SegreChart.segre_ratio, SegreChart.prod_ratio_update y t hyt p] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.Targets
