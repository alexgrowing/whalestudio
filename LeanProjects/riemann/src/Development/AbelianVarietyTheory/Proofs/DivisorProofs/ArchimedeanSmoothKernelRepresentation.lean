import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open Classical MeasureTheory NumberField Topology

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def unitOrOne (x : Lie E a) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (Matrix.of x) then h.unit else 1

theorem unitOrOne_val (x : Lie E a) :
    (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) = (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) x := by
  by_cases hx : x ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hx, unitOrOne, dif_pos (show IsUnit (Matrix.of x) from hx)]; rfl
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, unitOrOne, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]; rfl

theorem measurable_unitOrOne : Measurable fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) := by
  have e : (fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E))) =
      (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) := funext unitOrOne_val
  rw [e]
  exact Measurable.piecewise isOpen_invSet.measurableSet measurable_id measurable_const

theorem continuousAt_height_unitOrOne {x : Lie E a} (hx : x ∈ invSet E a) :
    ContinuousAt (fun y : Lie E a => height (unitOrOne y)) x := by
  have hev : (fun y : Lie E a => height (unitOrOne y)) =ᶠ[𝓝 x]
      fun y => 1 + ‖y‖ + ‖toL ((Matrix.of y)⁻¹)‖ := by
    filter_upwards [isOpen_invSet.mem_nhds hx] with y hy
    have h1 : ((unitOrOne y : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = Matrix.of y := by
      rw [unitOrOne, dif_pos (show IsUnit (Matrix.of y) from hy)]; rfl
    have h2 : (((unitOrOne y)⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = (Matrix.of y)⁻¹ := by
      rw [Matrix.coe_units_inv, h1]
    simp only [height, h1, h2]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  have hinv : ContinuousAt (fun y : Matrix (Fin a) (Fin a) (Cinf E) => y⁻¹) (Matrix.of x) := by
    refine continuousAt_matrix_inv _ ?_
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    rw [← hu.unit_spec]
    exact NormedRing.inverse_continuousAt hu.unit
  exact (continuousAt_const.add continuousAt_id.norm).add (hinv.comp (f := fun y : Lie E a => Matrix.of y)
    continuousAt_id).norm

theorem IsTestInf.isRapidInf {f : Lie E a → ℂ} (hf : IsTestInf f) :
    IsRapidInf (volume : Measure (Lie E a)) f unitOrOne := by
  refine ⟨hf.1.continuous.measurable, measurable_unitOrOne, fun N => ?_⟩
  have hc : Continuous fun x => ‖f x‖ * height (unitOrOne x) ^ N := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport f
    · exact hf.1.continuous.continuousAt.norm.mul ((continuousAt_height_unitOrOne (hf.2.2 hx)).pow N)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
  have hs : HasCompactSupport fun x => ‖f x‖ * height (unitOrOne x) ^ N :=
    hf.2.1.norm.mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem isRapidInf_and_smoothInf_eq_kerInf :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : Lie E a → ℂ), IsTestInf f →
      IsRapidInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) ∧
      ∀ F : GA E a → ℂ, smoothInf f F = kerInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) F := by
  intro E _ _ _ a f hf
  refine ⟨hf.isRapidInf, fun F => funext fun g => ?_⟩
  simp only [smoothInf, kerInf]
  congr 1
  funext x
  by_cases hx : IsUnit (Matrix.of x)
  · rw [chart, dif_pos hx, dif_pos hx]
  · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2.2 h)
    simp [h0]

end GlobalTheory.JSW
