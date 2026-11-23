import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

namespace GlobalTheory.HCF.ReproSpan

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_zero' (g : GA E a) (x : Lie E a) : chart (0 : GA E a → ℂ) g x = 0 := by
  unfold chart; split_ifs <;> rfl

theorem chart_add' (φ ψ : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (φ + ψ) g x = chart φ g x + chart ψ g x := by
  unfold chart; split_ifs <;> simp

theorem chart_smul' (c : ℂ) (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (c • φ) g x = c * chart φ g x := by
  unfold chart; split_ifs <;> simp

theorem integrable_chart_mul (ψ : Sm E a) (g : GA E a) (β : Lie E a → ℂ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ invSet E a) :
    MeasureTheory.Integrable (fun x => chart ψ.1 g x * β x) := by
  have hcont : Continuous (fun x => chart ψ.1 g x * β x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ invSet E a
    · exact (contDiffAt_chart ψ.2 g hx).continuousAt.mul hβ.continuousAt
    · have hxt : x ∉ tsupport β := fun h => hx (hs h)
      have hev : (fun x => chart ψ.1 g x * β x) =ᶠ[𝓝 x] fun _ => 0 := by
        have h0 : β =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
        filter_upwards [h0] with y hy
        simp [hy]
      exact (continuousAt_congr hev).mpr continuousAt_const
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Lie E a)) :=
    MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts _
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hc)

end GlobalTheory.HCF.ReproSpan

open GlobalTheory.HCF.ReproSpan in

theorem GlobalTheory.HCF.repro_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W X N β hβ hc hs hform φ hφ
  have hβc : Continuous β := hβ.continuous
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hform x hx
  | zero =>
    intro g
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
    simp [chart_zero']
  | add x y _ _ hx hy =>
    intro g
    have e : (fun z => chart (x + y).1 g z * β z) =
        fun z => chart x.1 g z * β z + chart y.1 g z * β z := by
      funext z
      rw [Submodule.coe_add, chart_add', add_mul]
    rw [e, MeasureTheory.integral_add (integrable_chart_mul x g β hβc hc hs)
      (integrable_chart_mul y g β hβc hc hs), hx g, hy g]
    rfl
  | smul c x _ hx =>
    intro g
    have e : (fun z => chart (c • x).1 g z * β z) = fun z => c * (chart x.1 g z * β z) := by
      funext z
      rw [Submodule.coe_smul, chart_smul', mul_assoc]
    rw [e, MeasureTheory.integral_const_mul, hx g]
    rfl
