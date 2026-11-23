import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MainThm
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

open scoped Pointwise

namespace GlobalTheory

theorem integral_biInvariant_hasSum_doubleCoset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (m : Measure G) [m.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) →
  ∀ (ι : Type) [Countable ι] (x : ι → G),
    Pairwise (Function.onFun Disjoint fun i => DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
  ∀ F : G → ℂ, (∀ g, ∀ j ∈ J, ∀ j' ∈ J, F (j * g * j') = F g) →
    (∀ g, F g ≠ 0 → ∃ i, g ∈ DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
    Summable (fun i => m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) * ‖F (x i)‖) →
    Integrable F m ∧
    HasSum (fun i => (m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) : ℂ) * F (x i)) (∫ g, F g ∂m) ∧
    HasSum (fun c : DoubleCoset.Quotient (J : Set G) (J : Set G) =>
      (m.real (DoubleCoset.doubleCoset c.out (J : Set G) (J : Set G)) : ℂ) * F c.out) (∫ g, F g ∂m) := by
  first
  | exact @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | (apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm ..)

end GlobalTheory
