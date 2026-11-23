import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.LeftTranslateSet
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjTrInnerPure
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SchurRelationAddSecond
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjDensUpper

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem pj_schurS (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : SchurS X :=
  pj_dens (muInf X) X.σs (pj_tensRep X hX).2.2.1
    (fun x y => (continuous_const.inner ((pj_tensRep X hX).2.2.2 x)).aestronglyMeasurable)
    (Submodule.span ℂ (Set.range X.tens)) hX.2.1.2.2.1.2.2 (fdegAll X.I X.σ X.w) (pj_fdegAll_pos D h1 X hX)
    (pj_schur_span D h1 X hX)

theorem projection_and_count_facts (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hph : Integrable (phOf X.I X.σ X.w) (muInf X)) (hR : RepA X) (hUm : UnimodF X) :
    X.ProjStep ∧ X.CountedStep :=
  pj_main D h1 X hX hph hR hUm (pj_sepF X hX) (pj_tensRep X hX) (pj_schurS D h1 X hX)

def StepsB' (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → RepA X ∧ UnimodF X ∧ X.CuspStep

theorem integrable_one_place_of_local (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) : MatrixCoefficientIntegrable D :=
  fun n ε lam hlam H _ _ _ σ hDS w hw h hg hh => (hloc n ε lam hlam H σ hDS w hw h hg hh).1

end Formalism.MainNotions.LeviCoordinates

end
