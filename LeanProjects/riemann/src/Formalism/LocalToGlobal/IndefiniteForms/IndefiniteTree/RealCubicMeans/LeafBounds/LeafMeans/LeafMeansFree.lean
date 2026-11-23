import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive

noncomputable section

open NumberField
open IsDedekindDomain
open Finset
open Formalism.DivisionValues
open Formalism.L2.Indef
open Formalism.L2.Indef.Tree

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

def SlopeMeansBounds {ι : Type} [Fintype ι] (X : ℝ) (sl : ι → ℝ) (T LL0 U E0 cc Qcc Ca Cb : ℝ) : Prop :=
  0 ≤ X ∧ -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) ∧ T * X ≤ Ca * LL0 * (U + E0) ∧ T * cc ≤ Cb * LL0 * (U + E0) + T * Qcc

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
