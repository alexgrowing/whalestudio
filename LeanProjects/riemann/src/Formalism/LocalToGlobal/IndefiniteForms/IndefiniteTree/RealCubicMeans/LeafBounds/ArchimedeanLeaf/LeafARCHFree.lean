import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive

noncomputable section

open NumberField
open IsDedekindDomain
open Finset
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef htMap)
open Formalism.DivisionValues
open Formalism.L2.Indef
open Formalism.L2.Indef.Tree

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

def ArchimedeanHeightBound {K : Type} [Field K] [NumberField K] {ι : Type} (zA zA' : ι → K) (B : ℝ) : Prop :=
  ∀ ij, meanInf K (fun v => Real.posLog ‖v.embedding (zA ij)‖) ≤ B ∧
    meanInf K (fun v => Real.posLog ‖v.embedding (zA' ij)‖) ≤ B

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
