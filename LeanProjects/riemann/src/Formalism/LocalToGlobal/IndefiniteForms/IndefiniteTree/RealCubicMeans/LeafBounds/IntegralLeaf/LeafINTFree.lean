import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive

noncomputable section

open NumberField
open IsDedekindDomain
open Finset
open Formalism.PairingDivisionLocalBalance (wt HtLe meanInf)
open Formalism.HN (muMaxDef htMap)
open Formalism.DivisionValues
open Formalism.L2.Indef
open Formalism.L2.Indef.Tree

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

def NonArchimedeanDefectBound {K : Type} [Field K] [NumberField K] {ι : Type} (dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ) (zA zA' : ι → K) (B : ℝ) : Prop :=
  (∀ w, 0 ≤ dl w) ∧ (∀ F : Finset (Formalism.PairingDivisionLocalBalance.Pl K), ∑ w ∈ F, lw w * dl w ≤ B) ∧
    ∀ ij, zA ij ≠ 0 ∧ zA' ij ≠ 0 ∧
      ∀ w, -(3 * dl w) ≤ (vw w (zA ij) : ℝ) ∧ -(3 * dl w) ≤ (vw w (zA' ij) : ℝ)

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
