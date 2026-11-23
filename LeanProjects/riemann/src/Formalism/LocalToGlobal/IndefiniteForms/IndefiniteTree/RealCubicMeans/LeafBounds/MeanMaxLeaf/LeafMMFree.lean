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

def TestLatticeCondition {K : Type} [Field K] [NumberField K] [StarRing K] (n : ℕ) (X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (M : Submodule (𝓞 K) (Fin n → K)) (E : ℝ) : Prop :=
  M.FG ∧ M ≠ ⊥ ∧ (∀ v, IsUnit (X' v).det) ∧ muMaxDef (Pi.basisFun K (Fin n)) X' M ≤ E

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
