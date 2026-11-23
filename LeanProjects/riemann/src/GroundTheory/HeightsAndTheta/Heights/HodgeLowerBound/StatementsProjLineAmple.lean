import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

def ProjLineAmple.Statement : Prop :=
  ∀ A : HermLine (PBlk 2), IsSmoothHerm A → 0 < A.a () → AmpleOnGenericFibre (⊥ : Ideal (MRing (PBlk 2))) A

namespace Line

theorem isOpen_nonzeroL : IsOpen {y : (Σ _ : Unit, Fin 2) → ℂ | ∃ i, y ⟨(), i⟩ ≠ 0} := by
  simp only [Set.ofPred_exists]
  exact isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
