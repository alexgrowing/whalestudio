import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteDatumOfHomLatticeCosetSelfDual
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteDatum_of_homLatticeCoset_selfDual : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {ε : Bool} {S T : GlobalTheory.Grid.Node D} {e : AE D}
    {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (c : GlobalTheory.Grid.Coset S T I) {f₀ f : WO S.V T.V → ℂ},
    GlobalTheory.Grid.IsVac ψ θ ε S T f₀ → IsSelfDualC S.V S.Λ → IsSelfDualC T.V T.Λ → IsIdemSum e P → I ≠ ⊥ →
    GlobalTheory.Grid.IsCosetVec ψ ε S T e I c f₀ f → GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  first | exact @GlobalTheory.Grid.isFinVec_of_isCosetVec | exact GlobalTheory.Grid.isFinVec_of_isCosetVec | (intros; apply GlobalTheory.Grid.isFinVec_of_isCosetVec <;> assumption)
