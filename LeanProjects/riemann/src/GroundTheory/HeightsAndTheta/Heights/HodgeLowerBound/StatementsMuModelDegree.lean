import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsHodgeFibrePt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.FlagLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.HilbertSamuel

def MuModelDegree.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    geomDeg (PXmu P) (muRefLine P) D.toComponentData.n =
      (genDeg (mCoordIdeal D.y) D.toComponentData.n H.aMu : ℝ)

namespace LineFlag

noncomputable def HL : HodgeData DL.toComponentData := Line.lineHodge Line.zeroSystem fun _ _ => le_rfl

end LineFlag

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
