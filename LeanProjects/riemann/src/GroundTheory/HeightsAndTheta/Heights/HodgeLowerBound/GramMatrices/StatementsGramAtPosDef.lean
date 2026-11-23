import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.MuLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

def GramAtPosDef.Statement (D : ComponentData II Ψ K ι Ω E) : Prop :=
  ∀ (τ : Ψ) (z : (Σ k, ι k) → ℂ) (c : (k : K) → ι k) (f : Ω) (bfr : Fin D.N → E τ),
    z ∈ D.Xo → IsFrameOver D.y (D.W τ) c f bfr → InFrameDomain D.y c f z → (gramAt (D.h τ) bfr z).PosDef

namespace DefinitionOfMu.LineEx

open GroundTheory.Heights₂.Heights.LowerBoundFree.Line IndefiniteRowSideFullHecke.LowerBoundFree IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag

end DefinitionOfMu.LineEx

end GroundTheory.Heights₂.Heights.LowerBoundFree
