import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ValPolyLineX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

def FlagDense.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (Pl : PlueckerData D.toComponentData)
    (P : IndefiniteRowSideFullHecke.LowerBoundFree.PlueckerData D) (h : Match Pl P),
    ∃ b : ∀ τ, Fin D.N → E τ, (∀ τ, LinearIndependent Ω (b τ)) ∧
      ∀ F : MRing Pl.ιY, aeval (genPt Pl b) F ≠ 0 →
        ∃ u ∈ IndefiniteRowSideFullHecke.LowerBoundFree.flagPts P, eval u (map (Int.castRingHom ℂ) (forget h F)) ≠ 0

namespace FlagDense

open Line IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag

end FlagDense

end GroundTheory.Heights₂.Heights.LowerBoundFree
