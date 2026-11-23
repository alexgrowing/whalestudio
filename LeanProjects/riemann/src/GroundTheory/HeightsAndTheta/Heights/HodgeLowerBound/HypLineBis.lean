import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ValPolyLineX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

def FlagGenericPointValue.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (z : (Σ k, ι k) → ℂ)
    (x : (Σ k, ι k) → Ω) (x' : (Σ k, ι k) → ℂ) (V : WedgeVals Pl Ω) (V' : WedgeVals Pl ℂ),
    (∀ p, IsValueAt D.y (x p) z (x' p)) → (∀ q m c, IsValueAt D.y (V q m c) z (V' q m c)) →
    ∀ j, ValPoly D.y z (genPtR Pl x V j) (genPtR Pl x' V' j)

namespace FlagGenericPointValue

open Line

end FlagGenericPointValue

end GroundTheory.Heights₂.Heights.LowerBoundFree
