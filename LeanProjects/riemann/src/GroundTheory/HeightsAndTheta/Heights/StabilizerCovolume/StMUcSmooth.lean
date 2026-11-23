import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def MUcSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.bregWeight t) → IsSmoothHerm (MUc H S B p q t)

section Inhabitants

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {H : HodgeData D} {M : XModel D}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
