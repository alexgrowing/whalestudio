import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RegAboveWeight.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ∃ t₂ : ℝ, 0 < t₂ ∧ ∃ N : Set ((Σ k, ι k) → ℂ), IsPtsNull (mCoordIdeal D.y) D.n N ∧
      ∀ t : ℝ, 0 < t → t ≤ t₂ → ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
        phMu X.H z ≤ Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
