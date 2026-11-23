import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ProjHoloLocal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e →
    ∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ e.source →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧ ∃ F : ((Σ k, ι k) → ℂ) → Fin D.n → ℂ,
        DifferentiableOn ℂ F W ∧
          ∀ z' ∈ W ∩ mcPts (mCoordIdeal D.y), M.proj z' ∈ e.source ∧ e (M.proj z') = F z'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
