import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ValPolyLineX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

def FlagGenericPointScale.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) {R : Type} [CommRing R]
    (x : (Σ k, ι k) → R) (V : WedgeVals Pl R) (α : K ⊕ (Ψ × Fin (D.N - 1)) → R), (∀ β, IsUnit (α β)) →
    ∀ F : MRing Pl.ιY,
      aeval (genPtR Pl (fun p => α (Sum.inl p.1) * x p) (fun q m c => α (Sum.inr q) * V q m c)) F = 0 ↔
        aeval (genPtR Pl x V) F = 0

namespace FlagGenericPointScale

open Line

end FlagGenericPointScale

end GroundTheory.Heights₂.Heights.LowerBoundFree
