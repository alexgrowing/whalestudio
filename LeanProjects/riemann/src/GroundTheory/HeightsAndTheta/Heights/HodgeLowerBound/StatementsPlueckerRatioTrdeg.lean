import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerArith
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PlueckerRatioTrdeg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D)
    (c : ∀ k, Pl.ιY k), (∀ k, Pl.yY ⟨k, c k⟩ ≠ 0) →
    Algebra.trdeg ℤ (Subfield.closure (coneRatios Pl.yY c)) = ((D.n + D.flagDim : ℕ) : Cardinal)

theorem PlueckerData.yY_inl {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (k : K) (t : ι k) :
    Pl.yY ⟨Sum.inl k, t⟩ = Pl.ofΩ (D.y ⟨k, t⟩) := rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
