import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelPointSteps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibrePtNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

def HodgeFibreSpecialise.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D) (τ : Ψ)
    (b : Fin D.N → E τ) (z : (Σ k, ι k) → ℂ) (wF : Fin (P.M τ (jIdx D)) → ℂ)
    (wW : Fin (P.M τ (lastIdx D)) → ℂ),
    IsHodgeFrame D τ b → z ∈ mcPts (mCoordIdeal D.y) → IsHodgeFibrePt P τ z wF wW →
    (∃ (lam : Ω) (mu : ℂ), lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ m, ∃ (s : Ω) (v : ℂ),
      P.gen τ (jIdx D) m (b ∘ Fin.castLE (jIdx D).isLt) = lam * s ∧ IsValueAt D.y s z v ∧
        wF m = mu * v) ∧
    (∃ (lam : Ω) (mu : ℂ), lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ m, ∃ (s : Ω) (v : ℂ),
      P.gen τ (lastIdx D) m (b ∘ Fin.castLE (lastIdx D).isLt) = lam * s ∧ IsValueAt D.y s z v ∧
        wW m = mu * v)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
