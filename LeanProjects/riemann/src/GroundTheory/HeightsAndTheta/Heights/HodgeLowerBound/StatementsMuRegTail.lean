import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegTail.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (δ : ℝ), 0 < δ →
    ∀ᶠ R in atTop, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ z => Real.log ((muReg X.H X.S B t).h z))
          X.Cd.cuspWeight -
        ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ z => Real.log ((muReg X.H X.S B t).h z))
          (fun z => min (X.Cd.cuspWeight z) R)| ≤ δ

end GroundTheory.Heights₂.Heights.LowerBoundFree
