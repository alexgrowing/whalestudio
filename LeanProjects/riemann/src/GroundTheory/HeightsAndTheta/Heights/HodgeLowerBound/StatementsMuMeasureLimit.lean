import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuMeasureLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      Tendsto (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2))
        (𝓝[>] 0) (𝓝 (meanU X.H X.Cd * degMu X.H / 2)) ∧
      Tendsto (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) (𝓝[>] 0) (𝓝 (degMu X.H))

end GroundTheory.Heights₂.Heights.LowerBoundFree
