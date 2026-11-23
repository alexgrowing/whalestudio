import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TpIntegrandLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ q → ∃ t₂ : ℝ, 0 < t₂ ∧ ∀ t : ℝ, 0 < t → t ≤ t₂ →
      ∃ (N : Set ((Σ k, ι k) → ℂ)) (C t'₀ : ℝ), 0 < t'₀ ∧ IsPtsNull (mCoordIdeal D.y) D.n N ∧
        (∀ t' : ℝ, 0 < t' → t' < t'₀ →
          (∀ z ∈ mcPts (mCoordIdeal D.y), |X.wSt B p q t t' z| ≤ C) ∧
          ContinuousOn (X.wSt B p q t t') (mcPts (mCoordIdeal D.y) \ N)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
          Tendsto (fun t' => X.wSt B p q t t' z) (𝓝[>] 0)
            (𝓝 (cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))))

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
