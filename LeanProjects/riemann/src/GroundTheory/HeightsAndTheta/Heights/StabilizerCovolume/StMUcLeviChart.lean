import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def MUcLeviChart.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.bregWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ u, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z u →
    ∀ k : Fin S.B.N, M.proj z ∈ S.B.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel M (S.B.chart k) z u v ∧
        levi (fun y => Real.log ((MUc H S B p q t).h y)) z u =
          q * levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k (M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z u

section Inhabitants

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {H : HodgeData D} {M : XModel D}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
