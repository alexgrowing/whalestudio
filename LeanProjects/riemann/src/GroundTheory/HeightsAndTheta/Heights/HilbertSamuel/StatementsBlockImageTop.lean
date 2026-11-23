import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageTop.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (y : (Σ k, ι k) → Ω) (k₀ : K) (A : HermLine ι)
    (M : Matrix (Ix κ) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω) (m : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsBlockImage y k₀ M N x → A.a = unitDeg k₀ →
    IsSmoothHerm A → IsSmoothMetric m → (∀ z ∈ mcPts (mCoordIdeal y), A.h z = m.ρ (blockMapC k₀ M z)) →
    I K ι (mCoordIdeal y) (D + 1) (fun _ => A) = top I x m D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
