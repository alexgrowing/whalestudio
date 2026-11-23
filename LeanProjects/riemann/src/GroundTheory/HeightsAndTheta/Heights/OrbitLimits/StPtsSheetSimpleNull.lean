import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreCoordGoodProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def IsSimpleSheetPt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSheet P Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)

def PtsSheetSimpleNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      volume {y : Fin e → ℂ | ∃ w ∈ fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) ∧ ¬ IsSimpleSheetPt P Ψ w} = 0

def planeLift (y : Fin 2 → ℂ) : (Σ k, PBlk 3 k) → ℂ := fun p => (Fin.cons 1 y : Fin 3 → ℂ) p.2

end GroundTheory.Heights₂.Heights
