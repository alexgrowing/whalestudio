import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

section Pull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {P' J' : Ideal (MRing ι')} {n : ℕ}

def pullPt (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k')) (x : R.X) : (Σ k, ι k) → ℂ :=
  fun p => R.lift x x (v p)

def pullQ (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) : Fin n → ℂ :=
  fun i => Ψ (segre (pullPt R v x)) i.succ / Ψ (segre (pullPt R v x)) 0

def pullW (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (pullPt R v x)) 0)⁻¹ • segre (pullPt R v x)

def pullBad (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0)}

end Pull

def pullbackPushforward_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ →
    (∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0) ∧
      ∀ y, (pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ).Finite

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
