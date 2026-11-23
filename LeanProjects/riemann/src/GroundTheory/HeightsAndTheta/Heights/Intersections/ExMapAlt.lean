import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

def pointFormRank_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ),
    IsArithVar Q d → d ≤ n → AnalyticAt ℂ F y → (∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) →
    ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)

def pointFormRank_holds.exLin : (Fin 2 → ℂ) →L[ℂ] ((Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj p.2

def pointFormRank_holds.exMap (y' : Fin 2 → ℂ) : (Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ :=
  (fun _ => (1 : ℂ)) + pointFormRank_holds.exLin y'

end GroundTheory.Heights₂.Heights.Inter
