import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

def pointFormEuler_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y x : Fin n → ℂ) (c : K → ℂ),
    IsSmoothHerm A → AnalyticAt ℂ F y → (∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0) → fderiv ℂ F y x = bsmul c (F y) →
    cxHessian (fun y' => Real.log (A.h (F y'))) y *ᵥ star x = 0

def pointFormEuler_holds.exLin : (Fin 1 → ℂ) →L[ℂ] ((Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 0

def pointFormEuler_holds.exMap (y' : Fin 1 → ℂ) : (Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ :=
  (fun _ => (1 : ℂ)) + pointFormEuler_holds.exLin y'

end GroundTheory.Heights₂.Heights.Inter
