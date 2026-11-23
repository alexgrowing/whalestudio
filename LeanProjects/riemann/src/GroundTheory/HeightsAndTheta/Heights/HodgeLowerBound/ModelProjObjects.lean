import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

def modelU (M : CxModel P e) (x : M.Xc) : Set M.Xc :=
  (M.sections x).choose

def modelLift (M : CxModel P e) (x : M.Xc) : M.Xc → (Σ k, ι k) → ℂ :=
  (M.sections x).choose_spec.2.2.choose

theorem modelU_isOpen (M : CxModel P e) (x : M.Xc) : IsOpen (modelU M x) :=
  (M.sections x).choose_spec.1

theorem mem_modelU (M : CxModel P e) (x : M.Xc) : x ∈ modelU M x :=
  (M.sections x).choose_spec.2.1

theorem modelLift_spec (M : CxModel P e) (x : M.Xc) :
    (∀ y ∈ modelU M x, modelLift M x y ∈ mcPts P ∧ M.proj (modelLift M x y) = y) ∧
      ∀ p, M.atlas.HoloOn (modelU M x) fun y => modelLift M x y p :=
  (M.sections x).choose_spec.2.2.choose_spec

def modelPot (M : CxModel P e) (L : HermLine ι) (c : ℝ) : LocPot M.Xc where
  U := modelU M
  isOpen_U := modelU_isOpen M
  mem_U := mem_modelU M
  φ x y := c * Real.log (L.h (modelLift M x y))

def modelQ (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : M.Xc) : Fin e → ℂ :=
  fun i => Ψ (segre (modelLift M x x)) i.succ / Ψ (segre (modelLift M x x)) 0

def modelCrit (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set M.Xc :=
  {x | Ψ (segre (modelLift M x x)) 0 = 0 ∨ ∃ j, x ∈ (M.atlas.chart j).source ∧
    ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def modelBad (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (E : Set M.Xc) : Set M.Xc :=
  E ∪ modelCrit M Ψ

theorem modelQ_good_of_notMem (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (E : Set M.Xc) : ∀ x ∉ modelBad M Ψ E, ∀ j, x ∈ (M.atlas.chart j).source →
      AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr (Or.inr ⟨j, hj, h⟩))

end GroundTheory.Heights₂.Heights.LowerBoundFree
