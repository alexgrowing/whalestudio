import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushSheetSum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def DivPushBranchCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (A : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∑ k, m k * ({x : W k | projCoord R Ψ (x : R.X) = y ∧ divPt R Ψ (x : R.X) = w} : Set (W k)).ncard =
        multAt (P ⊔ Ideal.span {s}) W'

end GroundTheory.Heights₂.Heights.Targets
