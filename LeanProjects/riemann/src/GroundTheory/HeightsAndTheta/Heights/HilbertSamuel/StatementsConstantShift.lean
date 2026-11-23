import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

section Def

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def HermLine.constShift (A : HermLine ι) (η : ℝ) : HermLine ι :=
  A.tensor (HermLine.ofWeight (fun _ => η) (fun _ _ _ => rfl))

end Def

def ConstantShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (η : ℝ),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm A →
    I P (D + 1) (fun _ => HermLine.constShift A η) =
      I P (D + 1) (fun _ => A) - ((D : ℝ) + 1) * η * geomDeg P A D

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
