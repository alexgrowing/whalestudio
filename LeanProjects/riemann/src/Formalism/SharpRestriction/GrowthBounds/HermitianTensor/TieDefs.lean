import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ModelIdentificationOfExplicitMap
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovWeyl
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovDet

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

theorem covY_eq (K : Type) [Field K] (m : ℕ) : ShapeCovering.covY K m = covY K m := rfl

def ExplicitMapInjective : Prop := ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → Function.Injective (PsiXY K m)

def ExplicitMapOntoTwoLetters : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → ∀ (P Q : ℕ) x,
    x ∈ twoSp K m P Q ↔ ∃ f ∈ PolAB K (m + 1) P Q, PsiXY K m f = x

def TwoLetterLatticeGaussInverse : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 1 ≤ m → ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf), IsUnit g.det →
    ∀ g' : GL (Fin (m + 1)) R.Kf, (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) = g⁻¹ →
      ∀ (P Q : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) P Q,
        PsiXY R.Kf m f ∈ twoLat R.O m P Q (colSpan R.O g) ↔ f ∈ latOf g' (GaussLat R.Ov.toSubring)

end Formalism.MainNotions.flipOneThree.Pf

end
