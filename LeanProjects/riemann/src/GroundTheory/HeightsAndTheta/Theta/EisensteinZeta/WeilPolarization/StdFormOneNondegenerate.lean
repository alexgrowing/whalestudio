import Mathlib
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.WmSysObjects

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField IsDedekindDomain Matrix
open scoped NumberField.AdeleRing ComplexOrder nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

section Objects

variable {K : Type*} [Field K] [NumberField K]
variable {X : Type*} [AddCommGroup X] [Module K X]

def rationalTheta [FiniteDimensional K X] (Φ : AdelicPoints K X → ℂ) : ℂ :=
  ∑' ξ : X, Φ (rationalAdelicPoint ξ)

end Objects

def ThetaAbsConv.Statement : Prop :=
  ∀ (K W X Y : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y]
    (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (_ : SympPolarization ω X Y) (Φ : AdelicPoints K X → ℂ), Φ ∈ schwartzBruhatPoints K X →
      Summable (fun ξ : X ↦ ‖Φ (rationalAdelicPoint ξ)‖)

def ThetaNeZero.Statement : Prop :=
  ∀ (K W X Y : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y]
    (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (_ : SympPolarization ω X Y),
      ∃ Φ : AdelicPoints K X → ℂ, Φ ∈ schwartzBruhatPoints K X ∧ rationalTheta Φ ≠ 0

section Inhabitants

variable (K : Type*) [Field K] [NumberField K]
variable (X : Type*) [AddCommGroup X] [Module K X] [FiniteDimensional K X]

def latticeGaussian : AdelicPoints K X → ℂ :=
  schwartzBruhatTensorPi (gaussianInfPi K (Fin (Module.finrank K X)))
      (finiteTensor fun _ ↦ cosetIndicator (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) 0) ∘
    adelicCoord (Module.finBasis K X)

end Inhabitants

end

end GroundTheory.Heights₂.Theta
