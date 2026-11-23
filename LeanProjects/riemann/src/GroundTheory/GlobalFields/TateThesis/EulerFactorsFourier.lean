import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactors
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierInfinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex WithZero
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem differentIdeal_ne_bot : differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
  FractionalIdeal.coeIdeal_ne_zero.1 coe_differentIdeal_ne_zero

def differentUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  idealUnit (differentIdeal ℤ (𝓞 K)) differentIdeal_ne_bot

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem exists_ofFinite_toFractionalIdeal_eq :
    ∃ δ : (FiniteAdeleRing (𝓞 K) K)ˣ, toFractionalIdeal (ofFinite δ) =
      idealUnit χ.conductor χ.conductor_ne_bot * differentUnit := by
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K)
    (idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
  refine ⟨toFinite K x, ?_⟩
  rw [← hx, toFractionalIdeal_eq_iff]
  intro v
  rw [count_toFractionalIdeal]
  rfl

theorem valued_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 K) K) v) = WithZero.exp (-(χ.condExp v + differentExp v)) := by
  rw [valued_eq_exp_ord, ← count_toFractionalIdeal, hδ, Units.val_mul,
    FractionalIdeal.count_mul K v (idealUnit χ.conductor χ.conductor_ne_bot).ne_zero
      (differentUnit (K := K)).ne_zero]
  rfl

def fourierConst (δ : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  (∏ w, (-I) ^ (χ.infiniteWeight w).natAbs) *
    finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)

theorem fourierConst_ne_zero {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    χ.fourierConst δ ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.2 I_ne_zero))
    (χ.finiteFourier_finiteTestFun_ne_zero δ (χ.valued_of_toFractionalIdeal_eq hδ))

theorem adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (y : 𝔸[K]) :
    adelicFourier K χ.testFunction y = χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) := by
  have hy1 : (ofFinite δ • y).1 = y.1 := by
    change (1 : InfiniteAdeleRing K) * y.1 = y.1
    exact one_mul _
  have hy2 : (ofFinite δ • y).2 = (δ : FiniteAdeleRing (𝓞 K) K) * y.2 := rfl
  rw [testFunction, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, χ.mixedFourier_infiniteSchwartz,
    χ.finiteFourier_finiteTestFun δ (χ.valued_of_toFractionalIdeal_eq hδ) y.2, testFunction,
    schwartzBruhatTensor, hy1, hy2, fourierConst]
  ring

end HeckeCharacter

end

end GroundTheory.Global
