import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u v

abbrev LengthFormulaDimOne.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthAdditivity.{u, v}

abbrev LengthFormulaDimTwo.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthMultiplicativity.{u}

def ConservationOfNumber.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ a : Fin d → K → ℤ,
        cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a

open Classical in

def CutByEffectiveDivisor.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
          cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
              else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

def VerticalDivisorsCommute.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b b' : K → ℤ) (f g f' g' : MRing ι O),
        IsVerticalDivisor P ϖ b f g → IsVerticalDivisor P ϖ b' f' g' →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g) =
          cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g')

section Examples

theorem isPrime_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.1
  · exact absurd rfl h

def dimTwoExampleIdeal : Ideal (Polynomial ℤ_[2]) :=
  RingHom.ker (Polynomial.eval₂RingHom (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) 0)

instance : dimTwoExampleIdeal.IsPrime := RingHom.ker_isPrime _

abbrev DimTwoExample : Type := Localization.AtPrime dimTwoExampleIdeal

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
