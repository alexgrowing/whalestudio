import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

open NumberField
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Published

def SingularModuliClassField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
      IsHilbertClassField K⟮(latticeCurve L).j⟯ ∧
      Module.finrank K K⟮(latticeCurve L).j⟯ = classNumber K ∧
      (minpoly K (latticeCurve L).j).rootSet ℂ = idealInvariants K

end GlobalTheory.Published
