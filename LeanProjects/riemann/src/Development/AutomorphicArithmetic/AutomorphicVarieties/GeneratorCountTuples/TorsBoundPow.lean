import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK

noncomputable section

open NumberField

namespace UpperTheory.V.K

abbrev HGL (L : Type) [Field L] [NumberField L] (N m : ℕ) : Type :=
  groupHomology (Rep.trivial ℤ (GL (Fin N) (𝓞 L)) ℤ) m

abbrev torsHGL (L : Type) [Field L] [NumberField L] (N m : ℕ) : AddSubgroup (HGL L N m) :=
  AddCommGroup.torsion (HGL L N m)

def tBound (C : ℝ) (m N n D : ℕ) : ℝ :=
  Real.exp (C * m * ((n : ℝ) * N) ^ 3 * N * Real.log (2 * (D : ℝ) * ((n : ℝ) * N)))

def TorsBound (C : ℝ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ e : ℕ, 1 ≤ e →
    Finite (torsHGL L (4 * e + 4) (2 * e)) ∧
      Real.log (Nat.card (torsHGL L (4 * e + 4) (2 * e))) ≤
        tBound C (2 * e) (4 * e + 4) (Module.finrank ℚ L) (discr L).natAbs

def TorsBoundPow (C : ℝ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ e : ℕ, 1 ≤ e →
    Finite (torsHGL L (4 * e + 4) (2 * e)) ∧
      Real.log (Nat.card (torsHGL L (4 * e + 4) (2 * e))) ≤ kBound C e (Module.finrank ℚ L) (discr L).natAbs

end UpperTheory.V.K

end
