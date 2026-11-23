import Formalism.GaloisCohomology.Statement

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

namespace UpperTheory.V

def HasMuQ (l : ℕ) (L : Type) [Field L] : Prop := ∃ ζ : L, IsPrimitiveRoot ζ (if l = 2 then 4 else l)

def kBound (C : ℝ) (e n D : ℕ) : ℝ := Real.exp ((2 * (e : ℝ) * n) ^ C * Real.log (2 * (D : ℝ)))

def LemmaK (CK : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (D : LData L Ω l), IsTotallyComplex L → HasMuQ l L → ∀ e : ℕ, 1 ≤ e →
      Finite (H2 (zlTw D ((e : ℤ) + 1))) ∧
        Real.log (Nat.card (H2 (zlTw D ((e : ℤ) + 1)))) ≤ kBound CK e (Module.finrank ℚ L) (discr L).natAbs

end UpperTheory.V

end
