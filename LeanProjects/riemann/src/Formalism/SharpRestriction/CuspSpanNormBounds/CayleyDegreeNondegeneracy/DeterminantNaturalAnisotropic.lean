import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat

def GenericFlagQuotientCardBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E)
    (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' →
    (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsGeneric Λ g F F' →
      (Nat.card (BQ Λ F F') : ℝ) ≤ NE (E := E) g ^ (r + 1)

def DeterminantNaturalAnisotropic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E),
    (∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)) →
    (∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal)) →
    (∀ x : S.V, S.hT x x = 0 → x = 0) →
    ∀ M : Submodule (𝓞 E) S.V, M.FG → M ≤ dualIn S M → ∃ de : ℕ, 1 ≤ de ∧ latDet S M = de

end Formalism.MainNotions.BridgeLemma₂

end
