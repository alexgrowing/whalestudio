import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas

open NumberField IsDedekindDomain TensorProduct Formalism.MainNotions.UnusedSlot33 Matrix ComplexOrder

namespace Formalism.MainNotions.Ext

def FinOrdG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

def UnitaryKronecker : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1

end Formalism.MainNotions.Ext
