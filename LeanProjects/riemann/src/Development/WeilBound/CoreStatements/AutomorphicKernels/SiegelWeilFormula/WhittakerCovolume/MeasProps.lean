import Formalism.UnipotentAdelicQuotients.SWXSDefs

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.KWhit.MeasP

open HeckeCharacterZeroLocus.SiegelWeilU MeasureTheory
open scoped TensorProduct

def ratHerm (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) :
    AddSubgroup (HermR (AF F) σ n) :=
  AddSubgroup.comap (HermR (AF F) σ n).subtype
    (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom).range

def ratTupA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → AF F ⊗[F] E) :=
  (AddMonoidHom.compLeft (AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin M)) (Fin n)).range

def HermCovol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (n : ℕ) (ν : Measure (HermR (AF F) σ n)), SdHerm F E σ (AF F) ψ n ν →
    ∃ 𝓕, IsAddFundamentalDomain (ratHerm F E σ n) 𝓕 ν ∧ ν 𝓕 = 1

def TupCovol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)),
    SdW F E σ M J (AF F) ψ n μ → ∃ 𝓕, IsAddFundamentalDomain (ratTupA F E n M) 𝓕 μ ∧ μ 𝓕 = 1

end PositivityTheory.SiegelWeilFormula.KWhit.MeasP

end
