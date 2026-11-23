import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

def EAtNeZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)), eAt E v ≠ 0

def UnitDich : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) (u : E ⊗[F] Formalism.L2.Herm.Af F),
    eAt E v * (u * Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) u) = 0 ∨ ∃ u', eAt E v * (u * u') = eAt E v

def ShiftOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (_ : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) (α β : E ⊗[F] Formalism.L2.Herm.Af F),
    (∃ α', eAt E v * (α * α') = eAt E v) →
    ∃ t : E, star t * t = 1 ∧ ∃ w, eAt E v * ((α * iA F E t + β) * w) = eAt E v

def ShiftDiag : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (_ : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
    ∃ t : Fin n → E, (∀ i, star (t i) * t i = 1) ∧
      ∃ w, eAt E v * ((M + Matrix.diagonal fun i => iA F E (t i)).det * w) = eAt E v

def ApproxA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : 𝓞 F), D ≠ 0 → ∀ u : E ⊗[F] Formalism.L2.Herm.Af F,
    ∃ b : E, ∃ s ∈ Formalism.L2.Herm.intAf F E, u = iA F E b + iA F E (algebraMap (𝓞 F) E D) * s

def UnitNear : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (_ : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F), π ∈ v.asIdeal → ∀ (n : ℕ)
    (s : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), (∀ i j, s i j ∈ Formalism.L2.Herm.intAf F E) →
    ∃ R : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), (∀ i j, R i j ∈ Formalism.L2.Herm.intAf F E) ∧
      eAt E v • ((1 - iA F E (algebraMap (𝓞 F) E π) • s) * R) = eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

def CayleyU : Prop :=
  ∀ (A : Type) [CommRing A] (σ : A →+* A), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (Q : GL (Fin n) A),
    (Q : Matrix (Fin n) (Fin n) A) + Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) A) = 1 →
    ∃ g ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) A),
      (g : Matrix (Fin n) (Fin n) A) = ((Q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1

def CayleyQ : Prop :=
  ∀ (A : Type) [CommRing A] (σ : A →+* A), (∀ a, σ (σ a) = a) → ∀ (n : ℕ),
    ∀ x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) A), ∀ P : GL (Fin n) A,
    (P : Matrix (Fin n) (Fin n) A) = 1 + (x : Matrix (Fin n) (Fin n) A) →
    ((P⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) + Formalism.UG.cT σ ((P⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1

def CayleyStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)), ∀ x ∈ UAd hc n,
    IsUnit (1 + (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) →
    ∃ γ ∈ URat hc n,
      IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

def IntAtInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)), ∀ y ∈ UAd hc n,
    IntAt v (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) →
    IntAt v ((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

def WeakApproxAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n

end Formalism.L2.GenusGluing.Gen
