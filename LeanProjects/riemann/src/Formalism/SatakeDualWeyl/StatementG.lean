import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.StatementF

noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.UG

def IsInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal

def InertLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), σ ≠ AlgHom.id F E → (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w →
    ∃ (e : E ⊗[F] v.adicCompletion F ≃+* w.adicCompletion E) (σw : w.adicCompletion E →+* w.adicCompletion E)
      (ϖ : w.adicCompletion E),
      (∀ x, e (sigR σ (v.adicCompletion F) x) = σw (e x)) ∧ IsUnramInv ϖ σw (qV F v) ∧
      ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v) ↔ e x ∈ intL (w.adicCompletion E)

def InertAntidiag : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Odd q →
    ∃ P : GL (Fin n) L, P ∈ (bc (n := Fin n) (intL L).subtype).range ∧
      cT σ (P : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = antiJ L n

def LocInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (e : E ⊗[F] v.adicCompletion F ≃+* L) (σw : L →+* L) (P : GL (Fin n) L),
    (∀ x, e (sigR σ (v.adicCompletion F) x) = σw (e x)) →
    (∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v) ↔ e x ∈ intL L) →
    P ∈ (bc (n := Fin n) (intL L).subtype).range →
    cT σw (P : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = antiJ L n →
    ∃ f : UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ≃* GU σw n,
      (∀ x, ((f x : GU σw n) : GL (Fin n) L) = P⁻¹ * bc (e : E ⊗[F] v.adicCompletion F →+* L) x * P) ∧
      ((levelV σ (1 : Matrix (Fin n) (Fin n) E) v).subgroupOf
          (UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))).map f.toMonoidHom = KU σw n

end Formalism.UG
