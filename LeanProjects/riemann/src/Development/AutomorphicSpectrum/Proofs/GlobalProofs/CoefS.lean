import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin 1 → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureC {M : ℕ} (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intF (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Af F) :=
  {y | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

def coefS (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (db : Measure (AF F))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (t : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ b, (intF S).indicator (fun _ => (1 : ℂ)) (sndA F b) *
    (starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b))) ∂db

def boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (Af F) :=
  {y | (∀ v ∈ S, y v ∈ U v) ∧ ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

def testT (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℂ :=
  (ρ (fstA F y) : ℂ) * (boxA S U).indicator (fun _ => (1 : ℂ)) (sndA F y)

def fouA (ψ : AddChar (AF F) ℂ) (db : Measure (AF F)) (T : AF F → ℂ) (b : AF F) : ℂ :=
  ∫ y, T y * ψ (y * b) ∂db

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
