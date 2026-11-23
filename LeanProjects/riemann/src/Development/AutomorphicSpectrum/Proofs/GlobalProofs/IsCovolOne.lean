import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def thetaInt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ h in 𝓕, theta σ J Φ h ∂μ

def thetaPart (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin 1 → Fin M → E)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ h in 𝓕, ∑' x : S, thetaTerm σ J Φ h x.1 ∂μ

def lev (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) : Set (Fin 1 → Fin M → E) :=
  {x | x ≠ 0 ∧ gramE σ J x = fun _ _ => algebraMap F E t}

def starT (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (b : AF F) : ℂ :=
  ∫ x, Φ x * ψ (b * qR (AF F) σ J (x 0)) ∂dx

def coefT (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (db : Measure (AF F))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (t : F) : ℂ :=
  ∫ b, starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b)) ∂db

def fouV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (y : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  ∫ x, Φ x * ψ (BR (AF F) σ J x y) ∂dx

def unipV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (b : AF F)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (x : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  ψ (b * qR (AF F) σ J (x 0)) * Φ x

def dilV {M : ℕ} (θ : ℝ →+* Ainf F) (a : ℝ) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (x : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  Φ fun i j => (pairA F (θ a) 1 ⊗ₜ[F] (1 : E)) * x i j

def IsCovolOne (db : Measure (AF F)) : Prop :=
  db.IsAddHaarMeasure ∧ ∃ D : Set (AF F),
    IsAddFundamentalDomain (algebraMap F (AF F)).toAddMonoidHom.range D db ∧ db D = 1

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV
