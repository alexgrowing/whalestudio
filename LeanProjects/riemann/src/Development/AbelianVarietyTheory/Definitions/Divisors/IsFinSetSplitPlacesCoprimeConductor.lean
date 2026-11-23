import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def IsCMType {I : Type} (φ : I → E →+* ℂ) : Prop :=
  ∀ σ : E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)

def UnramFin (E : Type) [Field E] [NumberField E] : Prop := differentIdeal (OF E) (𝓞 E) = ⊤

def Over (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Prop :=
  P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = v.asIdeal

def Splits (v : HeightOneSpectrum (OF E)) : Prop := ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Over P v ∧ Over P' v

def expIn (𝔣 : Ideal (OF E)) (v : HeightOneSpectrum (OF E)) : ℕ := multiplicity v.asIdeal 𝔣

def IsBaseCond (𝔣 : Ideal (OF E)) : Prop :=
  𝔣 ≠ ⊥ ∧ 𝔣 ≠ ⊤ ∧ ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → Splits v ∧ expIn 𝔣 v ≤ 2 ∧
    ∃ l : ℕ, l.Prime ∧ l ≠ 2 ∧ (l : OF E) ∈ v.asIdeal ∧ ¬ (l : ℤ) ∣ discr E ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = l

def IsFinSetSplitPlacesCoprimeConductor (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  ∀ q ∈ Q, Splits q ∧ ¬ q.asIdeal ∣ 𝔣

def condQ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Ideal (OF E) := 𝔣 * ∏ q ∈ Q, q.asIdeal

def IsValChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v →
      (v ∈ Q → LevelLe χ P 1) ∧ (v ∉ Q → ExpAt χ P (expIn 𝔣 v))

def IntAt (l : ℕ) (a : ℂ) : Prop := ∃ n : ℕ, n.Coprime l ∧ IsIntegral ℤ ((n : ℂ) * a)

def UnitAt (l : ℕ) (a : ℂ) : Prop := a ≠ 0 ∧ IntAt l a ∧ IntAt l a⁻¹

def LInf {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + (|m i| : ℤ))) * Complex.Gamma (s + (|m i| : ℤ)))

end GlobalTheory.CMVal
