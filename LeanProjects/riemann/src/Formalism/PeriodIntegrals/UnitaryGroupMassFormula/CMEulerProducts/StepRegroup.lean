import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio

open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

def FibreShape (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (v : Ideal (𝓞 F)) : Prop :=
  (∃ P : Ideal (𝓞 E), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v ∧
      conjIdeal (K := E) P = P ∧ Ideal.absNorm P = Ideal.absNorm v ^ 2 ∧
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v → Q = P) ∨
  (∃ P Q : Ideal (𝓞 E), P.IsMaximal ∧ Q.IsMaximal ∧
      P.comap (algebraMap (𝓞 F) (𝓞 E)) = v ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v ∧ P ≠ Q ∧
      conjIdeal (K := E) P = Q ∧ conjIdeal (K := E) Q = P ∧
      Ideal.absNorm P = Ideal.absNorm v ∧ Ideal.absNorm Q = Ideal.absNorm v ∧
      ∀ R : Ideal (𝓞 E), R.IsMaximal → R.comap (algebraMap (𝓞 F) (𝓞 E)) = v → R = P ∨ R = Q)

def StepFib : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∀ v : Ideal (𝓞 F), v.IsMaximal → FibreShape F E v

def StepConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∃ σ : 𝓞 E ≃+* 𝓞 E,
      (∀ x : 𝓞 E, algebraMap (𝓞 E) E (σ x) = star (algebraMap (𝓞 E) E x)) ∧
      (∀ x : 𝓞 E, σ (σ x) = x) ∧
      (∀ P : Ideal (𝓞 E), conjIdeal (K := E) P = P.map σ) ∧
      (∀ x : 𝓞 E, σ x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E))) ∧
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ : 𝓞 E, θ - σ θ ∉ P)

def StepMult : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ), 3 ≤ M →
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => eulerFac K M P.1)

def StepLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (M : ℕ), 3 ≤ M → ∀ v : Ideal (𝓞 F), v.IsMaximal → FibreShape F E v →
    HasProd (fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} =>
      eulerFac E M c.1) (eulerF F E M v)

def StepRegroup : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (M : ℕ), Multipliable (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => eulerFac E M P.1) →
    (∀ v : Ideal (𝓞 F), v.IsMaximal →
      HasProd (fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} =>
        eulerFac E M c.1) (eulerF F E M v)) →
    lText F E M = lValEta E M

end CMEul
