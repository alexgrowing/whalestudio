import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut

namespace GlobalTheory.HCF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def CentralNil (χ : (List (ℝ → GAd σ J) →₀ ℂ) → ℂ) (N : ℕ) (φ : GAd σ J → ℂ) : Prop :=
  ∀ zs : List (List (ℝ → GAd σ J) →₀ ℂ), zs.length = N → (∀ z ∈ zs, IsCentral σ J z) →
    zs.foldr (fun z f => dop z f - χ z • f) φ = 0

def forms (K U : Subgroup (GAd σ J)) (W : Submodule ℂ (K → ℂ)) (X : Set ((List (ℝ → GAd σ J) →₀ ℂ) → ℂ)) (N : ℕ) :
    Set (GAd σ J → ℂ) :=
  {φ | IsAut σ J K φ ∧ (∀ u ∈ U, u ∈ finPts σ J → ∀ g, φ (g * u) = φ g) ∧
    (∀ g, (fun k : K => φ (g * k)) ∈ W) ∧ ∃ χ ∈ X, CentralNil σ J χ N φ}

end GlobalTheory.HCF

namespace GlobalTheory.HCF

def CoreFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ K : Subgroup (GAd σ J), IsMaxCpt σ J K → ∀ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) →
        ∀ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W →
          ∀ X : Set ((List (ℝ → GAd σ J) →₀ ℂ) → ℂ), X.Finite → ∀ N : ℕ,
            FiniteDimensional ℂ (Submodule.span ℂ (forms σ J K U W X N))

end GlobalTheory.HCF

end
