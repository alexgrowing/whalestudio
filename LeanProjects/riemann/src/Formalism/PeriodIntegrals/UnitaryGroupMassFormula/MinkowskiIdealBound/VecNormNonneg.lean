import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelSetsSL2Adelic

open NumberField IsDedekindDomain

noncomputable section

namespace PIW.MinkowskiIdealBound

abbrev AF (F : Type) [Field F] [NumberField F] : Type := AdeleRing (𝓞 F) F

abbrev GF (F : Type) [Field F] [NumberField F] : Type := Matrix.SpecialLinearGroup (Fin 2) (AF F)

def idAbs (F : Type) [Field F] [NumberField F] (x : AF F) : ℝ :=
  ‖(x.1 : InfiniteAdeleRing F)‖ * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x.2 : FiniteAdeleRing (𝓞 F) F) v‖

def vecNorm (F : Type) [Field F] [NumberField F] (η : Fin 2 → AF F) : ℝ :=
  (∏ w : InfinitePlace F,
      (‖((η 0).1 : InfiniteAdeleRing F) w‖ ^ 2 + ‖((η 1).1 : InfiniteAdeleRing F) w‖ ^ 2) ^ ((w.mult : ℝ) / 2)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      max ‖((η 0).2 : FiniteAdeleRing (𝓞 F) F) v‖ ‖((η 1).2 : FiniteAdeleRing (𝓞 F) F) v‖

def Minkowski : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ C₁ : ℝ, ∀ g : GF F, ∃ ξ : Fin 2 → F, ξ ≠ 0 ∧
    vecNorm F (Matrix.vecMul (fun i => algebraMap F (AF F) (ξ i)) (g : Matrix (Fin 2) (Fin 2) (AF F))) ≤ C₁

def Iwasawa : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (GF F), IsCompact K ∧ ∀ h : GF F, ∃ k ∈ K,
    ((h * k⁻¹ : GF F) : Matrix (Fin 2) (Fin 2) (AF F)) 1 0 = 0 ∧
    idAbs F (((h * k⁻¹ : GF F) : Matrix (Fin 2) (Fin 2) (AF F)) 0 0) *
      vecNorm F ((h : Matrix (Fin 2) (Fin 2) (AF F)) 1) = 1

def IdeleRay : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∀ c : ℝ, 0 < c →
    ∃ (C : Set (AF F)ˣ) (t₀ : ℝ), IsCompact C ∧ 0 < t₀ ∧ ∀ α : (AF F)ˣ, c ≤ idAbs F (α : AF F) →
      ∃ f : F, f ≠ 0 ∧ ∃ u ∈ C, ∃ t : ℝ, t₀ ≤ t ∧ ∃ a a' : InfiniteAdeleRing F,
        (∀ w, a w * a' w = 1 ∧ InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) ∧
        (α : AF F) = algebraMap F (AF F) f * (u : AF F) * Formalism.D.adeleOfParts F a 1

def AdeleFund : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ D : Set (AF F), IsCompact D ∧
    ∀ x : AF F, ∃ f : F, x - algebraMap F (AF F) f ∈ D

end PIW.MinkowskiIdealBound

end
