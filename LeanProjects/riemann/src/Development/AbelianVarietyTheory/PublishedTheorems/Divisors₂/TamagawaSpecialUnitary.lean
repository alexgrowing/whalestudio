import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

noncomputable section

namespace GlobalTheory.Published

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol
open scoped ENNReal

def TamagawaSpecialUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)]
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E)
    (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    2 ≤ r → Unr E → SelfDualLat G Λ →
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e →
    IsSReps G (Λ : Set (Fin r → E)) 1 s →
    Multipliable (locFactor E r) ∧
    (∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G)
        (tangentHaar (realSU Ψ G) (formLie Ψ e))) *
      ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) *
        ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) *
        ∏' v, locFactor E r v) = 1

end GlobalTheory.Published
