import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal Classical

namespace GlobalTheory.WeilL2Words

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def arch1 (z : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0)

def IsStdInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∃ ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) ∧
    ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)

def arch (x : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F := fun i => arch1 F (x i)

def archPair (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) :=
  (arch F h.1, arch F h.2)

def archPart (a : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

def l2A (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℝ≥0∞ :=
  @lintegral _ (borel _) μ fun y => ∫⁻ x, ‖Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

def dS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun a => deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0

def word (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  hs.foldr (fun h g => dS F ψ h g) Φ

@[simp] theorem word_nil (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ [] Φ = Φ := rfl

theorem word_cons (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h) (hs) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ (h :: hs) Φ = dS F ψ h (word F ψ hs Φ) := rfl

end GlobalTheory.WeilL2Words

end
