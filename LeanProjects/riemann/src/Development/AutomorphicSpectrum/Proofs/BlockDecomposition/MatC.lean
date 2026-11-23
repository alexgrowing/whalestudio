import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsCoord (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph Θ ∧ (∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) ∧
    (∀ x w, Θ ((1 : Ainf F) ⊗ₜ[F] x) w = τ w x) ∧
    ∀ z w, ((e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w : ℝ) : ℂ) = Θ z w + conj (Θ z w)

def tupC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n M : ℕ} (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    InfinitePlace F → Fin n → Fin M → ℂ :=
  fun w a i => Θ (X a i) w

def matC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) : Matrix (Fin n) (Fin n) ℂ :=
  fun a c => Θ (b a c) w

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
