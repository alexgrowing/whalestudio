import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.CompanionTheory.IwaDbl

def HasSat {B : Type} [CommRing B] (A : Subring B) (β : Type) [Fintype β] [DecidableEq β] : Prop :=
  ∀ (C : Matrix (β ⊕ β) β B) (N : Matrix β (β ⊕ β) B), N * C = 1 →
    ∃ (t t' : Matrix β β B) (D : Matrix (β ⊕ β) β B) (M : Matrix (β ⊕ β) (β ⊕ β) B), t * t' = 1 ∧
      (∀ i j, (C * t) i j ∈ A) ∧ (∀ i j, D i j ∈ A) ∧ (∀ i j, M i j ∈ A) ∧ M * Matrix.fromCols (C * t) D = 1

def locGram {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  cT (sigR R σ) b.1 * JR R J * b.1

end GlobalTheory.CompanionTheory.IwaDbl

end
