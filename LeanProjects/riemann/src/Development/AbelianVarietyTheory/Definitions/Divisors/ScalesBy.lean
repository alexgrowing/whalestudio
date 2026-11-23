import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResidueEisenstein

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ScalesBy (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (p : GAd σ J)
    (β : GL (Fin k) (AF F ⊗[F] E)) : Prop := (matHom _ σ J p).1 * adMat F X = adMat F X * β.1

structure DataJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  lat : Submodule.IsLattice E L
  iwa : ∀ g, ∃ p β, ScalesBy σ J X p β ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p β, ScalesBy σ J X p β → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)

def IsRepsJ (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (T : Set (ratPts σ J)) :
    Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ β, ScalesBy σ J X (γ * t⁻¹ : ratPts σ J).1 β

structure IsFlowJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (b : ℝ → GAd σ J) : Prop where
  cont : Continuous b
  add : ∀ s t, b (s + t) = b s * b t
  onX : ∀ t, ∃ β, ScalesBy σ J X (b t) β ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) = Real.exp t
  mem : ∀ t, b t ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, b t * m = m * b t

example (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) : ScalesBy σ J X 1 1 := by
  simp [ScalesBy]

end GlobalTheory.ResidueEisenstein

end
