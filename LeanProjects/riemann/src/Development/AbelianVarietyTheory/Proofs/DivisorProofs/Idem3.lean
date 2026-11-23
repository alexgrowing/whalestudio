import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipHaar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

variable (σ : E →ₐ[F] E)

def adj {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) (AE F E) →+ Matrix (Fin n) (Fin n) (AE F E) where
  toFun X := (incM F (J.map σ))⁻¹ * (X.map (cA σ))ᵀ * incM F (J.map σ)
  map_zero' := by simp
  map_add' X Y := by
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

def prX {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) : Matrix (Fin n) (Fin n) E :=
  Matrix.vecMulVec H.x (J *ᵥ fun i => σ (H.y i))

def prY {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) : Matrix (Fin n) (Fin n) E :=
  -Matrix.vecMulVec H.y (J *ᵥ fun i => σ (H.x i))

def prI {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) : Matrix (Fin n) (Fin n) E :=
  1 - prX σ J H - prY σ J H

def idem3 {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) : Fin 3 → Matrix (Fin n) (Fin n) (AE F E) :=
  ![incM F (prX σ J H), incM F (prI σ J H), incM F (prY σ J H)]

def wt3 : Fin 3 → ℤ := ![1, 0, -1]

end GlobalTheory.UnipHaar

end
