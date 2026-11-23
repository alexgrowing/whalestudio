import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.LeviBlockRealization

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def leftTr (h : GAd σ J) : Module.End ℂ (GAd σ J → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => h * g)

@[simp] theorem leftTr_apply (h : GAd σ J) (f : GAd σ J → ℂ) (g : GAd σ J) : leftTr σ J h f g = f (h * g) := rfl

variable (F) in

def diagonalMulSingle (i : Fin r) (a : AF F ⊗[F] E) : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
  diagonal (Function.update 1 i a)

def IsBlockCentre (X Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (e : (AF F ⊗[F] E)ˣ) (h : GAd σ J) : Prop :=
  (matHom _ σ J h).1 * adMat F X = adMat F X * diagonalMulSingle F i (e : AF F ⊗[F] E) ∧
  (matHom _ σ J h).1 * adMat F Y = adMat F Y * diagonalMulSingle F i (sigR (AF F) σ ((e⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    (matHom _ σ J h).1 *ᵥ (fun k => inclR (F := F) (AF F) (z k)) = fun k => inclR (F := F) (AF F) (z k)

end GlobalTheory.LeviBlockRealization

end
