import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CentreFin

variable {n r : ℕ}

def cutP (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ) (k : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  X * diagonal (fun i => if i ≤ k then (1 : ℂ) else 0) * (Yᴴ * J)

variable {J : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin r) ℂ}

theorem dual_swap (hJ : Jᴴ = J) (hxy : Xᴴ * J * Y = 1) : Yᴴ * J * X = 1 := by
  have := congrArg conjTranspose hxy
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_one, ← Matrix.mul_assoc] at this

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_cT_emb (h : IsCMExt F E σ) (τ : E →+* ℂ) {a b : ℕ} (C : Matrix (Fin a) (Fin b) E) :
    (Formalism.UG.cT (σ : E →+* E) C).map τ = (C.map τ)ᴴ :=
  Matrix.ext fun i j => h.2.2.2 τ (C j i)

theorem frame_emb (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    (X.map τ)ᴴ * J.map τ * X.map τ = 0 ∧ (Y.map τ)ᴴ * J.map τ * Y.map τ = 0 ∧ (X.map τ)ᴴ * J.map τ * Y.map τ = 1 := by
  simp only [← map_cT_emb h, ← Matrix.map_mul]
  rw [hW.xx, hW.yy, hW.xy]
  exact ⟨Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)⟩

end Global

end GlobalTheory.CentreFin

end
