import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.ConeBump

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def integ {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (v : Pl F)
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (φ : (Fin n × Fin d → Fv F v) → ℂ) (k : UA σ X.J)
    (l : (AE F E)ˣ) : (Fin n₁ × Fin d₁ → Fv F v) → ℂ :=
  ev (locOp v (M.co.rho B.ψ (partFin v (u l))) (locOp v (om (k, 1)) φ))

def disp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (x₀ : Fin n → E) (k : UA σ J) (l : (AE F E)ˣ) :
    Fin n → Fv F v ⊗[F] E :=
  fun i => compFin F E v ((l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i) - compFin F E v (incV F x₀ i)

theorem coneFinInt_eq {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (om : Rep σ X W)
    (v : Pl F) (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → Fv F v) :
    coneFinInt B M om v ev u ν z φ k l y = integ B M om v ev u φ k l y * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) :=
  mul_assoc _ _ _

theorem disp_one_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (x₀ : Fin n → E) :
    disp v x₀ (1 : UA σ J) 1 = 0 := by
  funext i
  simp [disp, mat, Matrix.one_mulVec]

end GlobalTheory.ConeBump
