import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ChainTw
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker MvPolynomial

namespace GlobalTheory.KerJ

theorem eval₂_blockAct {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (σ : K →+* ℂ)
    (g : ι → Matrix (Fin n) (Fin n) K) (x : ι × Fin n × Fin n → ℂ) (P : Pol K ι n) :
    eval₂ σ x (Formalism.GradedWeylDivisibility.blockAct K g P) =
      eval₂ σ (fun k => ((g k.1).map σ * Matrix.of (fun a t => x (k.1, a, t))) k.2.1 k.2.2) P := by
  have h1 := MvPolynomial.eval₂Hom_bind₁ σ x (fun v : ι × Fin n × Fin n => ∑ b : Fin n, C (g v.1 v.2.1 b) * X (v.1, (b, v.2.2))) P
  simp only [coe_eval₂Hom] at h1
  rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_eq_bind₁, h1]
  congr 1
  funext k
  simp [eval₂_sum, Matrix.mul_apply]

theorem ufGL_val {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' γ.1.toLinearMap := by
  simp [ufGL, toGLm]
  rfl

end GlobalTheory.KerJ
