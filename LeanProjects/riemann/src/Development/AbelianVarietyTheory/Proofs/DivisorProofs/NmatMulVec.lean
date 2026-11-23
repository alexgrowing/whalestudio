import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def nmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → AE F E) (c : AE F E) :
    Matrix (Fin n) (Fin n) (AE F E) :=
  1 - Matrix.vecMulVec (u + c • x) (incM F J *ᵥ fun i => cA σ (x i)) -
    Matrix.vecMulVec x (incM F J *ᵥ fun i => cA σ (u i))

theorem nmat_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → AE F E) (c : AE F E)
    (v : Fin n → AE F E) : nmat σ J x u c *ᵥ v = v - hA σ J v x • (u + c • x) - hA σ J v u • x := by
  ext i
  simp only [nmat, hA, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.vecMulVec_mulVec, Pi.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm v, dotProduct_comm v]
  ring

end GlobalTheory.UnipMass
