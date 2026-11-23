import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TwoSidedDet

def sandwich {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ) where
  toFun z := (A * Matrix.of z * B : Matrix _ _ ℂ)
  map_add' z w := by
    change A * (Matrix.of z + Matrix.of w) * B = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    change A * (c • Matrix.of z) * B = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem det_sandwich {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (sandwich A B) = A.det ^ n * B.det ^ m := by
  let e : (Fin m × Fin n → ℂ) ≃ₗ[ℂ] (Fin m → Fin n → ℂ) := LinearEquiv.curry ℂ ℂ (Fin m) (Fin n)
  have h : sandwich A B = (e : _ →ₗ[ℂ] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) A B.transpose)) ∘ₗ (e.symm : _ →ₗ[ℂ] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (A * Matrix.of z * B) i j = (Matrix.kroneckerMap (· * ·) A B.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Matrix.of_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
  simp

theorem det_mulV (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) :
    LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  have h : mulV D M' M = LinearMap.pi (fun τ : D.what₂.Tau =>
      (sandwich (M'.map (embT D τ)) (M.map (embT D τ))) ∘ₗ LinearMap.proj τ) := by
    refine LinearMap.ext fun z => ?_
    rfl
  rw [h, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_sandwich, RingHom.map_det, RingHom.map_det]
  rfl

end GlobalTheory.TwoSidedDet
