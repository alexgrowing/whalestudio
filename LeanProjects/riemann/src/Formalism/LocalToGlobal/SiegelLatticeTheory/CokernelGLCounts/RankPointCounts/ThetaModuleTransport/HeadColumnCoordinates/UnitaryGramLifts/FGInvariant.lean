import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScCMulInv

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA3

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def phiEq (A A' : Matrix (Ix r) (Ix r) O) (h1 : A * A' = 1) (h2 : A' * A = 1) : (Ix r → O) ≃ₗ[O] (Ix r → O) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear A) (Matrix.vecMulLinear A')
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one,
        LinearMap.id_apply])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one,
        LinearMap.id_apply])

theorem coe_vecMul (Y : Ix r → O) (A : Matrix (Ix r) (Ix r) O) (j : Ix r) :
    ((Matrix.vecMul Y A j : O) : E) = Matrix.vecMul (fun i => (Y i : E)) (A.map O.subtype) j := by
  simp [Matrix.vecMul, dotProduct]

theorem relC_fwd (G G' C C' : Matrix (Ix r) (Ix r) E) (hC : C * C' = 1) (hG : G' = C.transpose * G * C.map cj)
    (A : Matrix (Ix r) (Ix r) O) (hA : A.map O.subtype = C.map cj) (hC'O : ∀ i j, C' j i ∈ O)
    (Y : Ix r → O) (hY : ∃ c : Ix r → O, ∀ j, (Y j : E) = ∑ i, (c i : E) * G i j) :
    ∃ c : Ix r → O, ∀ j, ((Matrix.vecMul Y A j : O) : E) = ∑ i, (c i : E) * G' i j := by
  obtain ⟨c, hc⟩ := hY
  let c' : Ix r → O := fun i => ⟨∑ k, (c k : E) * C' i k, Subring.sum_mem _ fun k _ => O.mul_mem (c k).2 (hC'O k i)⟩
  refine ⟨c', fun j => ?_⟩
  have hcE : (fun i => (c' i : E)) = Matrix.vecMul (fun k => (c k : E)) C'.transpose := by
    funext i; simp [c', Matrix.vecMul, dotProduct]
  have hYE : (fun i => (Y i : E)) = Matrix.vecMul (fun k => (c k : E)) G := by
    funext j; rw [hc j]; simp [Matrix.vecMul, dotProduct]
  rw [coe_vecMul, hA, hYE]
  show _ = Matrix.vecMul (fun i => (c' i : E)) G' j
  rw [hcE, hG, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, hC, Matrix.transpose_one, Matrix.one_mul]

def fG (G : Matrix (Ix r) (Ix r) E) (Y W : Ix r → E) : E := ∑ i, ∑ j, Y i * G⁻¹ i j * cj (W j)

theorem fG_eq (G : Matrix (Ix r) (Ix r) E) (Y W : Ix r → E) :
    fG cj G Y W = Matrix.vecMul Y G⁻¹ ⬝ᵥ (fun j => cj (W j)) := by
  unfold fG
  simp only [dotProduct, Matrix.vecMul, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem fG_invariant (hcj : ∀ x, cj (cj x) = x) (G G' C : Matrix (Ix r) (Ix r) E)
    (hG : G' = C.transpose * G * C.map cj) (hCu : IsUnit C.det) (hCcu : IsUnit (C.map cj).det) (Y W : Ix r → E) :
    fG cj G' (Matrix.vecMul Y (C.map cj)) (Matrix.vecMul W (C.map cj)) = fG cj G Y W := by
  have hcw : (fun j => cj (Matrix.vecMul W (C.map cj) j)) = C.transpose.mulVec fun j => cj (W j) := by
    funext j; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, hcj, mul_comm]
  have hCt : IsUnit C.transpose.det := by rw [Matrix.det_transpose]; exact hCu
  rw [fG_eq, fG_eq, hcw, hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hCcu, Matrix.one_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCt, Matrix.mul_one]

end ScaleA3

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
