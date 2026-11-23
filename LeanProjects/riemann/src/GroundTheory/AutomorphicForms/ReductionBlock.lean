import Mathlib

open Matrix

namespace GroundTheory.Automorphic

namespace Reduction

section Block

variable {R : Type*} [CommRing R] {m : ℕ}

def blockOne (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i

@[simp] theorem blockOne_last_last (M : Matrix (Fin m) (Fin m) R) :
    blockOne M (Fin.last m) (Fin.last m) = 1 := by
  simp [blockOne]

@[simp] theorem blockOne_last_castSucc (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    blockOne M (Fin.last m) (Fin.castSucc j) = 0 := by
  simp [blockOne]

@[simp] theorem blockOne_castSucc_last (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.last m) = 0 := by
  simp [blockOne]

@[simp] theorem blockOne_castSucc_castSucc (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.castSucc j) = M i j := by
  simp [blockOne]

theorem blockOne_mul (M N : Matrix (Fin m) (Fin m) R) :
    blockOne (M * N) = blockOne M * blockOne N := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem blockOne_one : blockOne (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem blockOne_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin m) (Fin m) R) :
    (blockOne M).map f = blockOne (M.map f) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp

def blockOneMonoidHom : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun := blockOne
  map_one' := blockOne_one
  map_mul' := blockOne_mul

def blockOneHom : GL (Fin m) R →* GL (Fin (m + 1)) R :=
  Units.map blockOneMonoidHom

@[simp] theorem coe_blockOneHom (γ : GL (Fin m) R) :
    ((blockOneHom γ : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      blockOne (γ : Matrix (Fin m) (Fin m) R) := rfl

theorem single_last_vecMul_blockOne (M : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* blockOne M = Pi.single (Fin.last m) 1 := by
  ext j
  induction j using Fin.lastCases <;>
    simp [vecMul, dotProduct, Pi.single_apply, Fin.castSucc_ne_last]

theorem vecMul_blockOne_castSucc (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    (y ᵥ* blockOne M) (Fin.castSucc j) = (Fin.init y ᵥ* M) j := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem vecMul_blockOne_last (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) :
    (y ᵥ* blockOne M) (Fin.last m) = y (Fin.last m) := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc]

end Block

section Row

variable {F : Type*} [Field F] {m : ℕ}

def rowMatrix (x : Fin (m + 1) → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => if i = Fin.last m then x j else if i = j then 1 else 0

theorem det_rowMatrix (x : Fin (m + 1) → F) : (rowMatrix x).det = x (Fin.last m) := by
  rw [det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [rowMatrix, Fin.castSucc_ne_last]
  · intro i j hij
    simp only [rowMatrix, of_apply]
    have hij' : i < j := hij
    have hi : i ≠ Fin.last m := fun h => by
      rw [h] at hij'
      exact absurd hij' (not_lt.2 (Fin.le_last j))
    rw [if_neg hi, if_neg hij'.ne]

theorem single_last_vecMul_rowMatrix (x : Fin (m + 1) → F) :
    Pi.single (Fin.last m) 1 ᵥ* rowMatrix x = x := by
  ext j
  rw [vecMul, dotProduct, Finset.sum_eq_single (Fin.last m)]
  · simp [rowMatrix]
  · intro b _ hb
    simp [hb]
  · simp

theorem exists_lastRow_eq {x : Fin (m + 1) → F} (hx : x ≠ 0) :
    ∃ γ : GL (Fin (m + 1)) F,
      Pi.single (Fin.last m) 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = x := by
  classical

  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun j => not_not.1 fun hj => h ⟨j, hj⟩)
  by_cases hl : x (Fin.last m) ≠ 0
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x) (by rw [det_rowMatrix]; exact hl), ?_⟩
    exact single_last_vecMul_rowMatrix x
  · rw [not_not] at hl
    have hjl : j ≠ Fin.last m := fun h => hj (h ▸ hl)
    set τ := transvection j (Fin.last m) (1 : F) with hτ
    have hτdet : τ.det = 1 := det_transvection_of_ne j (Fin.last m) hjl 1
    set x' := x ᵥ* τ with hx'
    have hx'l : x' (Fin.last m) = x j := by
      simp [hx', hτ, transvection, vecMul_add, hl, Matrix.vecMul, dotProduct,
        Matrix.single_apply]
    have hx'l0 : x' (Fin.last m) ≠ 0 := by rw [hx'l]; exact hj
    set τu : GL (Fin (m + 1)) F :=
      GeneralLinearGroup.mkOfDetNeZero τ (by rw [hτdet]; exact one_ne_zero) with hτu
    refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x') (by rw [det_rowMatrix]; exact hx'l0) *
      τu⁻¹, ?_⟩
    rw [Units.val_mul, ← vecMul_vecMul]
    change (Pi.single (Fin.last m) 1 ᵥ* rowMatrix x') ᵥ* _ = x
    have hτu' : (τu : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = τ := rfl
    rw [single_last_vecMul_rowMatrix, hx', ← hτu', vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, vecMul_one]

end Row

end Reduction

end GroundTheory.Automorphic
