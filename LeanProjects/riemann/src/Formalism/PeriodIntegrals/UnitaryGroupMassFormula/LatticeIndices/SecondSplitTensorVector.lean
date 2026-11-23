import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedCore

noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]

def IntV (v : n → K) : Prop := ∀ i, v i ∈ O

def IntM (M : Matrix n n K) : Prop := ∀ i j, M i j ∈ O

theorem intV_mulVec {M : Matrix n n K} {v : n → K} (hM : IntM O M) (hv : IntV O v) : IntV O (M *ᵥ v) := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem intM_one : IntM O (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)

def Lat : Set (n → T) :=
  {x | IntV O (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun j => t1 θ (x j)) ∧
    IntV O (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ fun j => t2 θ (x j))}

theorem firstSplit_mulVec (M : Matrix n n T) (x : n → T) :
    (fun i => t1 θ ((M *ᵥ x) i)) = M.map (t1 θ) *ᵥ fun j => t1 θ (x j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem secondSplit_mulVec (M : Matrix n n T) (x : n → T) :
    (fun i => t2 θ ((M *ᵥ x) i)) = M.map (t2 θ) *ᵥ fun j => t2 θ (x j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def tv (j : n) : n → T := fun i => θ.symm ((P : Matrix n n K) i j, 0)

theorem firstSplit_tensor_vector (j : n) : (fun i => t1 θ (tv θ P j i)) = fun i => (P : Matrix n n K) i j := by
  funext i
  simp [tv, t1]

theorem secondSplit_tensor_vector (j : n) : (fun i => t2 θ (tv θ P j i)) = 0 := by
  funext i
  simp [tv, t2]

theorem mulVec_col (M N : Matrix n n K) (j : n) : (M *ᵥ fun i => N i j) = fun i => (M * N) i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem tv_mem (j : n) : tv θ P j ∈ Lat O θ J P := by
  simp only [Lat, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [firstSplit_tensor_vector, mulVec_col]
    have hP : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by simp
    rw [hP]
    exact fun i => intM_one O i j
  · rw [secondSplit_tensor_vector, Matrix.mulVec_zero]
    exact fun _ => O.zero_mem

def conjPrime₂ (g : GL n T) : Matrix n n K :=
  ((P⁻¹ : GL n K) : Matrix n n K) * (g : Matrix n n T).map (t1 θ) * (P : Matrix n n K)

theorem conjP_int (g : GL n T) (hg : ∀ x, x ∈ Lat O θ J P → (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) :
    IntM O (conjPrime₂ θ P g) := by
  intro i j
  have h := hg _ (tv_mem O θ J P j)
  simp only [Lat, Set.mem_setOf_eq] at h
  have h1 := h.1
  rw [firstSplit_mulVec, firstSplit_tensor_vector, mulVec_col, mulVec_col] at h1
  have e : conjPrime₂ θ P g i j =
      (((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T).map (t1 θ) * (P : Matrix n n K))) i j := by
    rw [conjPrime₂, Matrix.mul_assoc]
  rw [e]
  exact h1 i

theorem conjP_mul (g h : GL n T) : conjPrime₂ θ P (g * h) = conjPrime₂ θ P g * conjPrime₂ θ P h := by
  have hP : (P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K) = 1 := by simp
  simp only [conjPrime₂, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P : Matrix n n K) ((P⁻¹ : GL n K) : Matrix n n K), hP, Matrix.one_mul]

theorem conjP_one : conjPrime₂ θ P 1 = 1 := by
  simp [conjPrime₂]

end MassDataIdxCore
