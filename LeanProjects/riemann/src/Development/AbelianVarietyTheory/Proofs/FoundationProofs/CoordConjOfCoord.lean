import Mathlib

noncomputable section

open scoped Matrix

namespace GlobalTheory.Sl2Ad

variable {K : Type*} [Field K]

def coord (X : Matrix (Fin 2) (Fin 2) K) : Fin 3 → K := ![X 0 1, X 1 0, X 0 0]

def ofCoord (v : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K := !![v 2, v 0; v 1, -v 2]

def ad (A : GL (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i

def form : LinearMap.BilinForm K (Fin 3 → K) := Matrix.toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2]

theorem trace_ofCoord (v : Fin 3 → K) : (ofCoord v).trace = 0 := by
  simp [ofCoord, Matrix.trace_fin_two]

theorem ofCoord_coord {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) : ofCoord (coord X) = X := by
  rw [Matrix.trace_fin_two] at hX
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord, coord] <;> linear_combination -hX

theorem coord_ofCoord (v : Fin 3 → K) : coord (ofCoord v) = v := by
  ext i; fin_cases i <;> simp [ofCoord, coord]

theorem coord_add (X Y : Matrix (Fin 2) (Fin 2) K) : coord (X + Y) = coord X + coord Y := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_smul (c : K) (X : Matrix (Fin 2) (Fin 2) K) : coord (c • X) = c • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem ofCoord_eq_sum (v : Fin 3 → K) : ofCoord v = ∑ j, v j • ofCoord (Pi.single j 1) := by
  ext i k; fin_cases i <;> fin_cases k <;> simp [ofCoord, Fin.sum_univ_three]

theorem coord_conj_ofCoord (A : GL (Fin 2) K) (v : Fin 3 → K) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ v := by
  conv_lhs => rw [ofCoord_eq_sum]
  ext i
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mulVec, dotProduct, ad, Matrix.of_apply]
  rw [show ∀ (s : Finset (Fin 3)) (f : Fin 3 → Matrix (Fin 2) (Fin 2) K), coord (∑ j ∈ s, f j) i = ∑ j ∈ s, coord (f j) i from by
    intro s f; induction s using Finset.induction_on with
    | empty => simp [coord]; fin_cases i <;> rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, Pi.add_apply, ih]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coord_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem trace_conj (A : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem coord_conj (A : GL (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ coord X := by
  conv_lhs => rw [← ofCoord_coord hX]
  exact coord_conj_ofCoord A _

theorem ad_mul (A B : GL (Fin 2) K) : ad (A * B) = ad A * ad B := by
  ext i j
  have h1 := coord_conj_ofCoord (A * B) (Pi.single j 1)
  have h2 := coord_conj_ofCoord B (Pi.single j 1)
  have h3 := coord_conj A (X := (B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (by rw [trace_conj, trace_ofCoord])
  rw [h2] at h3
  have : ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * (((A * B)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (A : Matrix (Fin 2) (Fin 2) K) * ((B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [this, h3, Matrix.mulVec_mulVec] at h1
  have := congrFun h1 i
  simpa [Matrix.mulVec_single, Matrix.mul_apply] using this.symm

theorem ad_one : ad (1 : GL (Fin 2) K) = 1 := by
  ext i j
  simp only [ad, Matrix.of_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, coord_ofCoord]
  fin_cases i <;> fin_cases j <;> rfl

def adHom : GL (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := ad
  map_one' := ad_one
  map_mul' := ad_mul

theorem form_apply (v w : Fin 3 → K) : form v w = v 0 * w 1 + v 1 * w 0 + 2 * (v 2 * w 2) := by
  simp [form, Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem form_coord {X Y : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) (hY : Y.trace = 0) :
    form (coord X) (coord Y) = (X * Y).trace := by
  rw [Matrix.trace_fin_two] at hX hY
  rw [form_apply]
  simp [coord, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (X 0 0) * hY - (Y 1 1) * hX

end GlobalTheory.Sl2Ad

end
