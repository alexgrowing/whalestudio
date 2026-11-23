import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DoubledPlaneEmb
open Matrix

section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}

def coef (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin n) (Fin n₁) E) :
    Matrix (Fin n₁) (Fin n) E :=
  J₁ᵀ⁻¹ * (ι.map σ)ᵀ * Jᵀ

def pairVec (J : Matrix (Fin n) (Fin n) E) (v : Fin n → E) : Fin n → E := J *ᵥ fun i => σ (v i)

def frameT (ι : Matrix (Fin n) (Fin n₁) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n₁ ⊕ Fin 2) E :=
  Matrix.fromCols ι (Matrix.of fun i k => ![x i, y i] k)

def frameS (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (x y : Fin n → E) : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E :=
  Matrix.fromRows (coef σ J J₁ ι) (Matrix.of ![pairVec σ J y, pairVec σ J x])

variable {σ}

theorem dot_pairVec (J : Matrix (Fin n) (Fin n) E) (w v : Fin n → E) : w ⬝ᵥ pairVec σ J v = form σ J w v := rfl

theorem form_symm {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ j i]; ring

end Alg

section Frame
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {x y : Fin n → E}

theorem form_col (v : Fin n → E) (k : Fin n₁) :
    form σ J v (ι *ᵥ Pi.single k 1) = ((ι.map σ)ᵀ *ᵥ (Jᵀ *ᵥ v)) k := by
  simp only [form, dotProduct, mulVec, Matrix.map_apply, transpose_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem coef_mul_self (hdet : J₁.det ≠ 0) (gram : ιᵀ * J * ι.map σ = J₁) : coef σ J J₁ ι * ι = 1 := by
  have h : (ι.map σ)ᵀ * Jᵀ * ι = J₁ᵀ := by
    rw [← gram]; simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [coef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ Jᵀ, h]
  exact nonsing_inv_mul _ (by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet)

theorem coef_mulVec (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin n → E)
    (hv : ∀ u, form σ J (ι *ᵥ u) v = 0) : coef σ J J₁ ι *ᵥ v = 0 := by
  have h : (ι.map σ)ᵀ *ᵥ (Jᵀ *ᵥ v) = 0 := by
    funext k
    rw [← form_col, form_symm hσ hJ, hv, map_zero, Pi.zero_apply]
  rw [coef, ← mulVec_mulVec, ← mulVec_mulVec, h, mulVec_zero]

theorem frameS_mul_frameT (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J₁.det ≠ 0)
    (xx : form σ J x x = 0) (yy : form σ J y y = 0) (xy : form σ J x y = 1)
    (orth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (gram : ιᵀ * J * ι.map σ = J₁) :
    frameS σ J J₁ ι x y * frameT ι x y = 1 := by
  have hQx := coef_mulVec (J₁ := J₁) hσ hJ x fun u => (orth u).1
  have hQy := coef_mulVec (J₁ := J₁) hσ hJ y fun u => (orth u).2
  have yx : form σ J y x = 1 := by rw [form_symm hσ hJ, xy, map_one]
  rw [frameS, frameT, fromRows_mul_fromCols, coef_mul_self hdet gram, ← fromBlocks_one]
  congr 1
  · ext i k; fin_cases k
    · simpa [mul_apply, mulVec, dotProduct] using congrFun hQx i
    · simpa [mul_apply, mulVec, dotProduct] using congrFun hQy i
  · ext r k; fin_cases r
    · have := (orth (Pi.single k 1)).2
      simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      simpa [mul_apply, pairVec, mulVec, dotProduct, mul_comm] using this
    · have := (orth (Pi.single k 1)).1
      simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      simpa [mul_apply, pairVec, mulVec, dotProduct, mul_comm] using this
  · ext r k; fin_cases r <;> fin_cases k
    · simpa [mul_apply, pairVec, Fin.sum_univ_two, ← dot_pairVec, dotProduct, mul_comm] using xy
    · simpa [mul_apply, pairVec, ← dot_pairVec, dotProduct, mul_comm] using yy
    · simpa [mul_apply, pairVec, ← dot_pairVec, dotProduct, mul_comm] using xx
    · simpa [mul_apply, pairVec, ← dot_pairVec, dotProduct, mul_comm] using yx

end Frame

section Frame2
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {x y : Fin n → E}

theorem frameT_mul_frameS (rank : n = n₁ + 2) (h : frameS σ J J₁ ι x y * frameT ι x y = 1) :
    frameT ι x y * frameS σ J J₁ ι x y = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin n₁ ⊕ Fin 2) (Fin n) E (by simp [rank])).mp h

theorem frameT_mul_frameS_eq : frameT ι x y * frameS σ J J₁ ι x y =
    ι * coef σ J J₁ ι + vecMulVec x (pairVec σ J y) + vecMulVec y (pairVec σ J x) := by
  rw [frameT, frameS, fromCols_mul_fromRows, add_assoc]
  congr 1
  ext i j
  simp [mul_apply, Fin.sum_univ_two, vecMulVec]

theorem herm_map_transpose (hJ : ∀ i j, σ (J j i) = J i j) : (J.map σ)ᵀ = J := by
  ext i j; simp [hJ]

theorem coef_transpose_mul (hdet : J₁.det ≠ 0) : (coef σ J J₁ ι)ᵀ * J₁ = J * ι.map σ := by
  rw [coef, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, transpose_nonsing_inv,
    transpose_transpose]
  simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]

theorem transpose_mul_eq_coef (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    (hJ₁ : ∀ i j, σ (J₁ j i) = J₁ i j) (hdet : J₁.det ≠ 0) : ιᵀ * J = J₁ * (coef σ J J₁ ι).map σ := by
  have hm : ∀ {a b c : ℕ} (M : Matrix (Fin a) (Fin b) E) (N : Matrix (Fin b) (Fin c) E),
      (M * N).map σ = M.map σ * N.map σ := fun M N => Matrix.map_mul (f := (σ : E →+* E))
  have h := congrArg (fun M => (M.map σ)ᵀ) (coef_transpose_mul (σ := σ) (J := J) (ι := ι) hdet)
  have hι : (ι.map σ).map σ = ι := by ext i j; simp [hσ]
  rw [hm, hm, transpose_mul, transpose_mul, hι, herm_map_transpose hJ, herm_map_transpose hJ₁, ← transpose_map,
    transpose_transpose] at h
  exact h.symm

theorem frame_gram (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    (xx : form σ J x x = 0) (yy : form σ J y y = 0) (xy : form σ J x y = 1)
    (orth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (gram : ιᵀ * J * ι.map σ = J₁) :
    (frameT ι x y)ᵀ * J * (frameT ι x y).map σ = fromBlocks J₁ 0 0 !![0, 1; 1, 0] := by
  have yx : form σ J y x = 1 := by rw [form_symm hσ hJ, xy, map_one]
  have o1 : ∀ k, form σ J x (ι *ᵥ Pi.single k 1) = 0 := fun k => by rw [form_symm hσ hJ, (orth _).1, map_zero]
  have o2 : ∀ k, form σ J y (ι *ᵥ Pi.single k 1) = 0 := fun k => by rw [form_symm hσ hJ, (orth _).2, map_zero]
  rw [frameT, transpose_fromCols, fromRows_mul, fromCols_map, fromRows_mul_fromCols, gram]
  congr 1
  · ext k r; fin_cases r
    · have := (orth (Pi.single k 1)).1
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := (orth (Pi.single k 1)).2
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
  · ext r k; fin_cases r
    · have := o1 k
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := o2 k
      simp [form, mul_apply, mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
  · ext r k; fin_cases r <;> fin_cases k
    · have := xx
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := xy
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := yx
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)
    · have := yy
      simp [form, mul_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc] at this ⊢
      first | exact this | (rw [Finset.sum_comm]; exact this)

end Frame2

section Rot
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}

theorem fromBlocks_mul_fromRows' {R : Type} [CommRing R] {l m₁ m₂ k₁ k₂ : Type} [Fintype k₁] [Fintype k₂]
    (A : Matrix m₁ k₁ R) (B : Matrix m₁ k₂ R) (C : Matrix m₂ k₁ R) (D : Matrix m₂ k₂ R) (P : Matrix k₁ l R)
    (Q : Matrix k₂ l R) : fromBlocks A B C D * fromRows P Q = fromRows (A * P + B * Q) (C * P + D * Q) := by
  ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type]

variable (n₁) in

def rotC : Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E :=
  fromBlocks (fromBlocks 1 0 0 !![2⁻¹, 0; 0, 1]) (fromBlocks 0 0 0 !![2⁻¹, 0; 0, -1])
    (fromBlocks 0 0 0 !![0, 2⁻¹; -1, 0]) (fromBlocks 1 0 0 !![0, 2⁻¹; 1, 0])

variable (n₁) in

def rotCinv : Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E :=
  fromBlocks (fromBlocks 1 0 0 !![1, 0; 0, 2⁻¹]) (fromBlocks 0 0 0 !![0, -2⁻¹; 1, 0])
    (fromBlocks 0 0 0 !![1, 0; 0, -2⁻¹]) (fromBlocks 1 0 0 !![0, 2⁻¹; 1, 0])

theorem rotC_mul_rotCinv [CharZero E] : rotC (E := E) n₁ * rotCinv n₁ = 1 := by
  simp only [rotC, rotCinv]
  rw [fromBlocks_multiply]
  repeat rw [fromBlocks_multiply]
  repeat rw [fromBlocks_add]
  rw [← fromBlocks_one, ← fromBlocks_one]
  congr 1
  all_goals (first | rw [← fromBlocks_one] | rw [← fromBlocks_zero] | skip)
  all_goals (congr 1)
  all_goals (try simp)
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> norm_num)

theorem rotC_map [CharZero E] : (rotC (E := E) n₁).map σ = rotC n₁ := by
  have h2 : σ 2⁻¹ = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  simp only [rotC, fromBlocks_map]
  congr 1
  all_goals (congr 1)
  all_goals (ext i j)
  all_goals (first | (fin_cases i <;> fin_cases j <;> simp [h2]) | simp [one_apply, apply_ite])

theorem rotC_unitary [CharZero E] (G₁ : Matrix (Fin n₁) (Fin n₁) E) :
    (rotC n₁)ᵀ * fromBlocks (fromBlocks G₁ 0 0 !![0, 1; 1, 0]) 0 0 (-fromBlocks G₁ 0 0 !![0, 1; 1, 0]) * rotC n₁ =
      fromBlocks (fromBlocks G₁ 0 0 !![0, 1; 1, 0]) 0 0 (-fromBlocks G₁ 0 0 !![0, 1; 1, 0]) := by
  simp only [rotC, fromBlocks_transpose, fromBlocks_neg, transpose_zero, transpose_one, neg_zero]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  repeat rw [fromBlocks_multiply]
  repeat rw [fromBlocks_add]
  congr 1
  all_goals (first | rw [← fromBlocks_zero] | skip)
  all_goals (congr 1)
  all_goals (try simp)
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> norm_num)

end Rot

section RotG
variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {x y : Fin n → E}

variable (σ J J₁ ι x y) in

def rotG : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E :=
  (Matrix.fromBlocks (frameT ι x y) (0 : Matrix (Fin n) (Fin n₁ ⊕ Fin 2) E) 0 (frameT ι x y) :
      Matrix (Fin n ⊕ Fin n) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E) * (rotC n₁ : Matrix _ _ E) *
    (Matrix.fromBlocks (frameS σ J J₁ ι x y) (0 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E) 0 (frameS σ J J₁ ι x y) :
      Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) (Fin n ⊕ Fin n) E)

theorem map_mul_σ {a b c : Type} [Fintype b] (M : Matrix a b E) (N : Matrix b c E) :
    (M * N).map σ = M.map σ * N.map σ := Matrix.map_mul (f := (σ : E →+* E))

theorem zero_map_σ {a b : Type} : (0 : Matrix a b E).map σ = 0 := by ext; simp

theorem one_map_σ {a : Type} [DecidableEq a] : (1 : Matrix a a E).map σ = 1 := by
  ext i j; simp [one_apply, apply_ite]

theorem rotG_mul_diag : rotG σ J J₁ ι x y * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) =
    fromRows (ι * coef σ J J₁ ι + vecMulVec x (pairVec σ J y)) (ι * coef σ J J₁ ι + vecMulVec x (pairVec σ J x)) := by
  rw [rotG, diagCols, Matrix.mul_assoc, Matrix.mul_assoc, fromBlocks_mul_fromRows', rotC]
  simp only [Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add]
  rw [fromBlocks_mul_fromRows', fromBlocks_mul_fromRows']
  simp only [Matrix.zero_mul, add_zero, zero_add, ← Matrix.add_mul, fromBlocks_add]
  simp only [frameS, frameT, fromBlocks_mul_fromRows', Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add,
    fromCols_mul_fromRows]
  congr 1 <;> congr 1 <;> ext i j <;> simp [mul_apply, Fin.sum_univ_two, vecMulVec] <;> norm_num

theorem dblT_mul_dblS (hTS : frameT ι x y * frameS σ J J₁ ι x y = 1) :
    fromBlocks (frameT ι x y) 0 0 (frameT ι x y) * fromBlocks (frameS σ J J₁ ι x y) 0 0 (frameS σ J J₁ ι x y) = 1 := by
  rw [fromBlocks_multiply, hTS, ← fromBlocks_one]; simp

theorem dblS_mul_dblT (hST : frameS σ J J₁ ι x y * frameT ι x y = 1) :
    fromBlocks (frameS σ J J₁ ι x y) 0 0 (frameS σ J J₁ ι x y) * fromBlocks (frameT ι x y) 0 0 (frameT ι x y) = 1 := by
  rw [fromBlocks_multiply, hST, ← fromBlocks_one]; simp

theorem rotG_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    (xx : form σ J x x = 0) (yy : form σ J y y = 0) (xy : form σ J x y = 1)
    (orth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (gram : ιᵀ * J * ι.map σ = J₁)
    (hTS : frameT ι x y * frameS σ J J₁ ι x y = 1) :
    (rotG σ J J₁ ι x y)ᵀ * fromBlocks J 0 0 (-J) * (rotG σ J J₁ ι x y).map σ = fromBlocks J 0 0 (-J) := by
  have hG := frame_gram hσ hJ xx yy xy orth gram
  set T := frameT ι x y
  set S := frameS σ J J₁ ι x y
  have hTd : (fromBlocks T 0 0 T)ᵀ * fromBlocks J 0 0 (-J) * (fromBlocks T 0 0 T).map σ =
      fromBlocks (fromBlocks J₁ 0 0 !![0, 1; 1, 0]) 0 0 (-fromBlocks J₁ 0 0 !![0, 1; 1, 0]) := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, ← hG]
    simp [zero_map_σ, Matrix.mul_neg, Matrix.neg_mul]
  have e1 : (rotG σ J J₁ ι x y)ᵀ * fromBlocks J 0 0 (-J) * (rotG σ J J₁ ι x y).map σ =
      (fromBlocks S 0 0 S)ᵀ * ((rotC n₁)ᵀ * ((fromBlocks T 0 0 T)ᵀ * fromBlocks J 0 0 (-J) *
        (fromBlocks T 0 0 T).map σ) * rotC n₁) * (fromBlocks S 0 0 S).map σ := by
    simp only [rotG, transpose_mul, map_mul_σ, rotC_map, Matrix.mul_assoc]
    rfl
  have e2 : fromBlocks J 0 0 (-J) = (fromBlocks S 0 0 S)ᵀ * ((fromBlocks T 0 0 T)ᵀ * fromBlocks J 0 0 (-J) *
        (fromBlocks T 0 0 T).map σ) * (fromBlocks S 0 0 S).map σ := by
    have h1 := dblT_mul_dblS hTS
    calc fromBlocks J 0 0 (-J) = (fromBlocks T 0 0 T * fromBlocks S 0 0 S)ᵀ * fromBlocks J 0 0 (-J) *
          (fromBlocks T 0 0 T * fromBlocks S 0 0 S).map σ := by
          rw [h1, transpose_one, one_map_σ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [transpose_mul, map_mul_σ, Matrix.mul_assoc]
  rw [e1, hTd, rotC_unitary, ← hTd, ← e2]

theorem rotG_mul_inv (hST : frameS σ J J₁ ι x y * frameT ι x y = 1) (hTS : frameT ι x y * frameS σ J J₁ ι x y = 1) :
    rotG σ J J₁ ι x y * ((Matrix.fromBlocks (frameT ι x y) (0 : Matrix (Fin n) (Fin n₁ ⊕ Fin 2) E) 0 (frameT ι x y) :
      Matrix (Fin n ⊕ Fin n) ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) E) * (rotCinv n₁ : Matrix _ _ E) *
    (Matrix.fromBlocks (frameS σ J J₁ ι x y) (0 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E) 0 (frameS σ J J₁ ι x y) :
      Matrix ((Fin n₁ ⊕ Fin 2) ⊕ (Fin n₁ ⊕ Fin 2)) (Fin n ⊕ Fin n) E)) = 1 := by
  have h1 := dblS_mul_dblT hST
  have h2 := dblT_mul_dblS hTS
  have h3 := rotC_mul_rotCinv (E := E) (n₁ := n₁)
  simp only [rotG, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (fromBlocks (frameS σ J J₁ ι x y) 0 0 _), h1, Matrix.one_mul, ← Matrix.mul_assoc (rotC n₁), h3,
    Matrix.one_mul, h2]

end RotG

section Ext
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} {m k : Type} [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k] {K : Matrix m m A} {K₁ : Matrix k k A} {ι : Matrix m k A} {Q : Matrix k m A}

def extM (ι : Matrix m k A) (Q : Matrix k m A) (g : Matrix k k A) : Matrix m m A := 1 - ι * Q + ι * g * Q

theorem extM_one : extM ι Q 1 = 1 := by simp [extM]

theorem extM_mul (hQ : Q * ι = 1) (g h : Matrix k k A) : extM ι Q g * extM ι Q h = extM ι Q (g * h) := by
  have e1 : ∀ X : Matrix k m A, Q * (ι * X) = X := fun X => by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  simp only [extM, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, e1]
  abel

theorem map_mul_c {a b d : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b d A) :
    (M * N).map c = M.map c * N.map c := Matrix.map_mul (f := (c : A →+* A))

theorem map_add_c {a b : Type} (M N : Matrix a b A) : (M + N).map c = M.map c + N.map c := by ext; simp

theorem map_sub_c {a b : Type} (M N : Matrix a b A) : (M - N).map c = M.map c - N.map c := by ext; simp

theorem map_one_c : (1 : Matrix m m A).map c = 1 := by
  ext i j; by_cases h : i = j <;> simp [one_apply, h]

theorem extM_form (hQ : Q * ι = 1) (h2 : Qᵀ * K₁ = K * ι.map c) (h3 : ιᵀ * K = K₁ * Q.map c) (g : Matrix k k A) :
    (extM ι Q g)ᵀ * K * (extM ι Q g).map c =
      (1 - ι * Q)ᵀ * K * (1 - ι * Q).map c + Qᵀ * (gᵀ * K₁ * g.map c) * Q.map c := by
  have hιι : ιᵀ * K * ι.map c = K₁ := by
    rw [h3, Matrix.mul_assoc, ← map_mul_c, hQ, map_one_c, Matrix.mul_one]
  have hP1 : (1 - ι * Q)ᵀ * K * ι.map c = 0 := by
    rw [transpose_sub, transpose_one, transpose_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc Qᵀ,
      Matrix.mul_assoc Qᵀ, hιι, h2, sub_self]
  have hP2 : ιᵀ * K * (1 - ι * Q).map c = 0 := by
    rw [map_sub_c, map_one_c, map_mul_c, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hιι, h3, sub_self]
  have e : extM ι Q g = (1 - ι * Q) + ι * (g * Q) := by rw [extM, Matrix.mul_assoc]
  rw [e, transpose_add, map_add_c, map_mul_c, map_mul_c, transpose_mul, transpose_mul]
  have hP1' : ∀ X : Matrix k m A, (1 - ι * Q)ᵀ * (K * (ι.map c * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.zero_mul]
  have hP2' : ∀ {a : Type} (X : Matrix a k A), X * (ιᵀ * (K * (1 - ι * Q).map c)) = 0 := fun X => by
    rw [← Matrix.mul_assoc ιᵀ, hP2, Matrix.mul_zero]
  have hιι' : ∀ {a : Type} (X : Matrix a k A) (Y : Matrix k m A), X * (ιᵀ * (K * (ι.map c * Y))) = X * (K₁ * Y) :=
    fun X Y => by rw [← Matrix.mul_assoc K, ← Matrix.mul_assoc ιᵀ (K * ι.map c), ← Matrix.mul_assoc ιᵀ K, hιι]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hP1', hP2', hιι', add_zero, zero_add, Matrix.mul_zero]

theorem extM_unitary (hQ : Q * ι = 1) (h2 : Qᵀ * K₁ = K * ι.map c) (h3 : ιᵀ * K = K₁ * Q.map c) (g : Matrix k k A)
    (hg : gᵀ * K₁ * g.map c = K₁) : (extM ι Q g)ᵀ * K * (extM ι Q g).map c = K := by
  have h1 := extM_form hQ h2 h3 1
  simp only [extM_one, transpose_one, Matrix.one_mul, Matrix.mul_one, map_one_c] at h1
  rw [extM_form hQ h2 h3, hg]; exact h1.symm

variable (c K K₁ ι Q) in

def extHom (hQ : Q * ι = 1) (h2 : Qᵀ * K₁ = K * ι.map c) (h3 : ιᵀ * K = K₁ * Q.map c) : UG c K₁ →* UG c K where
  toFun g := ⟨⟨extM ι Q g.1.1, extM ι Q (g.1⁻¹ : GL k A).1, by rw [extM_mul hQ, Units.mul_inv, extM_one],
    by rw [extM_mul hQ, Units.inv_mul, extM_one]⟩, extM_unitary hQ h2 h3 _ g.2⟩
  map_one' := by ext1; ext1; simp [extM_one]
  map_mul' g h := by ext1; ext1; simp [extM_mul hQ]

end Ext

section ExtMore
variable {A : Type} [CommRing A] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {ι : Matrix m k A} {Q : Matrix k m A}

theorem extM_mulVec_of (g : Matrix k k A) {v : m → A} (hv : Q *ᵥ v = 0) : extM ι Q g *ᵥ v = v := by
  simp [extM, sub_mulVec, add_mulVec, ← mulVec_mulVec, hv]

theorem extM_mul_self (hQ : Q * ι = 1) (g : Matrix k k A) : extM ι Q g * ι = ι * g := by
  simp only [extM, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one, sub_self,
    zero_add]

theorem mul_vecMulVec' {a b : Type} [Fintype b] (M : Matrix a b A) (u : b → A) (v : k → A) :
    M * vecMulVec u v = vecMulVec (M *ᵥ u) v := by
  ext i j; simp [vecMulVec, mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vecMulVec_mul' {a b : Type} [Fintype b] (u : a → A) (v : b → A) (M : Matrix b k A) :
    vecMulVec u v * M = vecMulVec u (v ᵥ* M) := by
  ext i j; simp [vecMulVec, mul_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem det_extM (hQ : Q * ι = 1) (t : Matrix k k A) : (extM ι Q t).det = t.det := by
  have e : extM ι Q t = 1 + ι * ((t - 1) * Q) := by
    simp only [extM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  rw [e, det_one_add_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one, add_sub_cancel]

theorem extM_dbl_fromRows (hQ : Q * ι = 1) {Ua Ub : Matrix m m A} (ha : Q * Ua = Q) (hb : Q * Ub = Q)
    (ha' : Ua * ι = ι) (hb' : Ub * ι = ι) (P : Matrix (k ⊕ k) (k ⊕ k) A) (t : Matrix k k A)
    (hP : P * (fromRows 1 1 : Matrix (k ⊕ k) k A) = fromRows 1 1 * t) :
    extM (fromBlocks ι 0 0 ι) (fromBlocks Q 0 0 Q) P * fromRows Ua Ub = fromRows Ua Ub * extM ι Q t := by
  have h1 : fromBlocks Q 0 0 Q * fromRows Ua Ub = (fromRows 1 1 : Matrix (k ⊕ k) k A) * Q := by
    rw [fromBlocks_mul_fromRows', fromRows_mul, ha, hb]; simp
  have h2 : fromBlocks ι 0 0 ι * (fromRows 1 1 : Matrix (k ⊕ k) k A) = fromRows ι ι := by
    rw [fromBlocks_mul_fromRows']; simp
  calc extM (fromBlocks ι 0 0 ι) (fromBlocks Q 0 0 Q) P * fromRows Ua Ub
      = fromRows Ua Ub - fromBlocks ι 0 0 ι * (fromBlocks Q 0 0 Q * fromRows Ua Ub) +
          fromBlocks ι 0 0 ι * (P * (fromBlocks Q 0 0 Q * fromRows Ua Ub)) := by
        simp only [extM, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = fromRows Ua Ub - fromBlocks ι 0 0 ι * (fromRows 1 1 : Matrix (k ⊕ k) k A) * Q +
          fromBlocks ι 0 0 ι * (fromRows 1 1 : Matrix (k ⊕ k) k A) * (t * Q) := by
        rw [h1, ← Matrix.mul_assoc P, hP]; simp only [Matrix.mul_assoc]
        first | rfl | (congr 2; exact Matrix.mul_assoc _ _ _)
    _ = fromRows Ua Ub - fromRows ι ι * Q + fromRows ι ι * (t * Q) := by rw [h2]
    _ = fromRows Ua Ub * extM ι Q t := by
        rw [fromRows_mul, fromRows_mul, fromRows_mul]
        simp only [extM, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ha', hb']
        ext (i | i) j <;> simp

end ExtMore

section UaFacts
variable {A : Type} [CommRing A] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {ι : Matrix m k A} {Q : Matrix k m A}

theorem coef_mul_Ua (hQ : Q * ι = 1) {x : m → A} (hx : Q *ᵥ x = 0) (v : m → A) : Q * (ι * Q + vecMulVec x v) = Q := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hQ, Matrix.one_mul, mul_vecMulVec', hx]
  ext i j; simp [vecMulVec]

theorem Ua_mul_self (hQ : Q * ι = 1) (x : m → A) {v : m → A} (hv : v ᵥ* ι = 0) : (ι * Q + vecMulVec x v) * ι = ι := by
  rw [Matrix.add_mul, Matrix.mul_assoc, hQ, Matrix.mul_one, vecMulVec_mul', hv]
  ext i j; simp [vecMulVec]

end UaFacts

section More
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E}

theorem pairVec_vecMul {v : Fin n → E} (hv : ∀ u, form σ J (ι *ᵥ u) v = 0) : pairVec σ J v ᵥ* ι = 0 := by
  funext k
  have := hv (Pi.single k 1)
  simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  simpa [vecMul, pairVec, mulVec, dotProduct, mul_comm] using this

end More

section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul' {a b d : Type} [Fintype b] (M : Matrix a b E) (N : Matrix b d E) :
    incM F (M * N) = incM F M * incM F N := Matrix.map_mul (f := inclR (F := F) (AF F))

theorem incM_add' {a b : Type} (M N : Matrix a b E) : incM F (M + N) = incM F M + incM F N := by ext; simp [incM]

theorem incM_one' {a : Type} [DecidableEq a] : incM F (1 : Matrix a a E) = 1 := by
  ext i j; by_cases h : i = j <;> simp [incM, one_apply, h]

theorem incM_zero' {a b : Type} : incM F (0 : Matrix a b E) = 0 := by ext; simp [incM]

theorem incM_neg' {a b : Type} (M : Matrix a b E) : incM F (-M) = -incM F M := by ext; simp [incM]

theorem incM_transpose' {a b : Type} (M : Matrix a b E) : incM F Mᵀ = (incM F M)ᵀ := by ext; simp [incM]

theorem incM_map_cA (σ : E →ₐ[F] E) {a b : Type} (M : Matrix a b E) :
    (incM F M).map (cA σ) = incM F (M.map σ) := by ext; simp [incM, cA, inclR]

theorem incM_vecMulVec' {a b : ℕ} (u : Fin a → E) (v : Fin b → E) :
    incM F (vecMulVec u v) = vecMulVec (incV F u) (incV F v) := by ext; simp [incM, incV, vecMulVec]

theorem incM_mulVec' {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin b → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  ext i; simp [incM, incV, mulVec, dotProduct, map_sum]

theorem incM_fromBlocks' {a b c d : Type} (P : Matrix a c E) (Q : Matrix a d E) (R : Matrix b c E) (S : Matrix b d E) :
    incM F (fromBlocks P Q R S) = fromBlocks (incM F P) (incM F Q) (incM F R) (incM F S) := by
  simp [incM, fromBlocks_map]

theorem incM_fromRows' {a b c : Type} (P : Matrix a c E) (Q : Matrix b c E) :
    incM F (fromRows P Q) = fromRows (incM F P) (incM F Q) := by
  ext (i | i) j <;> simp [incM]

theorem incV_zero' {a : ℕ} : incV F (0 : Fin a → E) = 0 := by ext; simp [incV]

theorem conj_conj_of_cm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  apply w.embedding.injective
  have e := h.2.2.2 w.embedding
  rw [e, e, star_star]

theorem det_ne_zero_of_sig {n r s : ℕ} (B : Base F E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
  obtain ⟨hrs, A, hA⟩ := h w
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * J.map (B.emb w).1 * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * J.map (B.emb w).1 * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  have e2 := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e2
  rw [Matrix.det_mul, Matrix.det_mul, ← e2, h0, map_zero]; simp

end Adelic

section ExtDiag
variable {A : Type} [CommRing A] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {ι : Matrix m k A} {Q : Matrix k m A}

theorem extM_diag (g h : Matrix k k A) :
    extM (fromBlocks ι 0 0 ι) (fromBlocks Q 0 0 Q) (fromBlocks g 0 0 h) = fromBlocks (extM ι Q g) 0 0 (extM ι Q h) := by
  simp only [extM, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem vecMulVec_inl {d : Type} (a : d → A) (v : m → A) :
    vecMulVec a (Sum.elim v (0 : m → A)) = fromCols (vecMulVec a v) 0 := by
  ext i (j | j) <;> simp [vecMulVec]

theorem vecMulVec_inr {d : Type} (a : d → A) (v : m → A) :
    vecMulVec a (Sum.elim (0 : m → A) v) = fromCols 0 (vecMulVec a v) := by
  ext i (j | j) <;> simp [vecMulVec]

theorem fromCols_add' {d : Type} (P R : Matrix d m A) (P' R' : Matrix d k A) :
    fromCols P P' + fromCols R R' = fromCols (P + R) (P' + R') := by
  ext i (j | j) <;> simp

theorem z_part {d : Type} [Fintype d] (z : Matrix d m A) (x a b : m → A) :
    z * (fromRows (ι * Q + vecMulVec x a) (ι * Q + vecMulVec x b))ᵀ =
      z * Qᵀ * (fromRows 1 1 : Matrix (k ⊕ k) k A)ᵀ * (fromBlocks ι 0 0 ι)ᵀ +
        (vecMulVec (z *ᵥ a) (Sum.elim x 0) + vecMulVec (z *ᵥ b) (Sum.elim 0 x)) := by
  rw [vecMulVec_inl, vecMulVec_inr, fromCols_add', transpose_fromRows, mul_fromCols, transpose_fromRows, transpose_one,
    mul_fromCols, Matrix.mul_one, fromBlocks_transpose, transpose_zero, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add, fromCols_add', transpose_add, transpose_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  congr 1 <;> congr 1 <;> ext i j <;> simp [vecMulVec, mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_comm, mul_left_comm] <;>
    (rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)

end ExtDiag

theorem exists_dbl_emb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ (emb : UG (cA σ) (dbl (incM F X₁.J)) →* UG (cA σ) (dbl (incM F X.J))) (g₀ : UG (cA σ) (dbl (incM F X.J))),
        Continuous emb ∧ (∀ gd₁, IsDLevi H gd₁ (emb gd₁)) ∧
        (∀ (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H 1 g₁ m → ∀ gd₁ : UG (cA σ) (dbl (incM F X₁.J)),
          gd₁.1.1 = Matrix.fromBlocks (mat g₁) 0 0 1 → (emb gd₁).1.1 = Matrix.fromBlocks (mat m) 0 0 1) ∧
        (∀ (p₁ : UG (cA σ) (dbl (incM F X₁.J))) (t₁ : GL (Fin n₁) (AE F E)),
          p₁.1.1 * (diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)) = (diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)) * t₁.1 →
          ∃ t : GL (Fin n) (AE F E), (emb p₁).1.1 * (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))) = (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))) * t.1 ∧
            Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det t₁) ∧
        ∀ z : Matrix (Fin d) (Fin n) (AE F E), ∃ z₁ : Matrix (Fin d) (Fin n₁) (AE F E), ∃ u ∈ isoD d H,
          z * (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)))ᵀ = z₁ * ((diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)))ᵀ * (dblEmb H.ι)ᵀ + u := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hσ : ∀ a, σ (σ a) = a := conj_conj_of_cm hP.base.cm
  have hJ := hP.herm.herm
  have hJ₁ := hP₁.herm.herm
  have hdet : X₁.J.det ≠ 0 := det_ne_zero_of_sig B X₁.J hP₁.herm.sig
  have hST := frameS_mul_frameT hσ hJ hdet hH.xx hH.yy hH.xy hH.orth hH.gram
  have hTS := frameT_mul_frameS hH.rank hST
  have hId : H.ι * coef σ X.J X₁.J H.ι + vecMulVec H.x (pairVec σ X.J H.y) + vecMulVec H.y (pairVec σ X.J H.x) = 1 := by
    rw [← frameT_mul_frameS_eq]; exact hTS
  have hQι := coef_mul_self hdet hH.gram
  have hQx := coef_mulVec (J₁ := X₁.J) hσ hJ H.x fun u => (hH.orth u).1
  have hQy := coef_mulVec (J₁ := X₁.J) hσ hJ H.y fun u => (hH.orth u).2
  have hαι := pairVec_vecMul (σ := σ) (J := X.J) (ι := H.ι) fun u => (hH.orth u).2
  have hβι := pairVec_vecMul (σ := σ) (J := X.J) (ι := H.ι) fun u => (hH.orth u).1
  have h2E := coef_transpose_mul (σ := σ) (J := X.J) (ι := H.ι) hdet
  have h3E := transpose_mul_eq_coef (ι := H.ι) hσ hJ hJ₁ hdet
  set Q := coef σ X.J X₁.J H.ι with hQdef
  have hQA : incM F Q * incM F H.ι = 1 := by rw [← incM_mul', hQι, incM_one']
  have hdblX : dbl (incM F X.J) = incM F (fromBlocks X.J 0 0 (-X.J)) := by
    rw [dbl, incM_fromBlocks', incM_zero', incM_neg']
  have hdblX₁ : dbl (incM F X₁.J) = incM F (fromBlocks X₁.J 0 0 (-X₁.J)) := by
    rw [dbl, incM_fromBlocks', incM_zero', incM_neg']
  have hembA : dblEmb (F := F) H.ι = incM F (fromBlocks H.ι 0 0 H.ι) := by
    rw [dblEmb, incM_fromBlocks', incM_zero']
  have hQdA : (fromBlocks (incM F Q) 0 0 (incM F Q) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n ⊕ Fin n) (AE F E)) =
      incM F (fromBlocks Q 0 0 Q) := by rw [incM_fromBlocks', incM_zero']
  have hQd : fromBlocks (incM F Q) 0 0 (incM F Q) * dblEmb (F := F) H.ι = 1 := by
    rw [dblEmb, fromBlocks_multiply, hQA]; simp
  have h2d : (fromBlocks (incM F Q) 0 0 (incM F Q))ᵀ * dbl (incM F X₁.J) =
      dbl (incM F X.J) * (dblEmb (F := F) H.ι).map (cA σ) := by
    rw [hdblX, hdblX₁, hembA, hQdA, incM_map_cA, ← incM_transpose', ← incM_mul', ← incM_mul']
    congr 1
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, h2E]
    simp [zero_map_σ, Matrix.mul_neg, Matrix.neg_mul, h2E]
  have h3d : (dblEmb (F := F) H.ι)ᵀ * dbl (incM F X.J) =
      dbl (incM F X₁.J) * (fromBlocks (incM F Q) 0 0 (incM F Q)).map (cA σ) := by
    rw [hdblX, hdblX₁, hembA, hQdA, incM_map_cA, ← incM_transpose', ← incM_mul', ← incM_mul']
    congr 1
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, h3E]
    simp [zero_map_σ, Matrix.mul_neg, Matrix.neg_mul, h3E]
  set Qd : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n ⊕ Fin n) (AE F E) := fromBlocks (incM F Q) 0 0 (incM F Q) with hQd_def
  let emb := extHom (cA σ) (dbl (incM F X.J)) (dbl (incM F X₁.J)) (dblEmb (F := F) H.ι) Qd hQd h2d h3d
  have hembv : ∀ g, (emb g).1.1 = extM (dblEmb (F := F) H.ι) Qd g.1.1 := fun g => rfl

  set G := rotG σ X.J X₁.J H.ι H.x H.y with hGdef
  have hGu := rotG_unitary hσ hJ hH.xx hH.yy hH.xy hH.orth hH.gram hTS
  have hGinv := rotG_mul_inv hST hTS
  have hGunit : IsUnit (incM F G) := by
    have hh := congrArg (incM F) hGinv
    rw [incM_mul', incM_one'] at hh
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_right_inverse hh
  have hGmem : hGunit.unit ∈ UG (cA σ) (dbl (incM F X.J)) := by
    show (hGunit.unit.1)ᵀ * _ * (hGunit.unit.1).map (cA σ) = _
    rw [IsUnit.unit_spec, hdblX, incM_map_cA, ← incM_transpose', ← incM_mul', ← incM_mul', hGu]
  let g₀ : UG (cA σ) (dbl (incM F X.J)) := ⟨hGunit.unit, hGmem⟩
  have hg₀ : g₀.1.1 = incM F G := IsUnit.unit_spec _
  have hg₀Δ : g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      fromRows (incM F (H.ι * Q + vecMulVec H.x (pairVec σ X.J H.y)))
        (incM F (H.ι * Q + vecMulVec H.x (pairVec σ X.J H.x))) := by
    rw [hg₀, ← incM_fromRows', ← rotG_mul_diag, incM_mul']
    congr 1
    rw [diagCols, diagCols, incM_fromRows', incM_one']
  have haE := coef_mul_Ua hQι hQx (pairVec σ X.J H.y)
  have hbE := coef_mul_Ua hQι hQx (pairVec σ X.J H.x)
  have haE' := Ua_mul_self hQι H.x hαι
  have hbE' := Ua_mul_self hQι H.x hβι
  refine ⟨emb, g₀, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply continuous_induced_rng.2
    apply Units.continuous_iff.2
    have hv : Continuous fun g : UG (cA σ) (dbl (incM F X₁.J)) => g.1.1 := by
      exact Units.continuous_val.comp continuous_subtype_val
    have hi : Continuous fun g : UG (cA σ) (dbl (incM F X₁.J)) => (g.1⁻¹).1 := by
      exact Units.continuous_coe_inv.comp continuous_subtype_val
    refine ⟨?_, ?_⟩
    · show Continuous fun g : UG (cA σ) (dbl (incM F X₁.J)) => extM (dblEmb (F := F) H.ι) Qd g.1.1
      unfold extM
      exact continuous_const.add ((continuous_const.matrix_mul hv).matrix_mul continuous_const)
    · show Continuous fun g : UG (cA σ) (dbl (incM F X₁.J)) => extM (dblEmb (F := F) H.ι) Qd (g.1⁻¹ : GL _ _).1
      unfold extM
      exact continuous_const.add ((continuous_const.matrix_mul hi).matrix_mul continuous_const)
  ·
    intro gd₁
    have h1 : Qd *ᵥ Sum.elim (incV F H.x) (0 : Fin n → AE F E) = 0 := by
      rw [hQd_def, fromBlocks_mulVec]; simp [incM_mulVec', hQx, incV_zero']
    have h2 : Qd *ᵥ Sum.elim (0 : Fin n → AE F E) (incV F H.x) = 0 := by
      rw [hQd_def, fromBlocks_mulVec]; simp [incM_mulVec', hQx, incV_zero']
    exact ⟨extM_mulVec_of _ h1, extM_mulVec_of _ h2, extM_mul_self hQd _⟩
  ·
    rintro g₁ m ⟨hmx, hmy, hmι⟩ gd₁ hgd
    have hmx' : mat m *ᵥ incV F H.x = incV F H.x := by rw [hmx]; simp
    have hmy' : mat m *ᵥ incV F H.y = incV F H.y := by rw [hmy]; simp
    have hIdA : incM F H.ι * incM F Q + vecMulVec (incV F H.x) (incV F (pairVec σ X.J H.y)) +
        vecMulVec (incV F H.y) (incV F (pairVec σ X.J H.x)) = 1 := by
      rw [← incM_mul', ← incM_vecMulVec', ← incM_vecMulVec', ← incM_add', ← incM_add', hId, incM_one']
    have hm : mat m = extM (incM F H.ι) (incM F Q) (mat g₁) := by
      calc mat m = mat m * (incM F H.ι * incM F Q + (vecMulVec (incV F H.x) (incV F (pairVec σ X.J H.y)) +
            vecMulVec (incV F H.y) (incV F (pairVec σ X.J H.x)))) := by rw [← add_assoc, hIdA, Matrix.mul_one]
        _ = incM F H.ι * mat g₁ * incM F Q + (vecMulVec (incV F H.x) (incV F (pairVec σ X.J H.y)) +
            vecMulVec (incV F H.y) (incV F (pairVec σ X.J H.x))) := by
          rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hmι, mul_vecMulVec', mul_vecMulVec', hmx', hmy']
        _ = extM (incM F H.ι) (incM F Q) (mat g₁) := by
          rw [extM, ← hIdA]; abel
    rw [hembv, hgd, dblEmb, hQd_def, extM_diag, extM_one, ← hm]
  ·
    intro p₁ t₁ hp
    refine ⟨⟨extM (incM F H.ι) (incM F Q) t₁.1, extM (incM F H.ι) (incM F Q) (t₁⁻¹).1,
      by rw [extM_mul hQA, Units.mul_inv, extM_one], by rw [extM_mul hQA, Units.inv_mul, extM_one]⟩, ?_, ?_⟩
    · rw [hg₀Δ, hembv, dblEmb, hQd_def]
      refine extM_dbl_fromRows hQA ?_ ?_ ?_ ?_ _ _ ?_
      · rw [← incM_mul', haE]
      · rw [← incM_mul', hbE]
      · rw [← incM_mul', haE']
      · rw [← incM_mul', hbE']
      · exact hp
    · ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, det_extM hQA]
  ·
    intro z
    refine ⟨z * (incM F Q)ᵀ, vecMulVec (z *ᵥ incV F (pairVec σ X.J H.y)) (Sum.elim (incV F H.x) 0) +
      vecMulVec (z *ᵥ incV F (pairVec σ X.J H.x)) (Sum.elim 0 (incV F H.x)), ⟨_, _, rfl⟩, ?_⟩
    rw [hg₀Δ]
    simp only [incM_add', incM_mul', incM_vecMulVec']
    exact z_part z _ _ _

end GlobalTheory.DoubledPlaneEmb
