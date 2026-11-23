import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedPlane

open Matrix

section Rank

variable {R : Type} [CommRing R] {N k : Type} [Fintype N] [DecidableEq N] [Fintype k] [DecidableEq k]

def rankMat (c : R →+* R) (D : Matrix N N R) (P : Matrix N k R) (C : Matrix k k R) : Matrix N N R :=
  1 + P * C * (D * P.map c)ᵀ

theorem gram_entry (c : R →+* R) (D : Matrix N N R) (P : Matrix N k R) (i j : k) :
    (Pᵀ * D * P.map c) i j = (fun r => P r i) ⬝ᵥ D *ᵥ (fun r => c (P r j)) := by
  rw [dotProduct_mulVec]; rfl

theorem rankMat_mul (c : R →+* R) (D : Matrix N N R) (P : Matrix N k R) (C C' : Matrix k k R)
    (h : C + C' + C * (Pᵀ * D * P.map c)ᵀ * C' = 0) :
    rankMat c D P C * rankMat c D P C' = 1 := by
  have e : (D * P.map c)ᵀ * P = (Pᵀ * D * P.map c)ᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have : rankMat c D P C * rankMat c D P C' =
      1 + P * (C + C' + C * (Pᵀ * D * P.map c)ᵀ * C') * (D * P.map c)ᵀ := by
    rw [← e]
    simp only [rankMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [this, h]; simp

theorem rankMat_unitary (c : R →+* R) (hc : ∀ r, c (c r) = r) (D : Matrix N N R) (hD : ∀ i j, c (D j i) = D i j)
    (P : Matrix N k R) (C : Matrix k k R)
    (h : C.map c + Cᵀ + Cᵀ * (Pᵀ * D * P.map c) * C.map c = 0) :
    (rankMat c D P C)ᵀ * D * (rankMat c D P C).map c = D := by
  have hDm : D.map c = Dᵀ := by ext i j; simp [hD]
  have hPP : (P.map c).map c = P := by ext i j; simp [hc]
  have hmap : (rankMat c D P C).map c = 1 + P.map c * C.map c * (Pᵀ * D) := by
    rw [rankMat, Matrix.map_add, Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.map_mul, hDm, hPP]
    all_goals first | simp [Matrix.transpose_mul] | exact fun a b => map_add c a b
  have htr : (rankMat c D P C)ᵀ = 1 + D * P.map c * Cᵀ * Pᵀ := by
    simp [rankMat, Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_assoc]
  have : (rankMat c D P C)ᵀ * D * (rankMat c D P C).map c =
      D + D * P.map c * (C.map c + Cᵀ + Cᵀ * (Pᵀ * D * P.map c) * C.map c) * (Pᵀ * D) := by
    rw [hmap, htr]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [this, h]; simp

end Rank

end GlobalTheory.MixedPlane

namespace GlobalTheory.MixedPlane

open Matrix

section Plane

variable {R : Type} [CommRing R] {n m : ℕ}

theorem dbl_form (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (v₁ v₂ w₁ w₂ : Fin n → R) :
    Sum.elim v₁ v₂ ⬝ᵥ dbl J *ᵥ (fun r => c (Sum.elim w₁ w₂ r)) =
      v₁ ⬝ᵥ J *ᵥ (fun i => c (w₁ i)) - v₂ ⬝ᵥ J *ᵥ (fun i => c (w₂ i)) := by
  have : (fun r => c (Sum.elim w₁ w₂ r)) = Sum.elim (fun i => c (w₁ i)) (fun i => c (w₂ i)) := by
    funext r; cases r <;> rfl
  rw [this, dbl, fromBlocks_mulVec]
  simp [sumElim_dotProduct_sumElim, neg_mulVec, sub_eq_add_neg]

theorem form_zero (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    v ⬝ᵥ J *ᵥ (fun i => c ((0 : Fin n → R) i)) = 0 := by
  have : (fun i => c ((0 : Fin n → R) i)) = 0 := by funext i; simp
  rw [this, mulVec_zero, dotProduct_zero]

theorem form_zero' (J : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    v ⬝ᵥ J *ᵥ (fun _ => (0 : R)) = 0 := by
  have : (fun _ : Fin n => (0 : R)) = 0 := rfl
  rw [this, mulVec_zero, dotProduct_zero]

theorem herm_swap (c : R →+* R) (hc : ∀ r, c (c r) = r) (J : Matrix (Fin n) (Fin n) R)
    (hJ : ∀ i j, c (J j i) = J i j) (v w : Fin n → R) :
    w ⬝ᵥ J *ᵥ (fun i => c (v i)) = c (v ⬝ᵥ J *ᵥ fun i => c (w i)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, hc, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def Pm (x y : Fin n → R) : Matrix (Fin n ⊕ Fin n) (Fin 4) R :=
  Matrix.of fun r i => (![Sum.elim x 0, Sum.elim y 0, Sum.elim 0 x, Sum.elim 0 y] : Fin 4 → Fin n ⊕ Fin n → R) i r

def gram0 : Matrix (Fin 4) (Fin 4) R := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]

def Cm (h : R) : Matrix (Fin 4) (Fin 4) R := !![0, 0, h, 0; -h, 0, 0, -1; 0, 1, -h, 1; -h, 0, 1, -1]

def Cm' (h : R) : Matrix (Fin 4) (Fin 4) R := !![0, -h, 0, -h; 0, 0, 1, 0; h, 0, -h, 1; 0, -1, 1, -1]

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {x y : Fin n → R}

theorem Pm_gram (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j)
    (hXX : x ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0) (hYY : y ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0)
    (hXY : x ⬝ᵥ J *ᵥ (fun i => c (y i)) = 1) :
    (Pm x y)ᵀ * dbl J * (Pm x y).map c = gram0 := by
  have hyx : y ⬝ᵥ J *ᵥ (fun i => c (x i)) = 1 := by rw [herm_swap c hc J hJ x y, hXY, map_one]
  ext i j
  rw [gram_entry]
  fin_cases i <;> fin_cases j <;> simp [Pm, gram0, dbl_form, form_zero, form_zero', hXX, hYY, hXY, hyx]

theorem Cm_unitary (h : R) (h2 : 2 * h = 1) (hch : c h = h) :
    (Cm h).map c + (Cm h)ᵀ + (Cm h)ᵀ * gram0 * (Cm h).map c = 0 := by
  have hm : (Cm h).map c = Cm h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Cm, hch]
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cm, gram0, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination h2 | linear_combination -h2 | linear_combination h * h2 |
      linear_combination -h * h2

theorem gram_matrix_transpose : (gram0 : Matrix (Fin 4) (Fin 4) R)ᵀ = gram0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Cm_mul (h : R) (h2 : 2 * h = 1) : Cm h + Cm' h + Cm h * (gram0 : Matrix (Fin 4) (Fin 4) R)ᵀ * Cm' h = 0 := by
  rw [gram_matrix_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cm, Cm', gram0, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination h2 | linear_combination -h2 | linear_combination h * h2 |
      linear_combination -h * h2

theorem Cm_mul' (h : R) (h2 : 2 * h = 1) : Cm' h + Cm h + Cm' h * (gram0 : Matrix (Fin 4) (Fin 4) R)ᵀ * Cm h = 0 := by
  rw [gram_matrix_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cm, Cm', gram0, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination h2 | linear_combination -h2 | linear_combination h * h2 |
      linear_combination -h * h2

end Plane

end GlobalTheory.MixedPlane

namespace GlobalTheory.MixedPlane

open Matrix

section Cols

variable {R : Type} [CommRing R] {n m : ℕ}

theorem rankMat_mulVec {N k : Type} [Fintype N] [DecidableEq N] [Fintype k] [DecidableEq k] (c : R →+* R)
    (D : Matrix N N R) (P : Matrix N k R) (C : Matrix k k R) (v : N → R) :
    rankMat c D P C *ᵥ v = v + P *ᵥ (C *ᵥ (fun j => v ⬝ᵥ D *ᵥ fun r => c (P r j))) := by
  rw [rankMat, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  congr
  funext j
  rw [mulVec_transpose, ← vecMul_vecMul, dotProduct_mulVec]; rfl

theorem Pm_mulVec (x y : Fin n → R) (w : Fin 4 → R) :
    Pm x y *ᵥ w = Sum.elim (w 0 • x + w 1 • y) (w 2 • x + w 3 • y) := by
  funext r; cases r <;> simp [Pm, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem Pm_form (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (x y v₁ v₂ : Fin n → R) :
    (fun j => Sum.elim v₁ v₂ ⬝ᵥ dbl J *ᵥ fun r => c (Pm x y r j)) =
      ![v₁ ⬝ᵥ J *ᵥ (fun i => c (x i)), v₁ ⬝ᵥ J *ᵥ (fun i => c (y i)), -(v₂ ⬝ᵥ J *ᵥ (fun i => c (x i))),
        -(v₂ ⬝ᵥ J *ᵥ (fun i => c (y i)))] := by
  funext j; fin_cases j <;> simp [Pm, dbl_form, form_zero, form_zero']

def colF (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) : Fin m ⊕ Fin 2 → Fin n ⊕ Fin n → R :=
  Sum.elim (fun j => Sum.elim (fun r => ι r j) (fun r => ι r j)) ![Sum.elim x 0, Sum.elim 0 x]

def colS (x y : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) : Fin m ⊕ Fin 2 → Fin n → R :=
  Sum.elim (fun j r => ι r j) ![x, y]

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin m) R}

theorem g_colF (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j)
    (hXX : x ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0) (hYY : y ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0)
    (hXY : x ⬝ᵥ J *ᵥ (fun i => c (y i)) = 1)
    (hιx : ∀ j, (fun r => ι r j) ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0)
    (hιy : ∀ j, (fun r => ι r j) ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0) (h : R) (k : Fin m ⊕ Fin 2) :
    rankMat c (dbl J) (Pm x y) (Cm h) *ᵥ colF x ι k = Sum.elim (colS x y ι k) (colS x y ι k) := by
  rcases k with j | i
  · simp only [colF, colS, Sum.elim_inl]
    rw [rankMat_mulVec, Pm_form, hιx, hιy]
    simp only [neg_zero]
    rw [show (![0, 0, 0, 0] : Fin 4 → R) = 0 by ext i; fin_cases i <;> rfl, mulVec_zero, mulVec_zero]
    funext r; cases r <;> simp
  · fin_cases i
    · simp only [colF, colS, Sum.elim_inr]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [rankMat_mulVec, Pm_form, Pm_mulVec, hXX, hXY]
      funext r; cases r <;> simp [Cm, mulVec, dotProduct, Fin.sum_univ_four]
    · simp only [colF, colS, Sum.elim_inr]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [rankMat_mulVec, Pm_form, Pm_mulVec, hXX, hXY]
      funext r; cases r <;> simp [Cm, mulVec, dotProduct, Fin.sum_univ_four]

theorem mul_of' {N κ : Type} [Fintype N] (M : Matrix N N R) (f : κ → N → R) :
    M * Matrix.of (fun r k => f k r) = Matrix.of fun r k => (M *ᵥ f k) r := by
  ext r k; rfl

theorem md_colF (M : Matrix (Fin n) (Fin n) R) (t : R) (hMx : M *ᵥ x = t • x) (hMι : M * ι = ι)
    (k : Fin m ⊕ Fin 2) :
    fromBlocks M 0 0 1 *ᵥ colF x ι k = (Sum.elim 1 ![t, 1] k : R) • colF x ι k := by
  have hcol : ∀ j, M *ᵥ (fun r => ι r j) = fun r => ι r j := fun j => by
    funext r; exact congrFun (congrFun hMι r) j
  rcases k with j | i
  · simp only [colF, Sum.elim_inl, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero,
      zero_add, one_mulVec, hcol, Pi.one_apply, one_smul]
  · fin_cases i
    · funext r; cases r <;> simp [colF, fromBlocks_mulVec, hMx]
    · funext r; cases r <;> simp [colF, fromBlocks_mulVec]

end Cols

end GlobalTheory.MixedPlane

namespace GlobalTheory.MixedPlane

open Matrix

section Assemble

variable {R : Type} [CommRing R] {n m : ℕ}

theorem colF_cols {d : ℕ} (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) (e : Fin m ⊕ Fin 2 ≃ Fin n)
    (z : Matrix (Fin d) (Fin n) R) :
    ∃ (y₁ y₂ : Fin d → R) (u : Matrix (Fin d) (Fin m) R),
      z * (Matrix.of fun r k => colF x ι (e.symm k) r)ᵀ =
        fromCols (vecMulVec y₁ x + u * ιᵀ) (vecMulVec y₂ x + u * ιᵀ) := by
  refine ⟨fun i => z i (e (Sum.inr 0)), fun i => z i (e (Sum.inr 1)), fun i j => z i (e (Sum.inl j)), ?_⟩
  ext i r
  rcases r with r | r
  · simp only [Matrix.mul_apply, transpose_apply, of_apply, fromCols_apply_inl]
    rw [← e.sum_comp]
    simp [Fintype.sum_sum_type, colF, vecMulVec_apply]
    rw [add_comm]; rfl
  · simp only [Matrix.mul_apply, transpose_apply, of_apply, fromCols_apply_inr]
    rw [← e.sum_comp]
    simp [Fintype.sum_sum_type, colF, vecMulVec_apply]
    rw [add_comm]; rfl

theorem g_mul_cols {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin m) R}
    (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j)
    (hXX : x ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0) (hYY : y ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0)
    (hXY : x ⬝ᵥ J *ᵥ (fun i => c (y i)) = 1)
    (hιx : ∀ j, (fun r => ι r j) ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0)
    (hιy : ∀ j, (fun r => ι r j) ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0) (h : R) (e : Fin m ⊕ Fin 2 ≃ Fin n) :
    rankMat c (dbl J) (Pm x y) (Cm h) * (Matrix.of fun r k => colF x ι (e.symm k) r) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R) * (Matrix.of fun r k => colS x y ι (e.symm k) r) := by
  rw [mul_of']
  ext r k
  rw [of_apply, g_colF hc hJ hXX hYY hXY hιx hιy h]
  rcases r with r | r <;> simp [diagCols, Matrix.mul_apply, fromRows_apply_inl, fromRows_apply_inr, one_apply]

end Assemble

end GlobalTheory.MixedPlane

namespace GlobalTheory.MixedPlane

open Matrix

section Det

variable {K : Type} [Field K] {n m : ℕ}

theorem colS_det_ne (c : K →+* K) (hc : ∀ r, c (c r) = r) {J : Matrix (Fin n) (Fin n) K}
    (hJ : ∀ i j, c (J j i) = J i j) {x y : Fin n → K} {ι : Matrix (Fin n) (Fin m) K}
    (hXX : x ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0) (hYY : y ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0)
    (hXY : x ⬝ᵥ J *ᵥ (fun i => c (y i)) = 1)
    (hιx : ∀ j, (fun r => ι r j) ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0)
    (hιy : ∀ j, (fun r => ι r j) ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0)
    (hJ₁ : (ιᵀ * J * ι.map c).det ≠ 0) (e : Fin m ⊕ Fin 2 ≃ Fin n) :
    (Matrix.of fun r k => colS x y ι (e.symm k) r).det ≠ 0 := by
  have hyx : y ⬝ᵥ J *ᵥ (fun i => c (x i)) = 1 := by rw [herm_swap c hc J hJ x y, hXY, map_one]
  set S₀ : Matrix (Fin n) (Fin m ⊕ Fin 2) K := Matrix.of fun r k => colS x y ι k r with hS₀
  have hG : S₀ᵀ * J * S₀.map c =
      fromBlocks (ιᵀ * J * ι.map c) 0 (S₀ᵀ * J * S₀.map c).toBlocks₂₁ !![0, 1; 1, 0] := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rw [fromBlocks_apply₁₂, gram_entry]
      fin_cases j
      · simpa [hS₀, colS] using hιx i
      · simpa [hS₀, colS] using hιy i
    · rfl
    · rw [fromBlocks_apply₂₂, gram_entry]
      fin_cases i <;> fin_cases j <;> simp [hS₀, colS, hXX, hYY, hXY, hyx]
  have hdet : (S₀ᵀ * J * S₀.map c).det = -(ιᵀ * J * ι.map c).det := by
    rw [hG, det_fromBlocks_zero₁₂]; simp [det_fin_two]
  have hS : (Matrix.of fun r k => colS x y ι (e.symm k) r)ᵀ * J * (Matrix.of fun r k => colS x y ι (e.symm k) r).map c =
      (S₀ᵀ * J * S₀.map c).submatrix e.symm e.symm := by
    ext i j; rfl
  intro h0
  have h1 := congrArg Matrix.det hS
  rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul, det_submatrix_equiv_self, hdet] at h1
  exact hJ₁ (neg_eq_zero.mp h1.symm)

theorem det_ne_of_sig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hB : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; rfl
  intro h0
  have h1 := congrArg Matrix.det hB
  rw [det_mul, det_mul, h0, mul_zero, zero_mul, det_submatrix_equiv_self, det_fromBlocks_zero₂₁] at h1
  simp [det_neg] at h1
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) h1.symm

end Det

end GlobalTheory.MixedPlane

open Matrix in

theorem GlobalTheory.MixedPlane.exists_mixed_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ (t : (AE F E)ˣ) (m : UA σ X.J), IsLevi (W₁ := X₁) H t 1 m →
      ∃ (Cy : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) (md : UG (cA σ) (dbl (incM F X.J))) (T : GL (Fin n) (AE F E))
        (g : UG (cA σ) (dbl (incM F X.J))) (S : GL (Fin n) (AE F E)),
        (∀ z : Matrix (Fin d) (Fin n) (AE F E), ∃ (y₁ y₂ : Fin d → AE F E) (u : Matrix (Fin d) (Fin n₁) (AE F E)),
          z * Cyᵀ = Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H.x) + u * (incM F H.ι)ᵀ)
            (Matrix.vecMulVec y₂ (incV F H.x) + u * (incM F H.ι)ᵀ)) ∧
        ((md : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
          Matrix.fromBlocks (mat m) 0 0 1 ∧
        ((md : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Cy = Cy * (T : Matrix (Fin n) (Fin n) (AE F E)) ∧
        Matrix.GeneralLinearGroup.det T = t ∧
        ((g : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Cy =
          (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (S : Matrix (Fin n) (Fin n) (AE F E)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hA hP₁ t m hL
  have hσ := GlobalTheory.LeviTorus.sigma_invol hP.base.cm

  have hJE : ∀ i j, σ.toRingHom (X.J j i) = X.J i j := hP.herm.herm
  have hσE : ∀ a, σ.toRingHom (σ.toRingHom a) = a := hσ
  have hιxE : ∀ j, form σ X.J (fun r => H.ι r j) H.x = 0 := fun j => by
    have h := (hA.orth (Pi.single j 1)).1
    rwa [mulVec_single_one] at h
  have hιyE : ∀ j, form σ X.J (fun r => H.ι r j) H.y = 0 := fun j => by
    have h := (hA.orth (Pi.single j 1)).2
    rwa [mulVec_single_one] at h
  have hJ₁ : (H.ιᵀ * X.J * H.ι.map σ.toRingHom).det ≠ 0 := by
    have hg : H.ιᵀ * X.J * H.ι.map σ.toRingHom = X₁.J := hA.gram
    rw [hg]
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := GlobalTheory.MixedPlane.det_ne_of_sig _ (hP₁.herm.sig w)
    intro h0; apply h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hSE := GlobalTheory.MixedPlane.colS_det_ne σ.toRingHom hσE hJE (x := H.x) (y := H.y) (ι := H.ι) hA.xx hA.yy hA.xy
    hιxE hιyE hJ₁ (finSumFinEquiv.trans (finCongr hA.rank.symm))

  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hc : ∀ a, c (c a) = a := GlobalTheory.LeviTorus.cA_invol hσ
  have hJ : ∀ i j, c (incM F X.J j i) = incM F X.J i j := by
    intro i j
    simp only [c, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorus.cA_incl, hP.herm.herm i j]
  have hXX : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fun i => c (incV F H.x i)) = 0 := by
    rw [show (fun i => c (incV F H.x i)) = fun i => cA σ (incV F H.x i) from rfl, GlobalTheory.LeviTorus.form_incl, hA.xx, map_zero]
  have hYY : incV F H.y ⬝ᵥ incM F X.J *ᵥ (fun i => c (incV F H.y i)) = 0 := by
    rw [show (fun i => c (incV F H.y i)) = fun i => cA σ (incV F H.y i) from rfl, GlobalTheory.LeviTorus.form_incl, hA.yy, map_zero]
  have hXY : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fun i => c (incV F H.y i)) = 1 := by
    rw [show (fun i => c (incV F H.y i)) = fun i => cA σ (incV F H.y i) from rfl, GlobalTheory.LeviTorus.form_incl, hA.xy, map_one]
  have hιx : ∀ j, (fun r => incM F H.ι r j) ⬝ᵥ incM F X.J *ᵥ (fun i => c (incV F H.x i)) = 0 := fun j => by
    have h := GlobalTheory.LeviTorus.form_incl σ X.J (fun r => H.ι r j) H.x
    rw [hιxE j, map_zero] at h
    exact h
  have hιy : ∀ j, (fun r => incM F H.ι r j) ⬝ᵥ incM F X.J *ᵥ (fun i => c (incV F H.y i)) = 0 := fun j => by
    have h := GlobalTheory.LeviTorus.form_incl σ X.J (fun r => H.ι r j) H.y
    rw [hιyE j, map_zero] at h
    exact h
  set hf : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhf
  have h2 : 2 * hf = 1 := by
    rw [hhf, show (2 : AE F E) = inclR (F := F) (AF F) (2 : E) from (map_ofNat _ 2).symm, ← map_mul,
      mul_inv_cancel₀ two_ne_zero, map_one]
  have hch : c hf = hf := by
    simp only [c, hhf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.LeviTorus.cA_incl, map_inv₀, map_ofNat]
  set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hA.rank.symm) with he
  have hD : ∀ i j, c (dbl (incM F X.J) j i) = dbl (incM F X.J) i j := by
    intro i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl, hJ]
  have hgram := GlobalTheory.MixedPlane.Pm_gram hc hJ hXX hYY hXY

  let gU : GL (Fin n ⊕ Fin n) (AE F E) :=
    ⟨GlobalTheory.MixedPlane.rankMat c (dbl (incM F X.J)) (GlobalTheory.MixedPlane.Pm (incV F H.x) (incV F H.y)) (GlobalTheory.MixedPlane.Cm hf),
      GlobalTheory.MixedPlane.rankMat c (dbl (incM F X.J)) (GlobalTheory.MixedPlane.Pm (incV F H.x) (incV F H.y)) (GlobalTheory.MixedPlane.Cm' hf),
      GlobalTheory.MixedPlane.rankMat_mul _ _ _ _ _ (by rw [hgram]; exact GlobalTheory.MixedPlane.Cm_mul hf h2),
      GlobalTheory.MixedPlane.rankMat_mul _ _ _ _ _ (by rw [hgram]; exact GlobalTheory.MixedPlane.Cm_mul' hf h2)⟩
  have gmem : gU ∈ UG (cA σ) (dbl (incM F X.J)) :=
    GlobalTheory.MixedPlane.rankMat_unitary c hc _ hD _ _ (by rw [hgram]; exact GlobalTheory.MixedPlane.Cm_unitary hf h2 hch)

  have hm : (mat m)ᵀ * incM F X.J * (mat m).map (cA σ) = incM F X.J := m.2
  have hmi : mat m * mat m⁻¹ = 1 := Units.mul_inv m.1
  have him : mat m⁻¹ * mat m = 1 := Units.inv_mul m.1
  let mdU : GL (Fin n ⊕ Fin n) (AE F E) :=
    ⟨fromBlocks (mat m) 0 0 1, fromBlocks (mat m⁻¹) 0 0 1, by rw [fromBlocks_multiply]; simp [hmi],
      by rw [fromBlocks_multiply]; simp [him]⟩
  have mdmem : mdU ∈ UG (cA σ) (dbl (incM F X.J)) := by
    show (fromBlocks (mat m) 0 0 1)ᵀ * dbl (incM F X.J) * (fromBlocks (mat m) 0 0 1).map (cA σ) = dbl (incM F X.J)
    rw [dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hm]

  let du : Fin n₁ ⊕ Fin 2 → (AE F E)ˣ := Sum.elim 1 ![t, 1]
  let TU : GL (Fin n) (AE F E) :=
    ⟨diagonal fun k => (du (e.symm k) : AE F E), diagonal fun k => ((du (e.symm k))⁻¹ : (AE F E)ˣ),
      by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

  have hSmap : (Matrix.of fun r k => GlobalTheory.MixedPlane.colS (incV F H.x) (incV F H.y) (incM F H.ι) (e.symm k) r) =
      (Matrix.of fun r k => GlobalTheory.MixedPlane.colS H.x H.y H.ι (e.symm k) r).map (inclR (F := F) (AF F)) := by
    ext r k
    simp only [of_apply, Matrix.map_apply]
    generalize e.symm k = k'
    rcases k' with j | i
    · rfl
    · fin_cases i <;> rfl
  have hSunit : IsUnit (Matrix.of fun r k =>
      GlobalTheory.MixedPlane.colS (incV F H.x) (incV F H.y) (incM F H.ι) (e.symm k) r).det := by
    rw [hSmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hSE).map _
  let SU : GL (Fin n) (AE F E) := ((Matrix.isUnit_iff_isUnit_det _).mpr hSunit).unit
  refine ⟨Matrix.of fun r k => GlobalTheory.MixedPlane.colF (incV F H.x) (incM F H.ι) (e.symm k) r, ⟨mdU, mdmem⟩, TU,
    ⟨gU, gmem⟩, SU, ?_, rfl, ?_, ?_, ?_⟩
  · exact fun z => GlobalTheory.MixedPlane.colF_cols _ _ e z
  · have hMx : mat m *ᵥ incV F H.x = t.1 • incV F H.x := hL.1
    have hMι : mat m * incM F H.ι = incM F H.ι := by rw [hL.2.2]; exact Matrix.mul_one _
    show fromBlocks (mat m) 0 0 1 * _ = _ * diagonal _
    rw [GlobalTheory.MixedPlane.mul_of']
    ext r k
    rw [of_apply, GlobalTheory.MixedPlane.md_colF (mat m) t.1 hMx hMι, mul_diagonal, of_apply]
    generalize e.symm k = k'
    rcases k' with j | i
    · simp [du]
    · fin_cases i <;> simp [du, mul_comm]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, TU, det_diagonal]
    rw [Equiv.prod_comp e.symm (fun k => (du k : AE F E))]
    simp [du, Fintype.prod_sum_type]
  · show GlobalTheory.MixedPlane.rankMat c (dbl (incM F X.J)) (GlobalTheory.MixedPlane.Pm (incV F H.x) (incV F H.y)) (GlobalTheory.MixedPlane.Cm hf) * _ =
      _ * (Matrix.of fun r k => GlobalTheory.MixedPlane.colS (incV F H.x) (incV F H.y) (incM F H.ι) (e.symm k) r)
    exact GlobalTheory.MixedPlane.g_mul_cols hc hJ hXX hYY hXY hιx hιy hf e
