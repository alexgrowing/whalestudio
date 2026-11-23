import Mathlib

import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open Matrix TensorProduct GroundTheory.Automorphic

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

local infixl:70 " ⬝ " => @HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid

variable (K E R) in

def cT {m n : Type*} (M : Matrix m n (R ⊗[K] E)) : Matrix n m (R ⊗[K] E) := Matrix.transpose (M.map (conjBase K E R))

theorem conjBase_conjBase (z : (R ⊗[K] E)) : conjBase K E R (conjBase K E R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [conjBase_tmul, conj_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjBase_smul (c : K) (z : (R ⊗[K] E)) : conjBase K E R (c • z) = c • conjBase K E R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [conjBase_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem cT_cT {m n : Type*} (M : Matrix m n (R ⊗[K] E)) : cT K E R (cT K E R M) = M := by
  ext i j
  simp [cT, conjBase_conjBase]

theorem cT_mul {l m n : Type*} [Fintype m] (M : Matrix l m (R ⊗[K] E)) (N : Matrix m n (R ⊗[K] E)) :
    cT K E R (M * N) = cT K E R N * cT K E R M := by
  rw [cT, cT, cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add {m n : Type*} (M N : Matrix m n (R ⊗[K] E)) :
    cT K E R (M + N) = cT K E R M + cT K E R N := by
  rw [cT, cT, cT, Matrix.map_add _ (map_add _), Matrix.transpose_add]

theorem cT_sub {m n : Type*} (M N : Matrix m n (R ⊗[K] E)) :
    cT K E R (M - N) = cT K E R M - cT K E R N := by
  rw [cT, cT, cT, Matrix.map_sub _ (map_sub _), Matrix.transpose_sub]

theorem cT_neg {m n : Type*} (M : Matrix m n (R ⊗[K] E)) :
    cT K E R (-M) = -cT K E R M := by
  rw [cT, cT, Matrix.map_neg _ (map_neg _), Matrix.transpose_neg]

theorem cT_zero {m n : Type*} : cT K E R (0 : Matrix m n (R ⊗[K] E)) = 0 := by
  rw [cT, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]

theorem cT_one {m : Type*} [DecidableEq m] : cT K E R (1 : Matrix m m (R ⊗[K] E)) = 1 := by
  rw [cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem cT_smul {m n : Type*} (c : K) (M : Matrix m n (R ⊗[K] E)) :
    cT K E R (c • M) = c • cT K E R M := by
  ext i j
  simp [cT, conjBase_smul]

theorem det_cT {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m (R ⊗[K] E)) :
    (cT K E R M).det = conjBase K E R M.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]

variable (K R) in

def Hm (H : Matrix ι ι E) : Matrix ι ι (R ⊗[K] E) :=
  H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] (R ⊗[K] E))

theorem framePair_eq (H : Matrix ι ι E) {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E))
    (Y : Matrix ι (Fin q) (R ⊗[K] E)) :
    framePair K E R H X Y = cT K E R X ⬝ Hm K R H ⬝ Y := rfl

theorem cT_Hm {H : Matrix ι ι E} (hH : IsHermitianFor (conjHom K E) H) :
    cT K E R (Hm K R H) = Hm K R H := by
  ext i j
  have := congrFun (congrFun hH i) j
  simp only [Matrix.transpose_apply, Matrix.map_apply] at this
  simp only [cT, Hm, Matrix.transpose_apply, Matrix.map_apply,
    Algebra.TensorProduct.includeRight_apply, conjBase_tmul]
  rw [← this]
  rfl

variable {H : Matrix ι ι E}

theorem cT_framePair (hH : IsHermitianFor (conjHom K E) H) {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E))
    (Y : Matrix ι (Fin q) (R ⊗[K] E)) : cT K E R (framePair K E R H X Y) = framePair K E R H Y X := by
  rw [framePair_eq, framePair_eq, cT_mul, cT_mul, cT_cT, cT_Hm hH, Matrix.mul_assoc]

theorem framePair_add_right {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E)) (Y Y' : Matrix ι (Fin q) (R ⊗[K] E)) :
    framePair K E R H X (Y + Y') = framePair K E R H X Y + framePair K E R H X Y' := by
  rw [framePair_eq, framePair_eq, framePair_eq, Matrix.mul_add]

theorem framePair_add_left {q : ℕ} (X X' : Matrix ι (Fin p) (R ⊗[K] E)) (Y : Matrix ι (Fin q) (R ⊗[K] E)) :
    framePair K E R H (X + X') Y = framePair K E R H X Y + framePair K E R H X' Y := by
  rw [framePair_eq, framePair_eq, framePair_eq, cT_add, Matrix.add_mul, Matrix.add_mul]

theorem framePair_mul_right {q r : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E)) (Y : Matrix ι (Fin q) (R ⊗[K] E))
    (d : Matrix (Fin q) (Fin r) (R ⊗[K] E)) :
    framePair K E R H X (Y * d) = framePair K E R H X Y * d := by
  simp only [framePair_eq, Matrix.mul_assoc]

theorem framePair_mul_left {q r : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E)) (d : Matrix (Fin p) (Fin r) (R ⊗[K] E))
    (Y : Matrix ι (Fin q) (R ⊗[K] E)) :
    framePair K E R H (X * d) Y = cT K E R d * framePair K E R H X Y := by
  rw [framePair_eq, framePair_eq, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

theorem gram_add_mul (hH : IsHermitianFor (conjHom K E) H) (X Z : Matrix ι (Fin p) (R ⊗[K] E))
    (T : Matrix (Fin p) (Fin p) (R ⊗[K] E)) :
    gram K E R H (X + Z * T) = gram K E R H X + cT K E R (framePair K E R H Z X) * T +
      cT K E R T * framePair K E R H Z X + cT K E R T * gram K E R H Z * T := by
  simp only [gram, framePair_add_left, framePair_add_right, framePair_mul_left,
    framePair_mul_right, cT_framePair hH, Matrix.mul_assoc, Matrix.add_mul]
  abel

theorem framePair_add_iso {Z : Matrix ι (Fin p) (R ⊗[K] E)} (hZ : gram K E R H Z = 0)
    (X : Matrix ι (Fin p) (R ⊗[K] E)) (d : Matrix (Fin p) (Fin p) (R ⊗[K] E)) :
    framePair K E R H Z (X + Z * d) = framePair K E R H Z X := by
  rw [framePair_add_right, framePair_mul_right, show framePair K E R H Z Z = gram K E R H Z from rfl,
    hZ, Matrix.zero_mul, add_zero]

def shiftT (Z X : Matrix ι (Fin p) (R ⊗[K] E)) (S : Matrix (Fin p) (Fin p) (R ⊗[K] E)) : Matrix (Fin p) (Fin p) (R ⊗[K] E) :=
  (cT K E R (framePair K E R H Z X))⁻¹ * ((2 : K)⁻¹ • S)

theorem gram_add_shiftT [CharZero K] (hH : IsHermitianFor (conjHom K E) H)
    {Z : Matrix ι (Fin p) (R ⊗[K] E)} (hZ : gram K E R H Z = 0) {X : Matrix ι (Fin p) (R ⊗[K] E)}
    (hX : IsUnit (framePair K E R H Z X).det) {S : Matrix (Fin p) (Fin p) (R ⊗[K] E)}
    (hS : cT K E R S = S) :
    gram K E R H (X + Z * shiftT (H := H) Z X S) = gram K E R H X + S := by
  set a := framePair K E R H Z X with ha
  have hcu : IsUnit (cT K E R a).det := by
    rw [det_cT]
    exact hX.map _
  have h1 : cT K E R a * shiftT (H := H) Z X S = (2 : K)⁻¹ • S := by
    rw [shiftT, ← ha, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcu, Matrix.one_mul]
  have h2 : cT K E R (shiftT (H := H) Z X S) * a = (2 : K)⁻¹ • S := by
    have := congrArg (cT K E R) h1
    rwa [cT_mul, cT_cT, cT_smul, hS] at this
  rw [gram_add_mul hH, hZ, Matrix.mul_zero, Matrix.zero_mul, add_zero, ← ha, h1, h2,
    add_assoc, ← add_smul]
  congr 1
  have : ((2 : K)⁻¹ + (2 : K)⁻¹) = 1 := by
    rw [← two_mul, mul_inv_cancel₀ (two_ne_zero)]
  rw [this, one_smul]

theorem isFree_of_isUnit {Z X : Matrix ι (Fin p) (R ⊗[K] E)} (hX : IsUnit (framePair K E R H Z X).det) :
    IsFree X := by
  refine ⟨(framePair K E R H Z X)⁻¹ ⬝ (cT K E R Z ⬝ Hm K R H), ?_⟩
  rw [Matrix.mul_assoc, ← framePair_eq, Matrix.nonsing_inv_mul _ hX]

theorem exists_partner [CharZero K] (hH : IsHermitianFor (conjHom K E) H) (hHu : IsUnit H.det)
    {Y : Matrix ι (Fin p) (R ⊗[K] E)} (hY : IsFree Y) (hY0 : gram K E R H Y = 0) :
    ∃ Z : Matrix ι (Fin p) (R ⊗[K] E), gram K E R H Z = 0 ∧ framePair K E R H Z Y = 1 := by
  obtain ⟨L, hL⟩ := hY
  have hHmu : IsUnit (Hm K R H).det := by
    have hdet : (Hm K R H).det = (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E) H.det := by
      rw [Hm, AlgHom.map_det]
      rfl
    rw [hdet]
    exact hHu.map _
  set Z' := (Hm K R H)⁻¹ * cT K E R L with hZ'
  have hYZ' : framePair K E R H Y Z' = 1 := by
    rw [framePair_eq, hZ', ← Matrix.mul_assoc, Matrix.mul_assoc (cT K E R Y),
      Matrix.mul_nonsing_inv _ hHmu, Matrix.mul_one, ← cT_mul, hL, cT_one]
  have hZ'Y : framePair K E R H Z' Y = 1 := by
    rw [← cT_framePair hH, hYZ', cT_one]
  set S := gram K E R H Z' with hS
  have hSh : cT K E R S = S := cT_framePair hH Z' Z'
  refine ⟨Z' + Y * (-((2 : K)⁻¹ • S)), ?_, ?_⟩
  · have hT : cT K E R (-((2 : K)⁻¹ • S)) = -((2 : K)⁻¹ • S) := by
      rw [cT_neg, cT_smul, hSh]
    have h2 : ((2 : K)⁻¹ + (2 : K)⁻¹) = 1 := by
      rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
    rw [gram_add_mul hH, hY0, hYZ', cT_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, ← hS, hT, add_assoc, ← neg_add, ← add_smul, h2, one_smul,
      add_neg_cancel]
  · rw [framePair_add_left, framePair_mul_left, show framePair K E R H Y Y = gram K E R H Y from rfl,
      hY0, Matrix.mul_zero, add_zero, hZ'Y]

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
