import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

def ct (x : U.RC k j (1 + ρ)) : Fin j → ℂ := fun a => x.1 (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) a

def cm (x : U.RC k j (1 + ρ)) : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ :=
  fun v a => x.1 (U.eB k 1 ρ (Sum.inl (Sum.inr v))) a

def cb (x : U.RC k j (1 + ρ)) : Fin j → ℂ := fun a => x.1 (U.eB k 1 ρ (Sum.inr 0)) a

def cy (y : U.RC k 1 ρ) : Fin (2 * ρ + k + 1) → ℂ := fun v => y.1 v 0

def dy (y : U.RC k 1 ρ) : ℝ := y.2.2 0

def r0 (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : Fin j → ℂ :=
  ct x - (1 / 2 : ℂ) • Matrix.vecMul (star (cy y)) (Hpk k ρ * cm x) + (Complex.I * (dy y : ℂ)) • cb x

def dlt (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : Matrix (Fin j) (Fin j) ℂ :=
  (1 / 2 : ℂ) • (Matrix.vecMulVec (star (cb x)) (ct x) - Matrix.vecMulVec (star (ct x)) (cb x)) +
    (1 / 2 : ℂ) • (Matrix.vecMulVec (((cm x)ᴴ * Hpk k ρ) *ᵥ cy y) (cb x) -
      (Matrix.vecMulVec (((cm x)ᴴ * Hpk k ρ) *ᵥ cy y) (cb x))ᴴ) +
    (Complex.I * (dy y : ℂ)) • Matrix.vecMulVec (star (cb x)) (cb x)

def SX (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  fun a b => Fin.cases (motive := fun _ => ℂ)
    (Fin.cases (motive := fun _ => ℂ) (Complex.I * (dy y : ℂ)) (fun b' => r0 x y b') b)
    (fun a' => Fin.cases (motive := fun _ => ℂ) (-star (r0 x y a')) (fun b' => U.skewOf x.2 a' b' + dlt x y a' b') b) a

def CX (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : Matrix (Fin (2 * ρ + k + 1)) (Fin (j + 1)) ℂ :=
  fun v b => Fin.cases (motive := fun _ => ℂ) (cy y v) (fun b' => cm x v b' + cy y v * cb x b') b

def XC (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : U.RC k (j + 1) ρ :=
  (fun v b => CX x y v b, (fun p => SX x y p.1.1 p.1.2, fun a => (SX x y a a).im))

def aC (x : U.RC k j (1 + ρ)) : Fin 1 → Fin j → ℂ := fun _ b => -cb x b.rev

def qL (x : U.RC k j (1 + ρ)) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ := U.blk2 1 (Matrix.of (aC x))ᴴ 0 1

theorem hs (k j ρ : ℕ) : 2 * ((j + 1) + ρ) + k + 1 = 2 * (j + (1 + ρ)) + k + 1 := by omega

theorem qX (a : Fin j) : Fin.cast (hs k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inl a.castSucc))) =
    U.eB k j (1 + ρ) (Sum.inl (Sum.inl a)) := by
  ext; simp [Ux3.block_index_first_val]

theorem qE : Fin.cast (hs k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inl (Fin.last j)))) =
    U.eB k j (1 + ρ) (Sum.inl (Sum.inr (U.eB k 1 ρ (Sum.inl (Sum.inl 0))))) := by
  ext; simp [Ux3.block_index_first_val, Ux3.block_index_middle_val]

theorem qV (v : Fin (2 * ρ + k + 1)) : Fin.cast (hs k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inr v))) =
    U.eB k j (1 + ρ) (Sum.inl (Sum.inr (U.eB k 1 ρ (Sum.inl (Sum.inr v))))) := by
  ext; simp [Ux3.block_index_middle_val]; omega

theorem qE' : Fin.cast (hs k j ρ) (U.eB k (j + 1) ρ (Sum.inr 0)) =
    U.eB k j (1 + ρ) (Sum.inl (Sum.inr (U.eB k 1 ρ (Sum.inr 0)))) := by
  ext; simp [Ux3.block_index_middle_val, Ux3.block_index_last_val]; omega

theorem qS (b : Fin j) : Fin.cast (hs k j ρ) (U.eB k (j + 1) ρ (Sum.inr b.succ)) = U.eB k j (1 + ρ) (Sum.inr b) := by
  ext; simp [Ux3.block_index_last_val]; omega

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

theorem sum_over_rank_one_basis {M : Type*} [AddCommMonoid M] (f : Fin (2 * (1 + ρ) + k + 1) → M) :
    ∑ i, f i = f (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) + ∑ v, f (U.eB k 1 ρ (Sum.inl (Sum.inr v))) +
      f (U.eB k 1 ρ (Sum.inr 0)) := by
  rw [← (U.eB k 1 ρ).sum_comp]
  simp [Fintype.sum_sum_type]

theorem hpk1 (p q : U.Ix k 1 ρ) : Hpk k (1 + ρ) (U.eB k 1 ρ p) (U.eB k 1 ρ q) =
    Matrix.fromBlocks (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (Hpk k ρ))
      (Matrix.fromRows (G.wMat 1) 0) (Matrix.fromCols (G.wMat 1) 0) 0 p q := by
  rw [Ux3.hpkBlocks k 1 ρ, Ux3.block3_apply]

theorem weyl_lift_eq_pair : G.wMat 1 = 1 := by ext a b; fin_cases a; fin_cases b; simp [G.wMat]

theorem cH_E (x : U.RC k j (1 + ρ)) (a : Fin j) :
    ((Matrix.of x.1)ᴴ * Hpk k (1 + ρ)) a (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = star (cb x a) := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis]
  simp [hpk1, weyl_lift_eq_pair, cb, Matrix.conjTranspose_apply]

theorem cH_V (x : U.RC k j (1 + ρ)) (a : Fin j) (v : Fin (2 * ρ + k + 1)) :
    ((Matrix.of x.1)ᴴ * Hpk k (1 + ρ)) a (U.eB k 1 ρ (Sum.inl (Sum.inr v))) = ((cm x)ᴴ * Hpk k ρ) a v := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis]
  simp [hpk1, weyl_lift_eq_pair, cm, Matrix.conjTranspose_apply, Matrix.mul_apply]

theorem cH_E' (x : U.RC k j (1 + ρ)) (a : Fin j) :
    ((Matrix.of x.1)ᴴ * Hpk k (1 + ρ)) a (U.eB k 1 ρ (Sum.inr 0)) = star (ct x a) := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis]
  simp [hpk1, weyl_lift_eq_pair, ct, Matrix.conjTranspose_apply]

theorem cHc (x : U.RC k j (1 + ρ)) (a b : Fin j) :
    ((Matrix.of x.1)ᴴ * Hpk k (1 + ρ) * Matrix.of x.1) a b =
      star (cb x a) * ct x b + ((cm x)ᴴ * Hpk k ρ * cm x) a b + star (ct x a) * cb x b := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis, cH_E, cH_E']
  simp only [cH_V]
  rw [Matrix.mul_apply (M := (cm x)ᴴ * Hpk k ρ) (N := cm x)]
  simp [ct, cb, cm]

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

theorem lhs_form (A : B.Mat k (1 + ρ)) (x : U.RC k j (1 + ρ)) :
    U.embG k j (1 + ρ) A * U.Rn k j (1 + ρ) x =
      U.blk3 1 (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k (1 + ρ)))
        (G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k (1 + ρ) * Matrix.of x.1) + U.skewOf x.2))
        0 A (A * Matrix.of x.1) 0 0 1 := by
  rw [Ux3.rn_eq, U.embG, Ux3.block3_mul]
  congr 1 <;> simp

theorem rhs_form (q : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ) (X : U.RC k (j + 1) ρ) :
    U.muP k (j + 1) ρ q * U.Rn k (j + 1) ρ X =
      U.blk3 q (q * -(G.wMat (j + 1) * (Matrix.of X.1)ᴴ * Hpk k ρ))
        (q * (G.wMat (j + 1) * ((-(1 / 2 : ℂ)) • ((Matrix.of X.1)ᴴ * Hpk k ρ * Matrix.of X.1) + U.skewOf X.2)))
        0 1 (Matrix.of X.1) 0 0 (G.wMat (j + 1) * qᴴ⁻¹ * G.wMat (j + 1)) := by
  rw [U.muP, Ux3.rn_eq, Ux3.block3_mul]
  congr 1 <;> simp

def nn (y : U.RC k 1 ρ) : ℂ := Matrix.vecMul (star (cy y)) (Hpk k ρ) ⬝ᵥ cy y

def uu (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : Fin j → ℂ := Matrix.vecMul (Matrix.vecMul (star (cy y)) (Hpk k ρ)) (cm x)

def uu' (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : Fin j → ℂ := ((cm x)ᴴ * Hpk k ρ) *ᵥ cy y

theorem hH (k ρ : ℕ) : (Hpk k ρ)ᴴ = Hpk k ρ := Ux4.hpk_conjTranspose k ρ

theorem star_uu' (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a : Fin j) : star (uu' x y a) = uu x y a := by
  simp only [uu', uu, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_sum, star_mul', star_star, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _
  have := congrFun (congrFun (hH k ρ) l) i
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]; simp; ring

theorem star_nn (y : U.RC k 1 ρ) : star (nn y) = nn y := by
  simp only [nn, Matrix.vecMul, dotProduct, star_sum, star_mul', star_star, Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _
  have := congrFun (congrFun (hH k ρ) l) i
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]; simp; ring

theorem CX_zero (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) : CX x y v 0 = cy y v := rfl
theorem CX_succ (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) (b : Fin j) :
    CX x y v b.succ = cm x v b + cy y v * cb x b := rfl

theorem cXH_zero (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) :
    ((Matrix.of (XC x y).1)ᴴ * Hpk k ρ) 0 v = Matrix.vecMul (star (cy y)) (Hpk k ρ) v := by
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, XC, CX_zero, Matrix.conjTranspose_apply]

theorem cXH_succ (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (b : Fin j) (v : Fin (2 * ρ + k + 1)) :
    ((Matrix.of (XC x y).1)ᴴ * Hpk k ρ) b.succ v =
      ((cm x)ᴴ * Hpk k ρ) b v + star (cb x b) * Matrix.vecMul (star (cy y)) (Hpk k ρ) v := by
  simp only [Matrix.mul_apply, Matrix.vecMul, dotProduct, XC, CX_succ, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_add, star_mul', add_mul, Finset.sum_add_distrib, Finset.mul_sum, Pi.star_apply]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

theorem cXHcX_00 (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) :
    ((Matrix.of (XC x y).1)ᴴ * Hpk k ρ * Matrix.of (XC x y).1) 0 0 = nn y := by
  rw [Matrix.mul_apply]; simp only [cXH_zero]; simp [nn, dotProduct, XC, CX_zero]

theorem cXHcX_0s (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (b : Fin j) :
    ((Matrix.of (XC x y).1)ᴴ * Hpk k ρ * Matrix.of (XC x y).1) 0 b.succ = uu x y b + nn y * cb x b := by
  rw [Matrix.mul_apply]; simp only [cXH_zero]
  simp only [Matrix.of_apply, XC, CX_succ, nn, uu, Matrix.vecMul, dotProduct, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul]
  congr 1; apply Finset.sum_congr rfl; intro i _; (try simp only [Finset.mul_sum, Finset.sum_mul])
  apply Finset.sum_congr rfl; intro l _; ring

theorem hermitian_form_column_succ_zero (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a : Fin j) :
    ((Matrix.of (XC x y).1)ᴴ * Hpk k ρ * Matrix.of (XC x y).1) a.succ 0 = uu' x y a + star (cb x a) * nn y := by
  rw [Matrix.mul_apply]; simp only [cXH_succ]
  simp only [Matrix.of_apply, XC, CX_zero, nn, uu', Matrix.mulVec, Matrix.vecMul, dotProduct, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro i _; (try simp only [Finset.mul_sum, Finset.sum_mul])
  apply Finset.sum_congr rfl; intro l _; ring

theorem cXHcX_ss (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a b : Fin j) :
    ((Matrix.of (XC x y).1)ᴴ * Hpk k ρ * Matrix.of (XC x y).1) a.succ b.succ =
      ((cm x)ᴴ * Hpk k ρ * cm x) a b + uu' x y a * cb x b + star (cb x a) * uu x y b +
        star (cb x a) * nn y * cb x b := by
  rw [Matrix.mul_apply]; simp only [cXH_succ]
  simp only [Matrix.of_apply, XC, CX_succ, nn, uu, uu', Matrix.mulVec, Matrix.vecMul, dotProduct, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro i _; ring

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

theorem dlt_apply (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a b : Fin j) :
    dlt x y a b = (1 / 2 : ℂ) * (star (cb x a) * ct x b - star (ct x a) * cb x b) +
      (1 / 2 : ℂ) * (uu' x y a * cb x b - star (cb x a) * star (uu' x y b)) +
      Complex.I * (dy y : ℂ) * (star (cb x a) * cb x b) := by
  simp only [dlt, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, Pi.star_apply, star_mul']
  simp only [uu']; ring

theorem dlt_skew (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a b : Fin j) : dlt x y a b = -star (dlt x y b a) := by
  rw [dlt_apply, dlt_apply]
  simp only [star_add, star_mul', star_sub, star_star, Complex.star_def, map_mul, map_sub, map_add, Complex.conj_conj,
    Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  ring

theorem skew_skew (q : (G.UT j → ℂ) × (Fin j → ℝ)) (a b : Fin j) : U.skewOf q a b = -star (U.skewOf q b a) := by
  have hs := congrFun (congrFun (Ux2.skewOf_ct q) a) b
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at hs
  rw [hs, neg_neg]

theorem SX_skew (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a b : Fin (j + 1)) : SX x y a b = -star (SX x y b a) := by
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => simp [SX, Complex.star_def, Complex.conj_ofReal]
    | succ b => simp [SX]
  | succ a =>
    cases b using Fin.cases with
    | zero => simp [SX]
    | succ b =>
      simp only [SX, Fin.cases_succ, star_add, neg_add]
      rw [← skew_skew, ← dlt_skew]

theorem SX_diag (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a : Fin (j + 1)) :
    SX x y a a = Complex.I * ((SX x y a a).im : ℂ) := by
  have h := SX_skew x y a a
  apply Complex.ext
  · have h1 := congrArg Complex.re h
    simp at h1 ⊢; linarith
  · simp

theorem skewOf_XC (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) : U.skewOf (XC x y).2 = SX x y := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [Ux2.skewOf_lt _ h]; rfl
  · subst h
    rw [Ux2.skewOf_diag, SX_diag x y a]; rfl
  · rw [skew_skew, Ux2.skewOf_lt _ h, SX_skew x y a b]; rfl

theorem block_two_apply_castSucc_castSucc {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin p) ℂ)
    (D : Matrix (Fin 1) (Fin 1) ℂ) (a b : Fin p) : U.blk2 A B' C D a.castSucc b.castSucc = A a b := by
  simp [U.blk2, Matrix.reindex_apply, show a.castSucc = Fin.castAdd 1 a from rfl,
    show b.castSucc = Fin.castAdd 1 b from rfl]

theorem block_two_apply_castSucc_last {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin p) ℂ)
    (D : Matrix (Fin 1) (Fin 1) ℂ) (a : Fin p) : U.blk2 A B' C D a.castSucc (Fin.last p) = B' a 0 := by
  have : Fin.last p = Fin.natAdd p (0 : Fin 1) := by ext; simp
  simp [U.blk2, Matrix.reindex_apply, show a.castSucc = Fin.castAdd 1 a from rfl, this]

theorem block_two_apply_last_castSucc {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin p) ℂ)
    (D : Matrix (Fin 1) (Fin 1) ℂ) (b : Fin p) : U.blk2 A B' C D (Fin.last p) b.castSucc = C 0 b := by
  have : Fin.last p = Fin.natAdd p (0 : Fin 1) := by ext; simp
  simp [U.blk2, Matrix.reindex_apply, show b.castSucc = Fin.castAdd 1 b from rfl, this]

theorem block_two_apply_last_last {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin p) ℂ)
    (D : Matrix (Fin 1) (Fin 1) ℂ) : U.blk2 A B' C D (Fin.last p) (Fin.last p) = D 0 0 := by
  have : Fin.last p = Fin.natAdd p (0 : Fin 1) := by ext; simp
  simp [U.blk2, Matrix.reindex_apply, this]

theorem qmul_cs {m : Type*} (x : U.RC k j (1 + ρ)) (M : Matrix (Fin (j + 1)) m ℂ) (a : Fin j) (v : m) :
    (qL x * M) a.castSucc v = M a.castSucc v + star (aC x 0 a) * M (Fin.last j) v := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [qL, block_two_apply_castSucc_castSucc, block_two_apply_castSucc_last, Matrix.conjTranspose_apply, Matrix.of_apply]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Matrix.one_apply_ne (Ne.symm hb)]
  · simp

theorem qmul_last {m : Type*} (x : U.RC k j (1 + ρ)) (M : Matrix (Fin (j + 1)) m ℂ) (v : m) :
    (qL x * M) (Fin.last j) v = M (Fin.last j) v := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [qL, block_two_apply_last_castSucc, block_two_apply_last_last]

theorem qL_inv (x : U.RC k j (1 + ρ)) : (qL x)⁻¹ = U.blk2 1 (-(Matrix.of (aC x))ᴴ) 0 1 := by
  apply Matrix.inv_eq_right_inv
  rw [qL, Ux3.symmetricScalarBlockMatrix_mul]
  simp [U.blk2, Matrix.fromBlocks_one]

theorem conj_inverse_block_apply (x : U.RC k j (1 + ρ)) (a b : Fin (j + 1)) :
    (G.wMat (j + 1) * (qL x)ᴴ⁻¹ * G.wMat (j + 1)) a b =
      U.blk2 1 0 (-(Matrix.of (aC x))) 1 a.rev b.rev := by
  have h : (U.blk2 1 (-(Matrix.of (aC x))ᴴ) 0 1)ᴴ = U.blk2 1 0 (-(Matrix.of (aC x))) 1 := by
    simp [U.blk2, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]
  rw [Dx2.Split.w_conj_apply, ← Matrix.conjTranspose_nonsing_inv, qL_inv, h]

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

section M1

open Dx2.Split

theorem radical_unipotent_rank_one_apply (y : U.RC k 1 ρ) (p q : U.Ix k 1 ρ) :
    U.Rn k 1 ρ y (U.eB k 1 ρ p) (U.eB k 1 ρ q) =
      Matrix.fromBlocks (Matrix.fromBlocks 1 (-(G.wMat 1 * (Matrix.of y.1)ᴴ * Hpk k ρ)) 0 1)
        (Matrix.fromRows (G.wMat 1 * ((-(1 / 2 : ℂ)) • ((Matrix.of y.1)ᴴ * Hpk k ρ * Matrix.of y.1) + U.skewOf y.2))
          (Matrix.of y.1)) (Matrix.fromCols 0 0) 1 p q := by
  rw [Ux3.rn_eq, Ux3.block3_apply]

theorem yH (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) :
    (G.wMat 1 * (Matrix.of y.1)ᴴ * Hpk k ρ) 0 v = Matrix.vecMul (star (cy y)) (Hpk k ρ) v := by
  rw [weyl_lift_eq_pair, Matrix.one_mul]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, cy, Matrix.conjTranspose_apply]

theorem yHy (y : U.RC k 1 ρ) :
    (G.wMat 1 * ((-(1 / 2 : ℂ)) • ((Matrix.of y.1)ᴴ * Hpk k ρ * Matrix.of y.1) + U.skewOf y.2)) 0 0 =
      -(1 / 2 : ℂ) * nn y + Complex.I * (dy y : ℂ) := by
  rw [weyl_lift_eq_pair, Matrix.one_mul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Ux2.skewOf_diag]
  congr 2

theorem rc_E (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (b : Fin j) :
    (U.Rn k 1 ρ y * Matrix.of x.1) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) b =
      ct x b - uu x y b + (-(1 / 2 : ℂ) * nn y + Complex.I * (dy y : ℂ)) * cb x b := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis]
  simp only [radical_unipotent_rank_one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromRows_apply_inl,
    Matrix.neg_apply, yH, yHy]
  simp [ct, cb, cm, uu, Matrix.vecMul, dotProduct, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem rc_V (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) (b : Fin j) :
    (U.Rn k 1 ρ y * Matrix.of x.1) (U.eB k 1 ρ (Sum.inl (Sum.inr v))) b = cm x v b + cy y v * cb x b := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis]
  simp only [radical_unipotent_rank_one_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.fromRows_apply_inr, Matrix.fromBlocks_apply₁₁]
  simp [cm, cb, cy, Matrix.one_apply]

theorem rc_E' (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (b : Fin j) :
    (U.Rn k 1 ρ y * Matrix.of x.1) (U.eB k 1 ρ (Sum.inr 0)) b = cb x b := by
  rw [Matrix.mul_apply, sum_over_rank_one_basis]
  simp [radical_unipotent_rank_one_apply, cb]

theorem radical_unipotent_first_basis_eq_one (y : U.RC k 1 ρ) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = 1 := by
  simp [radical_unipotent_rank_one_apply]

theorem radical_unipotent_first_middle (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inl (Sum.inr v))) =
      -Matrix.vecMul (star (cy y)) (Hpk k ρ) v := by
  rw [radical_unipotent_rank_one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, yH]

theorem radical_unipotent_first_last (y : U.RC k 1 ρ) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inr 0)) =
      -(1 / 2 : ℂ) * nn y + Complex.I * (dy y : ℂ) := by
  rw [radical_unipotent_rank_one_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromRows_apply_inl, yHy]

theorem radical_unipotent_middle_last (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inr v))) (U.eB k 1 ρ (Sum.inr 0)) = cy y v := by
  rw [radical_unipotent_rank_one_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromRows_apply_inr]; rfl

theorem reversed_adjoint_block_apply {n m : ℕ} (c : Matrix (Fin m) (Fin n) ℂ) (H : Matrix (Fin m) (Fin m) ℂ) (a : Fin n) (p : Fin m) :
    (-(G.wMat n * cᴴ * H)) a p = -(cᴴ * H) a.rev p := by
  rw [Matrix.neg_apply, Matrix.mul_assoc, Ux3.wMat_mul_apply]

theorem W_apply {n : ℕ} {m : Type*} (M : Matrix (Fin n) m ℂ) (a : Fin n) (p : m) :
    (G.wMat n * M) a p = M a.rev p := Ux3.wMat_mul_apply M a p

theorem star_first_coordinate_eq (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (a : Fin j) :
    star (r0 x y a) = star (ct x a) - (1 / 2 : ℂ) * uu' x y a - Complex.I * (dy y : ℂ) * star (cb x a) := by
  have h := star_uu' x y a
  simp only [r0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul',
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal, ← Matrix.vecMul_vecMul] at h ⊢
  rw [show Matrix.vecMul (Matrix.vecMul (star (cy y)) (Hpk k ρ)) (cm x) a = uu x y a from rfl, ← h,
    Complex.conj_conj]
  have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [h2]; ring

theorem first_coordinate_apply (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (b : Fin j) :
    r0 x y b = ct x b - (1 / 2 : ℂ) * uu x y b + Complex.I * (dy y : ℂ) * cb x b := by
  simp only [r0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Matrix.vecMul_vecMul]; rfl

end M1

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

section M1b

open Dx2.Split

theorem hs' (k j ρ : ℕ) : j + (1 + ρ) = (j + 1) + ρ := by omega

local macro "blks" : tactic => `(tactic| simp only [Ux3.block3_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
  Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
  Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr])

theorem M1 (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) :
    D.castM (hs' k j ρ) (U.embG k j (1 + ρ) (U.Rn k 1 ρ y) * U.Rn k j (1 + ρ) x) =
      U.muP k (j + 1) ρ (qL x) * U.Rn k (j + 1) ρ (XC x y) := by
  rw [lhs_form, rhs_form, skewOf_XC]
  apply Ux2.mat_ext_eB (k := k) (j := j + 1) (ρ := ρ)
  intro p q
  rw [castM_apply]
  rcases p with ((a | v) | b) <;> rcases q with ((a' | v') | b')
  ·
    cases a using Fin.lastCases with
    | last =>
      cases a' using Fin.lastCases with
      | last => simp only [qE]; blks; rw [radical_unipotent_first_basis_eq_one, qL, block_two_apply_last_last]; rfl
      | cast a' => simp only [qE, qX]; blks; simp [qL, block_two_apply_last_castSucc]
    | cast a =>
      cases a' using Fin.lastCases with
      | last =>
        simp only [qX, qE]; blks
        rw [reversed_adjoint_block_apply, cH_E, qL, block_two_apply_castSucc_last]
        simp [aC, Matrix.conjTranspose_apply]
      | cast a' => simp only [qX]; blks; simp [qL, block_two_apply_castSucc_castSucc]
  ·
    cases a using Fin.lastCases with
    | last =>
      simp only [qE, qV]; blks
      rw [radical_unipotent_first_middle, qmul_last, reversed_adjoint_block_apply, rev_last', cXH_zero]
    | cast a =>
      simp only [qX, qV]; blks
      rw [reversed_adjoint_block_apply, cH_V, qmul_cs, reversed_adjoint_block_apply, reversed_adjoint_block_apply, rev_castSucc', rev_last', cXH_succ, cXH_zero]
      simp [aC] <;> ring
  ·
    cases a using Fin.lastCases with
    | last =>
      cases b' using Fin.cases with
      | zero =>
        simp only [qE, qE']; blks
        rw [radical_unipotent_first_last, qmul_last, W_apply, rev_last', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cXHcX_00]
        simp [SX]
      | succ b' =>
        simp only [qE, qS]; blks
        rw [rc_E, qmul_last, W_apply, rev_last', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cXHcX_0s]
        simp only [SX, Fin.cases_zero, Fin.cases_succ, first_coordinate_apply]
        ring
    | cast a =>
      cases b' using Fin.cases with
      | zero =>
        simp only [qX, qE']; blks
        rw [reversed_adjoint_block_apply, cH_E', qmul_cs, W_apply, W_apply, rev_castSucc', rev_last']
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cXHcX_00, hermitian_form_column_succ_zero, SX, Fin.cases_zero,
          Fin.cases_succ, star_first_coordinate_eq, aC, star_neg]
        ring
      | succ b' =>
        simp only [qX, qS]; blks
        rw [W_apply, qmul_cs, W_apply, W_apply, rev_castSucc', rev_last']
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cHc, cXHcX_0s, cXHcX_ss, SX, Fin.cases_zero,
          Fin.cases_succ, first_coordinate_apply, dlt_apply, aC, star_neg, star_uu']
        ring
  ·
    cases a' using Fin.lastCases with
    | last => simp only [qV, qE]; blks; simp [radical_unipotent_rank_one_apply]
    | cast a' => simp only [qV, qX]; blks; simp
  ·
    simp only [qV]; blks; simp [radical_unipotent_rank_one_apply]
  ·
    cases b' using Fin.cases with
    | zero => simp only [qV, qE']; blks; rw [radical_unipotent_middle_last]; rfl
    | succ b' => simp only [qV, qS]; blks; rw [rc_V]; rfl
  ·
    cases b using Fin.cases with
    | zero =>
      cases a' using Fin.lastCases with
      | last => simp only [qE', qE]; blks; simp [radical_unipotent_rank_one_apply]
      | cast a' => simp only [qE', qX]; blks; simp
    | succ b =>
      cases a' using Fin.lastCases with
      | last => simp only [qS, qE]; blks; simp
      | cast a' => simp only [qS, qX]; blks; simp
  ·
    cases b using Fin.cases with
    | zero => simp only [qE', qV]; blks; simp [radical_unipotent_rank_one_apply]
    | succ b => simp only [qS, qV]; blks; simp
  ·
    cases b using Fin.cases with
    | zero =>
      cases b' using Fin.cases with
      | zero => simp only [qE']; blks; rw [conj_inverse_block_apply, rev_zero', block_two_apply_last_last]; simp [radical_unipotent_rank_one_apply]
      | succ b' =>
        simp only [qE', qS]; blks
        rw [rc_E', conj_inverse_block_apply, rev_zero', rev_succ', block_two_apply_last_castSucc]
        simp [aC]
    | succ b =>
      cases b' using Fin.cases with
      | zero => simp only [qS, qE']; blks; rw [conj_inverse_block_apply, rev_zero', rev_succ', block_two_apply_castSucc_last]; simp
      | succ b' =>
        simp only [qS]; blks
        rw [conj_inverse_block_apply, rev_succ', rev_succ', block_two_apply_castSucc_castSucc]
        simp [Matrix.one_apply, Fin.rev_inj]

end M1b

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

section M2

open Dx2.Split

local macro "blks" : tactic => `(tactic| simp only [Ux3.block3_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
  Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
  Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr])

def Z1 (c : ℂ) : G.Mat 1 := fun _ _ => c

theorem block_diagonal_inv {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) (hA : IsUnit A.det)
    (hD : IsUnit D'.det) : (U.blk2 A 0 0 D')⁻¹ = U.blk2 A⁻¹ 0 0 D'⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Ux3.symmetricScalarBlockMatrix_mul]
  simp [Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD, U.blk2, Matrix.fromBlocks_one]

theorem block_diagonal_conjTranspose {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) :
    (U.blk2 A 0 0 D')ᴴ = U.blk2 Aᴴ 0 0 D'ᴴ := by
  simp [U.blk2, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

theorem det_single_entry_matrix (c : ℂ) : (Matrix.of (Z1 c)).det = c := by
  simp [Z1, Matrix.det_unique]

theorem M2 (H : Matrix (Fin j) (Fin j) ℂ) (hH : IsUnit H.det) (c : ℂ) (hc : c ≠ 0) (γ : B.Mat k ρ) :
    D.castM (hs' k j ρ) (U.mMap k j (1 + ρ) H (U.mMap k 1 ρ (Matrix.of (Z1 c)) γ)) =
      U.mMap k (j + 1) ρ (U.blk2 H 0 0 (Matrix.of (Z1 c))) γ := by
  have hZ : IsUnit (Matrix.of (Z1 c)).det := by rw [det_single_entry_matrix]; exact Ne.isUnit hc
  have hH' : IsUnit Hᴴ.det := by rw [Matrix.det_conjTranspose]; exact hH.star
  have hZ' : IsUnit (Matrix.of (Z1 c))ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hZ.star
  rw [show U.mMap k (j + 1) ρ (U.blk2 H 0 0 (Matrix.of (Z1 c))) γ =
      U.blk3 0 0 ((U.blk2 H 0 0 (Matrix.of (Z1 c)))ᴴ⁻¹ * G.wMat (j + 1)) 0 γ 0
        (G.wMat (j + 1) * U.blk2 H 0 0 (Matrix.of (Z1 c))) 0 0 from rfl, block_diagonal_conjTranspose, block_diagonal_inv _ _ hH' hZ']
  apply Ux2.mat_ext_eB (k := k) (j := j + 1) (ρ := ρ)
  intro p q
  rw [castM_apply]
  simp only [U.mMap]
  rcases p with ((a | v) | b) <;> rcases q with ((a' | v') | b')
  · cases a using Fin.lastCases <;> cases a' using Fin.lastCases <;> simp only [qE, qX] <;> blks <;> simp
  · cases a using Fin.lastCases <;> simp only [qE, qX, qV] <;> blks <;> simp
  · cases a using Fin.lastCases <;> cases b' using Fin.cases
    all_goals (simp only [qE, qE', qX, qS]; blks; simp only [mul_w_apply, rev_zero', rev_succ', block_two_apply_last_last,
      block_two_apply_castSucc_last, block_two_apply_last_castSucc, block_two_apply_castSucc_castSucc, Fin.last_zero]; try simp)
  · cases a' using Fin.lastCases <;> simp only [qV, qE, qX] <;> blks <;> simp
  · simp only [qV]; blks
  · cases b' using Fin.cases <;> simp only [qV, qE', qS] <;> blks <;> simp
  · cases b using Fin.cases <;> cases a' using Fin.lastCases
    all_goals (simp only [qE, qE', qX, qS]; blks; simp only [W_apply, rev_zero', rev_succ', block_two_apply_last_last,
      block_two_apply_castSucc_last, block_two_apply_last_castSucc, block_two_apply_castSucc_castSucc, Fin.last_zero]; try simp [Z1])
  · cases b using Fin.cases <;> simp only [qE', qS, qV] <;> blks <;> simp
  · cases b using Fin.cases <;> cases b' using Fin.cases <;> simp only [qE', qS] <;> blks <;> simp

end M2

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

section GXs

open Dx2.Split

theorem muP_one' (n : ℕ) : U.muP k n ρ 1 = 1 := by
  rw [U.muP]; simp [Ux3.wMat_mul_self, Ux3.block3_one]

theorem leviElement_inv' {n : ℕ} (q : Matrix (Fin n) (Fin n) ℂ) (hq : IsUnit q.det) : (U.muP k n ρ q)⁻¹ = U.muP k n ρ q⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [leviElement_mul, Matrix.mul_nonsing_inv _ hq, muP_one']

theorem M3 {n : ℕ} (q q' Z : Matrix (Fin n) (Fin n) ℂ) (hq : IsUnit q.det) (hq' : IsUnit q'.det) (γ : B.Mat k ρ) :
    (U.muP k n ρ q)⁻¹ * U.mMap k n ρ Z γ * U.muP k n ρ q' = U.mMap k n ρ (qᴴ * Z * q') γ := by
  have hqh : IsUnit qᴴ.det := by rw [Matrix.det_conjTranspose]; exact hq.star
  rw [leviElement_inv' q hq, U.muP, U.muP, U.mMap, U.mMap, Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.wMat n) (G.wMat n), Ux3.wMat_mul_self, Matrix.one_mul]
  · rw [← Matrix.conjTranspose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.wMat n) (G.wMat n), Ux3.wMat_mul_self, Matrix.one_mul]

theorem block_two_zero_size_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 0) ℂ) (C : Matrix (Fin 0) (Fin p) ℂ)
    (D' : Matrix (Fin 0) (Fin 0) ℂ) : U.blk2 A B' C D' = A := by
  ext i l
  have hi : i = Fin.castAdd 0 i := rfl
  have hl : l = Fin.castAdd 0 l := rfl
  simp only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hi, hl, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem corner_matrix_zero_size_eq (a : Fin 0 → Fin j → ℂ) (b : Fin j → Fin 0 → ℂ) (H : Matrix (Fin j) (Fin j) ℂ)
    (Z : Matrix (Fin 0) (Fin 0) ℂ) : U.Zj a b H Z = H := by
  rw [U.Zj, block_two_zero_size_eq, block_two_zero_size_eq, block_two_zero_size_eq, Matrix.one_mul, Matrix.mul_one]

theorem mMap_sand {n ρ' : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (A M C : B.Mat k ρ') :
    U.mMap k n ρ' Z (A * M * C) = U.embG k n ρ' A * U.mMap k n ρ' Z M * U.embG k n ρ' C := by
  rw [U.mMap, U.mMap, U.embG, U.embG, Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp [Matrix.mul_assoc]

theorem embG_inv' {n ρ' : ℕ} (A : B.Mat k ρ') (hA : IsUnit A.det) : (U.embG k n ρ' A)⁻¹ = U.embG k n ρ' A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← embG_mul, Matrix.mul_nonsing_inv _ hA]
  rw [U.embG]; exact Ux3.block3_one

theorem castM_invS {a b : ℕ} (h : a = b) (A : B.Mat k a) : D.castM h A⁻¹ = (D.castM h A)⁻¹ := by
  simp [D.castM, Matrix.inv_reindex]

theorem rn_unit {n ρ' : ℕ} (x : U.RC k n ρ') : IsUnit (U.Rn k n ρ' x).det :=
  Matrix.isUnit_det_of_left_inverse (Ux3.rn_inv_mul x)

theorem qL_unit (x : U.RC k j (1 + ρ)) : IsUnit (qL x).det := by
  rw [qL, Ux3.block2_det_upper_triangular]; simp

theorem headH_unit (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ) (hd : ∀ i, d i ≠ 0) (η : U.XiH j 0 σ) :
    IsUnit (U.headH σ d η.2.1 η.2.2).det := by
  have h := Formalism.FourierDecayAlt.P.level_determinant_z j 0 σ d η (fun a => a.elim0)
  rw [U.ZjH, corner_matrix_zero_size_eq] at h
  rw [h]
  refine IsUnit.mul (Ne.isUnit (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd)) ?_
  simp [G.detM, Matrix.det_isEmpty]

def bC (x : U.RC k j (1 + ρ)) : Fin j → Fin 1 → ℂ := (Matrix.of (aC x))ᴴ

theorem qL_ct (x : U.RC k j (1 + ρ)) : (qL x)ᴴ = U.blk2 1 0 (Matrix.of (aC x)) 1 := by
  simp [qL, U.blk2, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

theorem GX (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ) (hd : ∀ i, d i ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (x x' : U.RC k j (1 + ρ)) (η : U.XiH j 0 σ) (y y' : U.RC k 1 ρ) (γ : B.Mat k ρ) :
    D.castM (hs' k j ρ) (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d ((x, x'), η) (fun a => a.elim0)
        ((U.Rn k 1 ρ y)⁻¹ * U.mMap k 1 ρ (Matrix.of (Z1 c)) γ * U.Rn k 1 ρ y')) =
      U.gaXi (p := j) (s := 1) k ρ σ d ((XC x y, XC x' y'), ((aC x, bC x'), η.2)) (Z1 c) γ := by
  have hH := headH_unit σ d hd η
  simp only [U.gaXi, U.ZjH]
  rw [corner_matrix_zero_size_eq, mMap_sand, ← embG_inv' _ (rn_unit y)]
  have e : (U.Rn k j (1 + ρ) x)⁻¹ * ((U.embG k j (1 + ρ) (U.Rn k 1 ρ y))⁻¹ *
        U.mMap k j (1 + ρ) (U.headH σ d η.2.1 η.2.2) (U.mMap k 1 ρ (Matrix.of (Z1 c)) γ) *
        U.embG k j (1 + ρ) (U.Rn k 1 ρ y')) * U.Rn k j (1 + ρ) x' =
      (U.embG k j (1 + ρ) (U.Rn k 1 ρ y) * U.Rn k j (1 + ρ) x)⁻¹ *
        U.mMap k j (1 + ρ) (U.headH σ d η.2.1 η.2.2) (U.mMap k 1 ρ (Matrix.of (Z1 c)) γ) *
        (U.embG k j (1 + ρ) (U.Rn k 1 ρ y') * U.Rn k j (1 + ρ) x') := by
    rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  show D.castM (hs' k j ρ) ((U.Rn k j (1 + ρ) x)⁻¹ * ((U.embG k j (1 + ρ) (U.Rn k 1 ρ y))⁻¹ *
        U.mMap k j (1 + ρ) (U.headH σ d η.2.1 η.2.2) (U.mMap k 1 ρ (Matrix.of (Z1 c)) γ) *
        U.embG k j (1 + ρ) (U.Rn k 1 ρ y')) * U.Rn k j (1 + ρ) x') = _
  rw [e, castM_mul, castM_mul, castM_invS, M1, M1, M2 _ hH c hc, Matrix.mul_inv_rev]
  have e2 : (U.Rn k (j + 1) ρ (XC x y))⁻¹ * (U.muP k (j + 1) ρ (qL x))⁻¹ *
        U.mMap k (j + 1) ρ (U.blk2 (U.headH σ d η.2.1 η.2.2) 0 0 (Matrix.of (Z1 c))) γ *
        (U.muP k (j + 1) ρ (qL x') * U.Rn k (j + 1) ρ (XC x' y')) =
      (U.Rn k (j + 1) ρ (XC x y))⁻¹ * ((U.muP k (j + 1) ρ (qL x))⁻¹ *
        U.mMap k (j + 1) ρ (U.blk2 (U.headH σ d η.2.1 η.2.2) 0 0 (Matrix.of (Z1 c))) γ *
        U.muP k (j + 1) ρ (qL x')) * U.Rn k (j + 1) ρ (XC x' y') := by
    simp only [Matrix.mul_assoc]
  rw [e2, M3 _ _ _ (qL_unit x) (qL_unit x'), qL_ct]
  rfl

end GXs

end Formalism.FourierDecayAlt.P.PBH
