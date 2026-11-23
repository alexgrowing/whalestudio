import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers

open Matrix Polynomial

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Generic

variable {K : Type*} [Field K]

theorem adjugate_last (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    M.adjugate (Fin.last r) (Fin.last r) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp only [Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem det_sub_single (r : ℕ) (W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (W - single (Fin.last r) (Fin.last r) c).det =
      W.det - c * W.adjugate (Fin.last r) (Fin.last r) := by
  have hrow : W - single (Fin.last r) (Fin.last r) c =
      W.updateRow (Fin.last r) (W (Fin.last r) + (-c) • Pi.single (Fin.last r) 1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.updateRow_apply, Matrix.single_apply, Pi.add_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp_all [sub_eq_add_neg]
  rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    ← Matrix.adjugate_apply]
  ring

theorem det_blocks_of_ne (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) (hZ : Z.det ≠ 0) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det = Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  haveI := Z.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hZ)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.single_mul_mul_single,
    det_sub_single, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  field_simp

theorem single_map {L M : Type*} [Ring L] [Ring M] (f : L →+* M) (r : ℕ) (c : L) :
    (single (Fin.last r) (Fin.last r) c).map f = single (Fin.last r) (Fin.last r) (f c) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

private theorem blocks_map_lemma {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (a b : R) :
    f ((fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det -
      (Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r))) =
    (fromBlocks (Z.map f) (single (Fin.last r) (Fin.last r) (f a))
        (single (Fin.last r) (Fin.last r) (f b)) (W.map f)).det -
      ((Z.map f).det * (W.map f).det - f a * f b * (Z.map f).adjugate (Fin.last r) (Fin.last r) *
        (W.map f).adjugate (Fin.last r) (Fin.last r)) := by
  have hdet : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R, f M.det = (M.map f).det := fun M =>
    RingHom.map_det f M
  have hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R,
      f (M.adjugate (Fin.last r) (Fin.last r)) = (M.map f).adjugate (Fin.last r) (Fin.last r) := by
    intro M
    rw [show M.map f = f.mapMatrix M from rfl, ← RingHom.map_adjugate]
    rfl
  simp only [map_sub, map_mul, hdet, hadj]
  rw [RingHom.map_det f, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, single_map, single_map]

theorem det_blocks (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det =
      Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] (FractionRing K[X])
  have hdet : ((charmatrix (-Z)).map φ).det ≠ 0 := by
    have h1 : φ (charmatrix (-Z)).det ≠ 0 := fun h =>
      (Matrix.charpoly_monic (-Z)).ne_zero (hφ (h.trans (map_zero φ).symm))
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h1
  have key := det_blocks_of_ne r ((charmatrix (-Z)).map φ) ((W.map Polynomial.C).map φ)
    (φ (Polynomial.C a)) (φ (Polynomial.C b)) hdet
  have hX : (fromBlocks (charmatrix (-Z)) (single (Fin.last r) (Fin.last r) (Polynomial.C a))
      (single (Fin.last r) (Fin.last r) (Polynomial.C b)) (W.map Polynomial.C)).det -
      ((charmatrix (-Z)).det * (W.map Polynomial.C).det - Polynomial.C a * Polynomial.C b *
        (charmatrix (-Z)).adjugate (Fin.last r) (Fin.last r) *
        (W.map Polynomial.C).adjugate (Fin.last r) (Fin.last r)) = 0 := by
    apply hφ
    rw [blocks_map_lemma, map_zero, key, sub_self]
  have h0 := congrArg (Polynomial.evalRingHom (0 : K)) hX
  rw [blocks_map_lemma, map_zero] at h0
  have hZ0 : (charmatrix (-Z)).map (Polynomial.evalRingHom (0 : K)) = Z := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.charmatrix_apply_eq]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h]
  have hW0 : (W.map Polynomial.C).map (Polynomial.evalRingHom (0 : K)) = W := by
    ext i j; simp
  rw [hZ0, hW0] at h0
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h0
  exact sub_eq_zero.mp h0

end Generic

theorem det_swap {K : Type*} [Field K] (n : ℕ) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
      (0 : Matrix (Fin n) (Fin n) K)).det = (-1) ^ n := by
  have hN : (fromBlocks (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    simp [Matrix.det_fromBlocks_zero₁₂]
  have hMN : fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) * fromBlocks (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) := by
    simp [Matrix.fromBlocks_multiply]
  have h := congrArg Matrix.det hMN
  rw [Matrix.det_mul, hN, mul_one, Matrix.det_fromBlocks_one₁₁] at h
  rw [h]
  simp [Matrix.det_neg]

open Formalism.L2.SG.CntLocal Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  rfl

theorem leadMinorE_r (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = Z.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS) := by
  rw [adjugate_last]
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ _)]
  rfl

theorem gram_determinant_formula_alt : DetGa := by
  intro D T T' _ _ Z
  have hA : ∀ c : D.host.E, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then c else 0) =
      single (Fin.last D.R.rS) (Fin.last D.R.rS) c := by
    intro c
    ext a b
    by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS <;>
      simp_all [Matrix.single_apply, eq_comm]
  have hprod : Ga T T' Z * fromBlocks (0 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) 1 1 0 =
      fromBlocks Z (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T))
        (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T')) Zᴴ := by
    unfold Ga
    rw [hA, hA, Matrix.fromBlocks_multiply]
    simp
  have h := congrArg Matrix.det hprod
  rw [Matrix.det_mul, det_swap, det_blocks, Matrix.det_conjTranspose, ← Matrix.adjugate_conjTranspose,
    Matrix.conjTranspose_apply] at h
  unfold GZ
  rw [leadMinorE_full, leadMinorE_r]
  have hsq : ((-1 : D.host.E) ^ (D.R.rS + 1)) * (-1) ^ (D.R.rS + 1) = 1 := by
    rw [← mul_pow]; simp
  calc (Ga T T' Z).det = (Ga T T' Z).det * ((-1) ^ (D.R.rS + 1) * (-1) ^ (D.R.rS + 1)) := by
        rw [hsq, mul_one]
    _ = (-1) ^ (D.R.rS + 1) * ((Ga T T' Z).det * (-1) ^ (D.R.rS + 1)) := by ring
    _ = _ := by rw [h]; ring

end PI.UnitaryGroupMassFormula.CntFormula.R6
